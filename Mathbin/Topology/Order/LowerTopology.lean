/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Topology.Homeomorph
import Topology.Order.Lattice
import Order.Hom.CompleteLattice

#align_import topology.order.lower_topology from "leanprover-community/mathlib"@"34ee86e6a59d911a8e4f89b68793ee7577ae79c7"

/-!
# Lower topology

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

#print Topology.WithLower /-
/-- Type synonym for a preorder equipped with the lower topology
-/
def Topology.WithLower :=
  α
#align with_lower_topology Topology.WithLower
-/

variable {α β}

namespace Topology.WithLower

#print Topology.WithLower.toLower /-
/-- `to_lower` is the identity function to the `with_lower_topology` of a type.  -/
@[match_pattern]
def Topology.WithLower.toLower : α ≃ Topology.WithLower α :=
  Equiv.refl _
#align with_lower_topology.to_lower Topology.WithLower.toLower
-/

#print Topology.WithLower.ofLower /-
/-- `of_lower` is the identity function from the `with_lower_topology` of a type.  -/
@[match_pattern]
def Topology.WithLower.ofLower : Topology.WithLower α ≃ α :=
  Equiv.refl _
#align with_lower_topology.of_lower Topology.WithLower.ofLower
-/

#print Topology.WithLower.to_WithLower_symm_eq /-
@[simp]
theorem Topology.WithLower.to_WithLower_symm_eq :
    (@Topology.WithLower.toLower α).symm = Topology.WithLower.ofLower :=
  rfl
#align with_lower_topology.to_with_lower_topology_symm_eq Topology.WithLower.to_WithLower_symm_eq
-/

#print Topology.WithLower.of_WithLower_symm_eq /-
@[simp]
theorem Topology.WithLower.of_WithLower_symm_eq :
    (@Topology.WithLower.ofLower α).symm = Topology.WithLower.toLower :=
  rfl
#align with_lower_topology.of_with_lower_topology_symm_eq Topology.WithLower.of_WithLower_symm_eq
-/

#print Topology.WithLower.toLower_ofLower /-
@[simp]
theorem Topology.WithLower.toLower_ofLower (a : Topology.WithLower α) :
    Topology.WithLower.toLower (Topology.WithLower.ofLower a) = a :=
  rfl
#align with_lower_topology.to_lower_of_lower Topology.WithLower.toLower_ofLower
-/

#print Topology.WithLower.ofLower_toLower /-
@[simp]
theorem Topology.WithLower.ofLower_toLower (a : α) :
    Topology.WithLower.ofLower (Topology.WithLower.toLower a) = a :=
  rfl
#align with_lower_topology.of_lower_to_lower Topology.WithLower.ofLower_toLower
-/

#print Topology.WithLower.toLower_inj /-
@[simp]
theorem Topology.WithLower.toLower_inj {a b : α} :
    Topology.WithLower.toLower a = Topology.WithLower.toLower b ↔ a = b :=
  Iff.rfl
#align with_lower_topology.to_lower_inj Topology.WithLower.toLower_inj
-/

#print Topology.WithLower.ofLower_inj /-
@[simp]
theorem Topology.WithLower.ofLower_inj {a b : Topology.WithLower α} :
    Topology.WithLower.ofLower a = Topology.WithLower.ofLower b ↔ a = b :=
  Iff.rfl
#align with_lower_topology.of_lower_inj Topology.WithLower.ofLower_inj
-/

#print Topology.WithLower.rec /-
/-- A recursor for `with_lower_topology`. Use as `induction x using with_lower_topology.rec`. -/
protected def Topology.WithLower.rec {β : Topology.WithLower α → Sort _}
    (h : ∀ a, β (Topology.WithLower.toLower a)) : ∀ a, β a := fun a =>
  h (Topology.WithLower.ofLower a)
#align with_lower_topology.rec Topology.WithLower.rec
-/

instance [Nonempty α] : Nonempty (Topology.WithLower α) :=
  ‹Nonempty α›

instance [Inhabited α] : Inhabited (Topology.WithLower α) :=
  ‹Inhabited α›

variable [Preorder α]

instance : Preorder (Topology.WithLower α) :=
  ‹Preorder α›

instance : TopologicalSpace (Topology.WithLower α) :=
  generateFrom {s | ∃ a, Ici aᶜ = s}

#print Topology.WithLower.isOpen_preimage_ofLower /-
theorem Topology.WithLower.isOpen_preimage_ofLower (S : Set α) :
    IsOpen (Topology.WithLower.ofLower ⁻¹' S) ↔
      (generateFrom {s : Set α | ∃ a : α, Ici aᶜ = s}).IsOpen S :=
  Iff.rfl
#align with_lower_topology.is_open_preimage_of_lower Topology.WithLower.isOpen_preimage_ofLower
-/

#print Topology.WithLower.isOpen_def /-
theorem Topology.WithLower.isOpen_def (T : Set (Topology.WithLower α)) :
    IsOpen T ↔
      (generateFrom {s : Set α | ∃ a : α, Ici aᶜ = s}).IsOpen (Topology.WithLower.toLower ⁻¹' T) :=
  Iff.rfl
#align with_lower_topology.is_open_def Topology.WithLower.isOpen_def
-/

end Topology.WithLower

#print Topology.IsLower /-
/- ./././Mathport/Syntax/Translate/Command.lean:400:30: infer kinds are unsupported in Lean 4: #[`topology_eq_isLower] [] -/
/--
The lower topology is the topology generated by the complements of the closed intervals to infinity.
-/
class Topology.IsLower (α : Type _) [t : TopologicalSpace α] [Preorder α] : Prop where
  topology_eq_isLower : t = generateFrom {s | ∃ a, Ici aᶜ = s}
#align lower_topology Topology.IsLower
-/

instance [Preorder α] : Topology.IsLower (Topology.WithLower α) :=
  ⟨rfl⟩

namespace Topology.IsLower

#print Topology.IsLower.lowerBasis /-
/-- The complements of the upper closures of finite sets are a collection of lower sets
which form a basis for the lower topology. -/
def Topology.IsLower.lowerBasis (α : Type _) [Preorder α] :=
  {s : Set α | ∃ t : Set α, t.Finite ∧ (upperClosure t : Set α)ᶜ = s}
#align lower_topology.lower_basis Topology.IsLower.lowerBasis
-/

section Preorder

variable [Preorder α] [TopologicalSpace α] [Topology.IsLower α] {s : Set α}

#print Topology.IsLower.WithLowerHomeomorph /-
/-- If `α` is equipped with the lower topology, then it is homeomorphic to `with_lower_topology α`.
-/
def Topology.IsLower.WithLowerHomeomorph : Topology.WithLower α ≃ₜ α :=
  {
    Topology.WithLower.ofLower with
    continuous_toFun := by convert continuous_id; apply topology_eq_lower_topology
    continuous_invFun := by convert ← continuous_id; apply topology_eq_lower_topology }
#align lower_topology.with_lower_topology_homeomorph Topology.IsLower.WithLowerHomeomorph
-/

#print Topology.IsLower.isOpen_iff_generate_Ici_compl /-
theorem Topology.IsLower.isOpen_iff_generate_Ici_compl :
    IsOpen s ↔ GenerateOpen {t | ∃ a, Ici aᶜ = t} s := by rw [topology_eq_lower_topology α] <;> rfl
#align lower_topology.is_open_iff_generate_Ici_compl Topology.IsLower.isOpen_iff_generate_Ici_compl
-/

/- warning: lower_topology.is_closed_Ici clashes with is_closed_Ici -> isClosed_Ici
Case conversion may be inaccurate. Consider using '#align lower_topology.is_closed_Ici isClosed_Iciₓ'. -/
#print isClosed_Ici /-
/-- Left-closed right-infinite intervals [a, ∞) are closed in the lower topology. -/
theorem isClosed_Ici (a : α) : IsClosed (Ici a) :=
  isOpen_compl_iff.1 <|
    Topology.IsLower.isOpen_iff_generate_Ici_compl.2 <| GenerateOpen.basic _ ⟨a, rfl⟩
#align lower_topology.is_closed_Ici isClosed_Ici
-/

#print Topology.IsLower.isClosed_upperClosure /-
/-- The upper closure of a finite set is closed in the lower topology. -/
theorem Topology.IsLower.isClosed_upperClosure (h : s.Finite) : IsClosed (upperClosure s : Set α) :=
  by
  simp only [← UpperSet.iInf_Ici, UpperSet.coe_iInf]
  exact Set.Finite.isClosed_biUnion h fun a h₁ => isClosed_Ici a
#align lower_topology.is_closed_upper_closure Topology.IsLower.isClosed_upperClosure
-/

#print Topology.IsLower.isLowerSet_of_isOpen /-
/-- Every set open in the lower topology is a lower set. -/
theorem Topology.IsLower.isLowerSet_of_isOpen (h : IsOpen s) : IsLowerSet s :=
  by
  rw [is_open_iff_generate_Ici_compl] at h 
  induction h
  case basic u h => obtain ⟨a, rfl⟩ := h; exact (isUpperSet_Ici a).compl
  case univ => exact isLowerSet_univ
  case inter u v hu1 hv1 hu2 hv2 => exact hu2.inter hv2
  case sUnion _ _ ih => exact isLowerSet_sUnion ih
#align lower_topology.is_lower_set_of_is_open Topology.IsLower.isLowerSet_of_isOpen
-/

#print Topology.IsLower.isUpperSet_of_isClosed /-
theorem Topology.IsLower.isUpperSet_of_isClosed (h : IsClosed s) : IsUpperSet s :=
  isLowerSet_compl.1 <| Topology.IsLower.isLowerSet_of_isOpen h.isOpen_compl
#align lower_topology.is_upper_set_of_is_closed Topology.IsLower.isUpperSet_of_isClosed
-/

#print Topology.IsLower.closure_singleton /-
/--
The closure of a singleton `{a}` in the lower topology is the left-closed right-infinite interval
[a, ∞).
-/
@[simp]
theorem Topology.IsLower.closure_singleton (a : α) : closure {a} = Ici a :=
  subset_antisymm ((closure_minimal fun b h => h.ge) <| isClosed_Ici a) <|
    (Topology.IsLower.isUpperSet_of_isClosed isClosed_closure).Ici_subset <| subset_closure rfl
#align lower_topology.closure_singleton Topology.IsLower.closure_singleton
-/

#print Topology.IsLower.isTopologicalBasis /-
protected theorem Topology.IsLower.isTopologicalBasis :
    IsTopologicalBasis (Topology.IsLower.lowerBasis α) :=
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
#align lower_topology.is_topological_basis Topology.IsLower.isTopologicalBasis
-/

end Preorder

section PartialOrder

variable [PartialOrder α] [TopologicalSpace α] [Topology.IsLower α]

-- see Note [lower instance priority]
/-- The lower topology on a partial order is T₀.
-/
instance (priority := 90) : T0Space α :=
  (t0Space_iff_inseparable α).2 fun x y h =>
    Ici_injective <| by simpa only [inseparable_iff_closure_eq, closure_singleton] using h

end PartialOrder

end Topology.IsLower

instance [Preorder α] [TopologicalSpace α] [Topology.IsLower α] [OrderBot α] [Preorder β]
    [TopologicalSpace β] [Topology.IsLower β] [OrderBot β] : Topology.IsLower (α × β)
    where topology_eq_isLower :=
    by
    refine' le_antisymm (le_generateFrom _) _
    · rintro _ ⟨x, rfl⟩
      exact ((isClosed_Ici _).Prod <| isClosed_Ici _).isOpen_compl
    rw [(lower_topology.is_topological_basis.prod
          Topology.IsLower.isTopologicalBasis).eq_generateFrom,
      le_generate_from_iff_subset_is_open, image2_subset_iff]
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    dsimp
    simp_rw [coe_upperClosure, compl_Union, prod_eq, preimage_Inter, preimage_compl]
    -- Note: `refine` doesn't work here because it tries using `prod.topological_space`.
    apply
      (Set.Finite.isOpen_biInter hs fun a _ => _).inter (Set.Finite.isOpen_biInter ht fun b _ => _)
    · exact generate_open.basic _ ⟨(a, ⊥), by simp [Ici_prod_eq, prod_univ]⟩
    · exact generate_open.basic _ ⟨(⊥, b), by simp [Ici_prod_eq, univ_prod]⟩
    all_goals infer_instance

section CompleteLattice

variable [CompleteLattice α] [CompleteLattice β] [TopologicalSpace α] [Topology.IsLower α]
  [TopologicalSpace β] [Topology.IsLower β]

#print sInfHom.continuous /-
theorem sInfHom.continuous (f : sInfHom α β) : Continuous f :=
  by
  convert continuous_generateFrom _
  · exact Topology.IsLower.topology_eq_isLower β
  rintro _ ⟨b, rfl⟩
  rw [preimage_compl, isOpen_compl_iff]
  convert isClosed_Ici (Inf <| f ⁻¹' Ici b)
  refine' subset_antisymm (fun a => sInf_le) fun a ha => le_trans _ <| OrderHomClass.mono f ha
  simp [map_Inf]
#align Inf_hom.continuous sInfHom.continuous
-/

#print Topology.IsLower.toContinuousInf /-
-- see Note [lower instance priority]
instance (priority := 90) Topology.IsLower.toContinuousInf : ContinuousInf α :=
  ⟨(infsInfHom : sInfHom (α × α) α).Continuous⟩
#align lower_topology.to_has_continuous_inf Topology.IsLower.toContinuousInf
-/

end CompleteLattice

