/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot

! This file was ported from Lean 3 source module topology.constructions
! leanprover-community/mathlib commit 28aa996fc6fb4317f0083c4e6daf79878d81be33
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Maps
import Mathbin.Topology.LocallyFinite
import Mathbin.Order.Filter.Pi

/-!
# Constructions of new topological spaces from old ones

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

open Classical Topology Filter

universe u v

variable {α : Type u} {β : Type v} {γ δ ε ζ : Type _}

section Constructions

instance {p : α → Prop} [t : TopologicalSpace α] : TopologicalSpace (Subtype p) :=
  induced coe t

instance {r : α → α → Prop} [t : TopologicalSpace α] : TopologicalSpace (Quot r) :=
  coinduced (Quot.mk r) t

instance {s : Setoid α} [t : TopologicalSpace α] : TopologicalSpace (Quotient s) :=
  coinduced Quotient.mk' t

instance [t₁ : TopologicalSpace α] [t₂ : TopologicalSpace β] : TopologicalSpace (α × β) :=
  induced Prod.fst t₁ ⊓ induced Prod.snd t₂

instance [t₁ : TopologicalSpace α] [t₂ : TopologicalSpace β] : TopologicalSpace (Sum α β) :=
  coinduced Sum.inl t₁ ⊔ coinduced Sum.inr t₂

instance {β : α → Type v} [t₂ : ∀ a, TopologicalSpace (β a)] : TopologicalSpace (Sigma β) :=
  ⨆ a, coinduced (Sigma.mk a) (t₂ a)

#print Pi.topologicalSpace /-
instance Pi.topologicalSpace {β : α → Type v} [t₂ : ∀ a, TopologicalSpace (β a)] :
    TopologicalSpace (∀ a, β a) :=
  ⨅ a, induced (fun f => f a) (t₂ a)
#align Pi.topological_space Pi.topologicalSpace
-/

#print ULift.topologicalSpace /-
instance ULift.topologicalSpace [t : TopologicalSpace α] : TopologicalSpace (ULift.{v, u} α) :=
  t.induced ULift.down
#align ulift.topological_space ULift.topologicalSpace
-/

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

#print continuous_ofMul /-
theorem continuous_ofMul : Continuous (ofMul : α → Additive α) :=
  continuous_id
#align continuous_of_mul continuous_ofMul
-/

#print continuous_toMul /-
theorem continuous_toMul : Continuous (toMul : Additive α → α) :=
  continuous_id
#align continuous_to_mul continuous_toMul
-/

#print continuous_ofAdd /-
theorem continuous_ofAdd : Continuous (ofAdd : α → Multiplicative α) :=
  continuous_id
#align continuous_of_add continuous_ofAdd
-/

#print continuous_toAdd /-
theorem continuous_toAdd : Continuous (toAdd : Multiplicative α → α) :=
  continuous_id
#align continuous_to_add continuous_toAdd
-/

#print isOpenMap_ofMul /-
theorem isOpenMap_ofMul : IsOpenMap (ofMul : α → Additive α) :=
  IsOpenMap.id
#align is_open_map_of_mul isOpenMap_ofMul
-/

#print isOpenMap_toMul /-
theorem isOpenMap_toMul : IsOpenMap (toMul : Additive α → α) :=
  IsOpenMap.id
#align is_open_map_to_mul isOpenMap_toMul
-/

#print isOpenMap_ofAdd /-
theorem isOpenMap_ofAdd : IsOpenMap (ofAdd : α → Multiplicative α) :=
  IsOpenMap.id
#align is_open_map_of_add isOpenMap_ofAdd
-/

#print isOpenMap_toAdd /-
theorem isOpenMap_toAdd : IsOpenMap (toAdd : Multiplicative α → α) :=
  IsOpenMap.id
#align is_open_map_to_add isOpenMap_toAdd
-/

#print isClosedMap_ofMul /-
theorem isClosedMap_ofMul : IsClosedMap (ofMul : α → Additive α) :=
  IsClosedMap.id
#align is_closed_map_of_mul isClosedMap_ofMul
-/

#print isClosedMap_toMul /-
theorem isClosedMap_toMul : IsClosedMap (toMul : Additive α → α) :=
  IsClosedMap.id
#align is_closed_map_to_mul isClosedMap_toMul
-/

#print isClosedMap_ofAdd /-
theorem isClosedMap_ofAdd : IsClosedMap (ofAdd : α → Multiplicative α) :=
  IsClosedMap.id
#align is_closed_map_of_add isClosedMap_ofAdd
-/

#print isClosedMap_toAdd /-
theorem isClosedMap_toAdd : IsClosedMap (toAdd : Multiplicative α → α) :=
  IsClosedMap.id
#align is_closed_map_to_add isClosedMap_toAdd
-/

#print nhds_ofMul /-
theorem nhds_ofMul (a : α) : 𝓝 (ofMul a) = map ofMul (𝓝 a) :=
  by
  unfold nhds
  rfl
#align nhds_of_mul nhds_ofMul
-/

#print nhds_ofAdd /-
theorem nhds_ofAdd (a : α) : 𝓝 (ofAdd a) = map ofAdd (𝓝 a) :=
  by
  unfold nhds
  rfl
#align nhds_of_add nhds_ofAdd
-/

#print nhds_toMul /-
theorem nhds_toMul (a : Additive α) : 𝓝 (toMul a) = map toMul (𝓝 a) :=
  by
  unfold nhds
  rfl
#align nhds_to_mul nhds_toMul
-/

#print nhds_toAdd /-
theorem nhds_toAdd (a : Multiplicative α) : 𝓝 (toAdd a) = map toAdd (𝓝 a) :=
  by
  unfold nhds
  rfl
#align nhds_to_add nhds_toAdd
-/

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

#print continuous_toDual /-
theorem continuous_toDual : Continuous (toDual : α → αᵒᵈ) :=
  continuous_id
#align continuous_to_dual continuous_toDual
-/

#print continuous_ofDual /-
theorem continuous_ofDual : Continuous (ofDual : αᵒᵈ → α) :=
  continuous_id
#align continuous_of_dual continuous_ofDual
-/

#print isOpenMap_toDual /-
theorem isOpenMap_toDual : IsOpenMap (toDual : α → αᵒᵈ) :=
  IsOpenMap.id
#align is_open_map_to_dual isOpenMap_toDual
-/

#print isOpenMap_ofDual /-
theorem isOpenMap_ofDual : IsOpenMap (ofDual : αᵒᵈ → α) :=
  IsOpenMap.id
#align is_open_map_of_dual isOpenMap_ofDual
-/

#print isClosedMap_toDual /-
theorem isClosedMap_toDual : IsClosedMap (toDual : α → αᵒᵈ) :=
  IsClosedMap.id
#align is_closed_map_to_dual isClosedMap_toDual
-/

#print isClosedMap_ofDual /-
theorem isClosedMap_ofDual : IsClosedMap (ofDual : αᵒᵈ → α) :=
  IsClosedMap.id
#align is_closed_map_of_dual isClosedMap_ofDual
-/

#print nhds_toDual /-
theorem nhds_toDual (a : α) : 𝓝 (toDual a) = map toDual (𝓝 a) :=
  by
  unfold nhds
  rfl
#align nhds_to_dual nhds_toDual
-/

#print nhds_ofDual /-
theorem nhds_ofDual (a : α) : 𝓝 (ofDual a) = map ofDual (𝓝 a) :=
  by
  unfold nhds
  rfl
#align nhds_of_dual nhds_ofDual
-/

end

#print Quotient.preimage_mem_nhds /-
theorem Quotient.preimage_mem_nhds [TopologicalSpace α] [s : Setoid α] {V : Set <| Quotient s}
    {a : α} (hs : V ∈ 𝓝 (Quotient.mk' a)) : Quotient.mk' ⁻¹' V ∈ 𝓝 a :=
  preimage_nhds_coinduced hs
#align quotient.preimage_mem_nhds Quotient.preimage_mem_nhds
-/

#print Dense.quotient /-
/-- The image of a dense set under `quotient.mk` is a dense set. -/
theorem Dense.quotient [Setoid α] [TopologicalSpace α] {s : Set α} (H : Dense s) :
    Dense (Quotient.mk' '' s) :=
  (surjective_quotient_mk α).DenseRange.dense_image continuous_coinduced_rng H
#align dense.quotient Dense.quotient
-/

#print DenseRange.quotient /-
/-- The composition of `quotient.mk` and a function with dense range has dense range. -/
theorem DenseRange.quotient [Setoid α] [TopologicalSpace α] {f : β → α} (hf : DenseRange f) :
    DenseRange (Quotient.mk' ∘ f) :=
  (surjective_quotient_mk α).DenseRange.comp hf continuous_coinduced_rng
#align dense_range.quotient DenseRange.quotient
-/

instance {p : α → Prop} [TopologicalSpace α] [DiscreteTopology α] : DiscreteTopology (Subtype p) :=
  ⟨bot_unique fun s hs =>
      ⟨coe '' s, isOpen_discrete _, Set.preimage_image_eq _ Subtype.coe_injective⟩⟩

/- warning: sum.discrete_topology -> Sum.discreteTopology is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [hα : DiscreteTopology.{u1} α _inst_1] [hβ : DiscreteTopology.{u2} β _inst_2], DiscreteTopology.{max u1 u2} (Sum.{u1, u2} α β) (Sum.topologicalSpace.{u1, u2} α β _inst_1 _inst_2)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [hα : DiscreteTopology.{u1} α _inst_1] [hβ : DiscreteTopology.{u2} β _inst_2], DiscreteTopology.{max u2 u1} (Sum.{u1, u2} α β) (instTopologicalSpaceSum.{u1, u2} α β _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align sum.discrete_topology Sum.discreteTopologyₓ'. -/
instance Sum.discreteTopology [TopologicalSpace α] [TopologicalSpace β] [hα : DiscreteTopology α]
    [hβ : DiscreteTopology β] : DiscreteTopology (Sum α β) :=
  ⟨by unfold Sum.topologicalSpace <;> simp [hα.eq_bot, hβ.eq_bot]⟩
#align sum.discrete_topology Sum.discreteTopology

/- warning: sigma.discrete_topology -> Sigma.discreteTopology is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} [_inst_1 : forall (a : α), TopologicalSpace.{u2} (β a)] [h : forall (a : α), DiscreteTopology.{u2} (β a) (_inst_1 a)], DiscreteTopology.{max u1 u2} (Sigma.{u1, u2} α β) (Sigma.topologicalSpace.{u1, u2} α β (fun (a : α) => _inst_1 a))
but is expected to have type
  forall {α : Type.{u1}} {β : α -> Type.{u2}} [_inst_1 : forall (a : α), TopologicalSpace.{u2} (β a)] [h : forall (a : α), DiscreteTopology.{u2} (β a) (_inst_1 a)], DiscreteTopology.{max u2 u1} (Sigma.{u1, u2} α β) (instTopologicalSpaceSigma.{u1, u2} α β (fun (a : α) => _inst_1 a))
Case conversion may be inaccurate. Consider using '#align sigma.discrete_topology Sigma.discreteTopologyₓ'. -/
instance Sigma.discreteTopology {β : α → Type v} [∀ a, TopologicalSpace (β a)]
    [h : ∀ a, DiscreteTopology (β a)] : DiscreteTopology (Sigma β) :=
  ⟨by
    unfold Sigma.topologicalSpace
    simp [fun a => (h a).eq_bot]⟩
#align sigma.discrete_topology Sigma.discreteTopology

section Topα

variable [TopologicalSpace α]

/- warning: mem_nhds_subtype -> mem_nhds_subtype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : Set.{u1} α) (a : Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) (t : Set.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))), Iff (Membership.Mem.{u1, u1} (Set.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))) (Filter.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))) (Filter.hasMem.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))) t (nhds.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) a)) (Exists.{succ u1} (Set.{u1} α) (fun (u : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) u (nhds.{u1} α _inst_1 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) a))) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) u (nhds.{u1} α _inst_1 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) a))) => HasSubset.Subset.{u1} (Set.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))) (Set.hasSubset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))) (Set.preimage.{u1, u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)))))) u) t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : Set.{u1} α) (a : Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)) (t : Set.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s))), Iff (Membership.mem.{u1, u1} (Set.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s))) (Filter.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s))) (instMembershipSetFilter.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s))) t (nhds.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)) (instTopologicalSpaceSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) _inst_1) a)) (Exists.{succ u1} (Set.{u1} α) (fun (u : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) u (nhds.{u1} α _inst_1 (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) a))) (HasSubset.Subset.{u1} (Set.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s))) (Set.instHasSubsetSet.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s))) (Set.preimage.{u1, u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)) α (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)) u) t)))
Case conversion may be inaccurate. Consider using '#align mem_nhds_subtype mem_nhds_subtypeₓ'. -/
/-
The 𝓝 filter and the subspace topology.
-/
theorem mem_nhds_subtype (s : Set α) (a : { x // x ∈ s }) (t : Set { x // x ∈ s }) :
    t ∈ 𝓝 a ↔ ∃ u ∈ 𝓝 (a : α), coe ⁻¹' u ⊆ t :=
  mem_nhds_induced coe a t
#align mem_nhds_subtype mem_nhds_subtype

#print nhds_subtype /-
theorem nhds_subtype (s : Set α) (a : { x // x ∈ s }) : 𝓝 a = comap coe (𝓝 (a : α)) :=
  nhds_induced coe a
#align nhds_subtype nhds_subtype
-/

/- warning: nhds_within_subtype_eq_bot_iff -> nhdsWithin_subtype_eq_bot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s}, Iff (Eq.{succ u1} (Filter.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) (nhdsWithin.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) x (Set.preimage.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)))))) t)) (Bot.bot.{u1} (Filter.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) (CompleteLattice.toHasBot.{u1} (Filter.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) (Filter.completeLattice.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s))))) (Eq.{succ u1} (Filter.{u1} α) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) (nhdsWithin.{u1} α _inst_1 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) x) t) (Filter.principal.{u1} α s)) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {x : Set.Elem.{u1} α s}, Iff (Eq.{succ u1} (Filter.{u1} (Set.Elem.{u1} α s)) (nhdsWithin.{u1} (Set.Elem.{u1} α s) (instTopologicalSpaceSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) _inst_1) x (Set.preimage.{u1, u1} (Set.Elem.{u1} α s) α (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)) t)) (Bot.bot.{u1} (Filter.{u1} (Set.Elem.{u1} α s)) (CompleteLattice.toBot.{u1} (Filter.{u1} (Set.Elem.{u1} α s)) (Filter.instCompleteLatticeFilter.{u1} (Set.Elem.{u1} α s))))) (Eq.{succ u1} (Filter.{u1} α) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) (nhdsWithin.{u1} α _inst_1 (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) x) t) (Filter.principal.{u1} α s)) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))))
Case conversion may be inaccurate. Consider using '#align nhds_within_subtype_eq_bot_iff nhdsWithin_subtype_eq_bot_iffₓ'. -/
theorem nhdsWithin_subtype_eq_bot_iff {s t : Set α} {x : s} :
    𝓝[(coe : s → α) ⁻¹' t] x = ⊥ ↔ 𝓝[t] (x : α) ⊓ 𝓟 s = ⊥ := by
  rw [inf_principal_eq_bot_iff_comap, nhdsWithin, nhdsWithin, comap_inf, comap_principal,
    nhds_induced]
#align nhds_within_subtype_eq_bot_iff nhdsWithin_subtype_eq_bot_iff

/- warning: nhds_ne_subtype_eq_bot_iff -> nhds_ne_subtype_eq_bot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {S : Set.{u1} α} {x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S}, Iff (Eq.{succ u1} (Filter.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S)) (nhdsWithin.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S) (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x S) _inst_1) x (HasCompl.compl.{u1} (Set.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S)) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S)) (Set.booleanAlgebra.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S))) (Singleton.singleton.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S) (Set.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S)) (Set.hasSingleton.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S)) x))) (Bot.bot.{u1} (Filter.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S)) (CompleteLattice.toHasBot.{u1} (Filter.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S)) (Filter.completeLattice.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S))))) (Eq.{succ u1} (Filter.{u1} α) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) (nhdsWithin.{u1} α _inst_1 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x S))))) x) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x S))))) x)))) (Filter.principal.{u1} α S)) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {S : Set.{u1} α} {x : Set.Elem.{u1} α S}, Iff (Eq.{succ u1} (Filter.{u1} (Set.Elem.{u1} α S)) (nhdsWithin.{u1} (Set.Elem.{u1} α S) (instTopologicalSpaceSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x S) _inst_1) x (HasCompl.compl.{u1} (Set.{u1} (Set.Elem.{u1} α S)) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} (Set.Elem.{u1} α S)) (Set.instBooleanAlgebraSet.{u1} (Set.Elem.{u1} α S))) (Singleton.singleton.{u1, u1} (Set.Elem.{u1} α S) (Set.{u1} (Set.Elem.{u1} α S)) (Set.instSingletonSet.{u1} (Set.Elem.{u1} α S)) x))) (Bot.bot.{u1} (Filter.{u1} (Set.Elem.{u1} α S)) (CompleteLattice.toBot.{u1} (Filter.{u1} (Set.Elem.{u1} α S)) (Filter.instCompleteLatticeFilter.{u1} (Set.Elem.{u1} α S))))) (Eq.{succ u1} (Filter.{u1} α) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) (nhdsWithin.{u1} α _inst_1 (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x S) x) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x S) x)))) (Filter.principal.{u1} α S)) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))))
Case conversion may be inaccurate. Consider using '#align nhds_ne_subtype_eq_bot_iff nhds_ne_subtype_eq_bot_iffₓ'. -/
theorem nhds_ne_subtype_eq_bot_iff {S : Set α} {x : S} :
    𝓝[{x}ᶜ] x = ⊥ ↔ 𝓝[{x}ᶜ] (x : α) ⊓ 𝓟 S = ⊥ := by
  rw [← nhdsWithin_subtype_eq_bot_iff, preimage_compl, ← image_singleton,
    subtype.coe_injective.preimage_image]
#align nhds_ne_subtype_eq_bot_iff nhds_ne_subtype_eq_bot_iff

/- warning: nhds_ne_subtype_ne_bot_iff -> nhds_ne_subtype_neBot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {S : Set.{u1} α} {x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S}, Iff (Filter.NeBot.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S) (nhdsWithin.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S) (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x S) _inst_1) x (HasCompl.compl.{u1} (Set.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S)) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S)) (Set.booleanAlgebra.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S))) (Singleton.singleton.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S) (Set.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S)) (Set.hasSingleton.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S)) x)))) (Filter.NeBot.{u1} α (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) (nhdsWithin.{u1} α _inst_1 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x S))))) x) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x S))))) x)))) (Filter.principal.{u1} α S)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {S : Set.{u1} α} {x : Set.Elem.{u1} α S}, Iff (Filter.NeBot.{u1} (Set.Elem.{u1} α S) (nhdsWithin.{u1} (Set.Elem.{u1} α S) (instTopologicalSpaceSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x S) _inst_1) x (HasCompl.compl.{u1} (Set.{u1} (Set.Elem.{u1} α S)) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} (Set.Elem.{u1} α S)) (Set.instBooleanAlgebraSet.{u1} (Set.Elem.{u1} α S))) (Singleton.singleton.{u1, u1} (Set.Elem.{u1} α S) (Set.{u1} (Set.Elem.{u1} α S)) (Set.instSingletonSet.{u1} (Set.Elem.{u1} α S)) x)))) (Filter.NeBot.{u1} α (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) (nhdsWithin.{u1} α _inst_1 (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x S) x) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x S) x)))) (Filter.principal.{u1} α S)))
Case conversion may be inaccurate. Consider using '#align nhds_ne_subtype_ne_bot_iff nhds_ne_subtype_neBot_iffₓ'. -/
theorem nhds_ne_subtype_neBot_iff {S : Set α} {x : S} :
    (𝓝[{x}ᶜ] x).ne_bot ↔ (𝓝[{x}ᶜ] (x : α) ⊓ 𝓟 S).ne_bot := by
  rw [ne_bot_iff, ne_bot_iff, not_iff_not, nhds_ne_subtype_eq_bot_iff]
#align nhds_ne_subtype_ne_bot_iff nhds_ne_subtype_neBot_iff

/- warning: discrete_topology_subtype_iff -> discreteTopology_subtype_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {S : Set.{u1} α}, Iff (DiscreteTopology.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) S) (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x S) _inst_1)) (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x S) -> (Eq.{succ u1} (Filter.{u1} α) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) (nhdsWithin.{u1} α _inst_1 x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x))) (Filter.principal.{u1} α S)) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {S : Set.{u1} α}, Iff (DiscreteTopology.{u1} (Set.Elem.{u1} α S) (instTopologicalSpaceSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x S) _inst_1)) (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x S) -> (Eq.{succ u1} (Filter.{u1} α) (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) (nhdsWithin.{u1} α _inst_1 x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x))) (Filter.principal.{u1} α S)) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))))
Case conversion may be inaccurate. Consider using '#align discrete_topology_subtype_iff discreteTopology_subtype_iffₓ'. -/
theorem discreteTopology_subtype_iff {S : Set α} : DiscreteTopology S ↔ ∀ x ∈ S, 𝓝[≠] x ⊓ 𝓟 S = ⊥ :=
  by simp_rw [discreteTopology_iff_nhds_ne, SetCoe.forall', nhds_ne_subtype_eq_bot_iff]
#align discrete_topology_subtype_iff discreteTopology_subtype_iff

end Topα

#print CofiniteTopology /-
/-- A type synonym equiped with the topology whose open sets are the empty set and the sets with
finite complements. -/
def CofiniteTopology (α : Type _) :=
  α
#align cofinite_topology CofiniteTopology
-/

namespace CofiniteTopology

#print CofiniteTopology.of /-
/-- The identity equivalence between `α` and `cofinite_topology α`. -/
def of : α ≃ CofiniteTopology α :=
  Equiv.refl α
#align cofinite_topology.of CofiniteTopology.of
-/

instance [Inhabited α] : Inhabited (CofiniteTopology α) where default := of default

instance : TopologicalSpace (CofiniteTopology α)
    where
  IsOpen s := s.Nonempty → Set.Finite (sᶜ)
  isOpen_univ := by simp
  isOpen_inter s t := by
    rintro hs ht ⟨x, hxs, hxt⟩
    rw [compl_inter]
    exact (hs ⟨x, hxs⟩).union (ht ⟨x, hxt⟩)
  isOpen_unionₛ := by
    rintro s h ⟨x, t, hts, hzt⟩
    rw [Set.compl_unionₛ]
    exact Set.Finite.interₛ (mem_image_of_mem _ hts) (h t hts ⟨x, hzt⟩)

/- warning: cofinite_topology.is_open_iff -> CofiniteTopology.isOpen_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} (CofiniteTopology.{u1} α)}, Iff (IsOpen.{u1} (CofiniteTopology.{u1} α) (CofiniteTopology.topologicalSpace.{u1} α) s) ((Set.Nonempty.{u1} (CofiniteTopology.{u1} α) s) -> (Set.Finite.{u1} (CofiniteTopology.{u1} α) (HasCompl.compl.{u1} (Set.{u1} (CofiniteTopology.{u1} α)) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} (CofiniteTopology.{u1} α)) (Set.booleanAlgebra.{u1} (CofiniteTopology.{u1} α))) s)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} (CofiniteTopology.{u1} α)}, Iff (IsOpen.{u1} (CofiniteTopology.{u1} α) (CofiniteTopology.instTopologicalSpaceCofiniteTopology.{u1} α) s) ((Set.Nonempty.{u1} (CofiniteTopology.{u1} α) s) -> (Set.Finite.{u1} (CofiniteTopology.{u1} α) (HasCompl.compl.{u1} (Set.{u1} (CofiniteTopology.{u1} α)) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} (CofiniteTopology.{u1} α)) (Set.instBooleanAlgebraSet.{u1} (CofiniteTopology.{u1} α))) s)))
Case conversion may be inaccurate. Consider using '#align cofinite_topology.is_open_iff CofiniteTopology.isOpen_iffₓ'. -/
theorem isOpen_iff {s : Set (CofiniteTopology α)} : IsOpen s ↔ s.Nonempty → sᶜ.Finite :=
  Iff.rfl
#align cofinite_topology.is_open_iff CofiniteTopology.isOpen_iff

/- warning: cofinite_topology.is_open_iff' -> CofiniteTopology.isOpen_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} (CofiniteTopology.{u1} α)}, Iff (IsOpen.{u1} (CofiniteTopology.{u1} α) (CofiniteTopology.topologicalSpace.{u1} α) s) (Or (Eq.{succ u1} (Set.{u1} (CofiniteTopology.{u1} α)) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} (CofiniteTopology.{u1} α)) (Set.hasEmptyc.{u1} (CofiniteTopology.{u1} α)))) (Set.Finite.{u1} (CofiniteTopology.{u1} α) (HasCompl.compl.{u1} (Set.{u1} (CofiniteTopology.{u1} α)) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} (CofiniteTopology.{u1} α)) (Set.booleanAlgebra.{u1} (CofiniteTopology.{u1} α))) s)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} (CofiniteTopology.{u1} α)}, Iff (IsOpen.{u1} (CofiniteTopology.{u1} α) (CofiniteTopology.instTopologicalSpaceCofiniteTopology.{u1} α) s) (Or (Eq.{succ u1} (Set.{u1} (CofiniteTopology.{u1} α)) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} (CofiniteTopology.{u1} α)) (Set.instEmptyCollectionSet.{u1} (CofiniteTopology.{u1} α)))) (Set.Finite.{u1} (CofiniteTopology.{u1} α) (HasCompl.compl.{u1} (Set.{u1} (CofiniteTopology.{u1} α)) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} (CofiniteTopology.{u1} α)) (Set.instBooleanAlgebraSet.{u1} (CofiniteTopology.{u1} α))) s)))
Case conversion may be inaccurate. Consider using '#align cofinite_topology.is_open_iff' CofiniteTopology.isOpen_iff'ₓ'. -/
theorem isOpen_iff' {s : Set (CofiniteTopology α)} : IsOpen s ↔ s = ∅ ∨ sᶜ.Finite := by
  simp only [is_open_iff, nonempty_iff_ne_empty, or_iff_not_imp_left]
#align cofinite_topology.is_open_iff' CofiniteTopology.isOpen_iff'

/- warning: cofinite_topology.is_closed_iff -> CofiniteTopology.isClosed_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} (CofiniteTopology.{u1} α)}, Iff (IsClosed.{u1} (CofiniteTopology.{u1} α) (CofiniteTopology.topologicalSpace.{u1} α) s) (Or (Eq.{succ u1} (Set.{u1} (CofiniteTopology.{u1} α)) s (Set.univ.{u1} (CofiniteTopology.{u1} α))) (Set.Finite.{u1} (CofiniteTopology.{u1} α) s))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} (CofiniteTopology.{u1} α)}, Iff (IsClosed.{u1} (CofiniteTopology.{u1} α) (CofiniteTopology.instTopologicalSpaceCofiniteTopology.{u1} α) s) (Or (Eq.{succ u1} (Set.{u1} (CofiniteTopology.{u1} α)) s (Set.univ.{u1} (CofiniteTopology.{u1} α))) (Set.Finite.{u1} (CofiniteTopology.{u1} α) s))
Case conversion may be inaccurate. Consider using '#align cofinite_topology.is_closed_iff CofiniteTopology.isClosed_iffₓ'. -/
theorem isClosed_iff {s : Set (CofiniteTopology α)} : IsClosed s ↔ s = univ ∨ s.Finite := by
  simp [← isOpen_compl_iff, is_open_iff']
#align cofinite_topology.is_closed_iff CofiniteTopology.isClosed_iff

/- warning: cofinite_topology.nhds_eq -> CofiniteTopology.nhds_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : CofiniteTopology.{u1} α), Eq.{succ u1} (Filter.{u1} (CofiniteTopology.{u1} α)) (nhds.{u1} (CofiniteTopology.{u1} α) (CofiniteTopology.topologicalSpace.{u1} α) a) (HasSup.sup.{u1} (Filter.{u1} (CofiniteTopology.{u1} α)) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} (CofiniteTopology.{u1} α)) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} (CofiniteTopology.{u1} α)) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} (CofiniteTopology.{u1} α)) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} (CofiniteTopology.{u1} α)) (Filter.completeLattice.{u1} (CofiniteTopology.{u1} α)))))) (Pure.pure.{u1, u1} Filter.{u1} Filter.hasPure.{u1} (CofiniteTopology.{u1} α) a) (Filter.cofinite.{u1} (CofiniteTopology.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} (a : CofiniteTopology.{u1} α), Eq.{succ u1} (Filter.{u1} (CofiniteTopology.{u1} α)) (nhds.{u1} (CofiniteTopology.{u1} α) (CofiniteTopology.instTopologicalSpaceCofiniteTopology.{u1} α) a) (HasSup.sup.{u1} (Filter.{u1} (CofiniteTopology.{u1} α)) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} (CofiniteTopology.{u1} α)) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} (CofiniteTopology.{u1} α)) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} (CofiniteTopology.{u1} α)) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} (CofiniteTopology.{u1} α)) (Filter.instCompleteLatticeFilter.{u1} (CofiniteTopology.{u1} α)))))) (Pure.pure.{u1, u1} Filter.{u1} Filter.instPureFilter.{u1} (CofiniteTopology.{u1} α) a) (Filter.cofinite.{u1} (CofiniteTopology.{u1} α)))
Case conversion may be inaccurate. Consider using '#align cofinite_topology.nhds_eq CofiniteTopology.nhds_eqₓ'. -/
theorem nhds_eq (a : CofiniteTopology α) : 𝓝 a = pure a ⊔ cofinite :=
  by
  ext U
  rw [mem_nhds_iff]
  constructor
  · rintro ⟨V, hVU, V_op, haV⟩
    exact mem_sup.mpr ⟨hVU haV, mem_of_superset (V_op ⟨_, haV⟩) hVU⟩
  · rintro ⟨hU : a ∈ U, hU' : Uᶜ.Finite⟩
    exact ⟨U, subset.rfl, fun h => hU', hU⟩
#align cofinite_topology.nhds_eq CofiniteTopology.nhds_eq

/- warning: cofinite_topology.mem_nhds_iff -> CofiniteTopology.mem_nhds_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : CofiniteTopology.{u1} α} {s : Set.{u1} (CofiniteTopology.{u1} α)}, Iff (Membership.Mem.{u1, u1} (Set.{u1} (CofiniteTopology.{u1} α)) (Filter.{u1} (CofiniteTopology.{u1} α)) (Filter.hasMem.{u1} (CofiniteTopology.{u1} α)) s (nhds.{u1} (CofiniteTopology.{u1} α) (CofiniteTopology.topologicalSpace.{u1} α) a)) (And (Membership.Mem.{u1, u1} (CofiniteTopology.{u1} α) (Set.{u1} (CofiniteTopology.{u1} α)) (Set.hasMem.{u1} (CofiniteTopology.{u1} α)) a s) (Set.Finite.{u1} (CofiniteTopology.{u1} α) (HasCompl.compl.{u1} (Set.{u1} (CofiniteTopology.{u1} α)) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} (CofiniteTopology.{u1} α)) (Set.booleanAlgebra.{u1} (CofiniteTopology.{u1} α))) s)))
but is expected to have type
  forall {α : Type.{u1}} {a : CofiniteTopology.{u1} α} {s : Set.{u1} (CofiniteTopology.{u1} α)}, Iff (Membership.mem.{u1, u1} (Set.{u1} (CofiniteTopology.{u1} α)) (Filter.{u1} (CofiniteTopology.{u1} α)) (instMembershipSetFilter.{u1} (CofiniteTopology.{u1} α)) s (nhds.{u1} (CofiniteTopology.{u1} α) (CofiniteTopology.instTopologicalSpaceCofiniteTopology.{u1} α) a)) (And (Membership.mem.{u1, u1} (CofiniteTopology.{u1} α) (Set.{u1} (CofiniteTopology.{u1} α)) (Set.instMembershipSet.{u1} (CofiniteTopology.{u1} α)) a s) (Set.Finite.{u1} (CofiniteTopology.{u1} α) (HasCompl.compl.{u1} (Set.{u1} (CofiniteTopology.{u1} α)) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} (CofiniteTopology.{u1} α)) (Set.instBooleanAlgebraSet.{u1} (CofiniteTopology.{u1} α))) s)))
Case conversion may be inaccurate. Consider using '#align cofinite_topology.mem_nhds_iff CofiniteTopology.mem_nhds_iffₓ'. -/
theorem mem_nhds_iff {a : CofiniteTopology α} {s : Set (CofiniteTopology α)} :
    s ∈ 𝓝 a ↔ a ∈ s ∧ sᶜ.Finite := by simp [nhds_eq]
#align cofinite_topology.mem_nhds_iff CofiniteTopology.mem_nhds_iff

end CofiniteTopology

end Constructions

section Prod

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]
  [TopologicalSpace ε] [TopologicalSpace ζ]

/- warning: continuous_fst -> continuous_fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], Continuous.{max u1 u2, u1} (Prod.{u1, u2} α β) α (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_1 (Prod.fst.{u1, u2} α β)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], Continuous.{max u1 u2, u1} (Prod.{u1, u2} α β) α (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) _inst_1 (Prod.fst.{u1, u2} α β)
Case conversion may be inaccurate. Consider using '#align continuous_fst continuous_fstₓ'. -/
@[continuity]
theorem continuous_fst : Continuous (@Prod.fst α β) :=
  continuous_inf_dom_left continuous_induced_dom
#align continuous_fst continuous_fst

/- warning: continuous.fst -> Continuous.fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {f : α -> (Prod.{u2, u3} β γ)}, (Continuous.{u1, max u2 u3} α (Prod.{u2, u3} β γ) _inst_1 (Prod.topologicalSpace.{u2, u3} β γ _inst_2 _inst_3) f) -> (Continuous.{u1, u2} α β _inst_1 _inst_2 (fun (a : α) => Prod.fst.{u2, u3} β γ (f a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u1} γ] {f : α -> (Prod.{u3, u1} β γ)}, (Continuous.{u2, max u3 u1} α (Prod.{u3, u1} β γ) _inst_1 (instTopologicalSpaceProd.{u3, u1} β γ _inst_2 _inst_3) f) -> (Continuous.{u2, u3} α β _inst_1 _inst_2 (fun (a : α) => Prod.fst.{u3, u1} β γ (f a)))
Case conversion may be inaccurate. Consider using '#align continuous.fst Continuous.fstₓ'. -/
/-- Postcomposing `f` with `prod.fst` is continuous -/
theorem Continuous.fst {f : α → β × γ} (hf : Continuous f) : Continuous fun a : α => (f a).1 :=
  continuous_fst.comp hf
#align continuous.fst Continuous.fst

/- warning: continuous.fst' -> Continuous.fst' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {f : α -> γ}, (Continuous.{u1, u3} α γ _inst_1 _inst_3 f) -> (Continuous.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3 (fun (x : Prod.{u1, u2} α β) => f (Prod.fst.{u1, u2} α β x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u1} γ] {f : α -> γ}, (Continuous.{u2, u1} α γ _inst_1 _inst_3 f) -> (Continuous.{max u2 u3, u1} (Prod.{u2, u3} α β) γ (instTopologicalSpaceProd.{u2, u3} α β _inst_1 _inst_2) _inst_3 (fun (x : Prod.{u2, u3} α β) => f (Prod.fst.{u2, u3} α β x)))
Case conversion may be inaccurate. Consider using '#align continuous.fst' Continuous.fst'ₓ'. -/
/-- Precomposing `f` with `prod.fst` is continuous -/
theorem Continuous.fst' {f : α → γ} (hf : Continuous f) : Continuous fun x : α × β => f x.fst :=
  hf.comp continuous_fst
#align continuous.fst' Continuous.fst'

/- warning: continuous_at_fst -> continuousAt_fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {p : Prod.{u1, u2} α β}, ContinuousAt.{max u1 u2, u1} (Prod.{u1, u2} α β) α (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_1 (Prod.fst.{u1, u2} α β) p
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {p : Prod.{u1, u2} α β}, ContinuousAt.{max u2 u1, u1} (Prod.{u1, u2} α β) α (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) _inst_1 (Prod.fst.{u1, u2} α β) p
Case conversion may be inaccurate. Consider using '#align continuous_at_fst continuousAt_fstₓ'. -/
theorem continuousAt_fst {p : α × β} : ContinuousAt Prod.fst p :=
  continuous_fst.ContinuousAt
#align continuous_at_fst continuousAt_fst

/- warning: continuous_at.fst -> ContinuousAt.fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {f : α -> (Prod.{u2, u3} β γ)} {x : α}, (ContinuousAt.{u1, max u2 u3} α (Prod.{u2, u3} β γ) _inst_1 (Prod.topologicalSpace.{u2, u3} β γ _inst_2 _inst_3) f x) -> (ContinuousAt.{u1, u2} α β _inst_1 _inst_2 (fun (a : α) => Prod.fst.{u2, u3} β γ (f a)) x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u1} γ] {f : α -> (Prod.{u3, u1} β γ)} {x : α}, (ContinuousAt.{u2, max u3 u1} α (Prod.{u3, u1} β γ) _inst_1 (instTopologicalSpaceProd.{u3, u1} β γ _inst_2 _inst_3) f x) -> (ContinuousAt.{u2, u3} α β _inst_1 _inst_2 (fun (a : α) => Prod.fst.{u3, u1} β γ (f a)) x)
Case conversion may be inaccurate. Consider using '#align continuous_at.fst ContinuousAt.fstₓ'. -/
/-- Postcomposing `f` with `prod.fst` is continuous at `x` -/
theorem ContinuousAt.fst {f : α → β × γ} {x : α} (hf : ContinuousAt f x) :
    ContinuousAt (fun a : α => (f a).1) x :=
  continuousAt_fst.comp hf
#align continuous_at.fst ContinuousAt.fst

/- warning: continuous_at.fst' -> ContinuousAt.fst' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {f : α -> γ} {x : α} {y : β}, (ContinuousAt.{u1, u3} α γ _inst_1 _inst_3 f x) -> (ContinuousAt.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3 (fun (x : Prod.{u1, u2} α β) => f (Prod.fst.{u1, u2} α β x)) (Prod.mk.{u1, u2} α β x y))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u1} γ] {f : α -> γ} {x : α} {y : β}, (ContinuousAt.{u2, u1} α γ _inst_1 _inst_3 f x) -> (ContinuousAt.{max u2 u3, u1} (Prod.{u2, u3} α β) γ (instTopologicalSpaceProd.{u2, u3} α β _inst_1 _inst_2) _inst_3 (fun (x : Prod.{u2, u3} α β) => f (Prod.fst.{u2, u3} α β x)) (Prod.mk.{u2, u3} α β x y))
Case conversion may be inaccurate. Consider using '#align continuous_at.fst' ContinuousAt.fst'ₓ'. -/
/-- Precomposing `f` with `prod.fst` is continuous at `(x, y)` -/
theorem ContinuousAt.fst' {f : α → γ} {x : α} {y : β} (hf : ContinuousAt f x) :
    ContinuousAt (fun x : α × β => f x.fst) (x, y) :=
  ContinuousAt.comp hf continuousAt_fst
#align continuous_at.fst' ContinuousAt.fst'

/- warning: continuous_at.fst'' -> ContinuousAt.fst'' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {f : α -> γ} {x : Prod.{u1, u2} α β}, (ContinuousAt.{u1, u3} α γ _inst_1 _inst_3 f (Prod.fst.{u1, u2} α β x)) -> (ContinuousAt.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3 (fun (x : Prod.{u1, u2} α β) => f (Prod.fst.{u1, u2} α β x)) x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u1} γ] {f : α -> γ} {x : Prod.{u2, u3} α β}, (ContinuousAt.{u2, u1} α γ _inst_1 _inst_3 f (Prod.fst.{u2, u3} α β x)) -> (ContinuousAt.{max u2 u3, u1} (Prod.{u2, u3} α β) γ (instTopologicalSpaceProd.{u2, u3} α β _inst_1 _inst_2) _inst_3 (fun (x : Prod.{u2, u3} α β) => f (Prod.fst.{u2, u3} α β x)) x)
Case conversion may be inaccurate. Consider using '#align continuous_at.fst'' ContinuousAt.fst''ₓ'. -/
/-- Precomposing `f` with `prod.fst` is continuous at `x : α × β` -/
theorem ContinuousAt.fst'' {f : α → γ} {x : α × β} (hf : ContinuousAt f x.fst) :
    ContinuousAt (fun x : α × β => f x.fst) x :=
  hf.comp continuousAt_fst
#align continuous_at.fst'' ContinuousAt.fst''

/- warning: continuous_snd -> continuous_snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], Continuous.{max u1 u2, u2} (Prod.{u1, u2} α β) β (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_2 (Prod.snd.{u1, u2} α β)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], Continuous.{max u1 u2, u2} (Prod.{u1, u2} α β) β (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) _inst_2 (Prod.snd.{u1, u2} α β)
Case conversion may be inaccurate. Consider using '#align continuous_snd continuous_sndₓ'. -/
@[continuity]
theorem continuous_snd : Continuous (@Prod.snd α β) :=
  continuous_inf_dom_right continuous_induced_dom
#align continuous_snd continuous_snd

/- warning: continuous.snd -> Continuous.snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {f : α -> (Prod.{u2, u3} β γ)}, (Continuous.{u1, max u2 u3} α (Prod.{u2, u3} β γ) _inst_1 (Prod.topologicalSpace.{u2, u3} β γ _inst_2 _inst_3) f) -> (Continuous.{u1, u3} α γ _inst_1 _inst_3 (fun (a : α) => Prod.snd.{u2, u3} β γ (f a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u1} γ] {f : α -> (Prod.{u3, u1} β γ)}, (Continuous.{u2, max u3 u1} α (Prod.{u3, u1} β γ) _inst_1 (instTopologicalSpaceProd.{u3, u1} β γ _inst_2 _inst_3) f) -> (Continuous.{u2, u1} α γ _inst_1 _inst_3 (fun (a : α) => Prod.snd.{u3, u1} β γ (f a)))
Case conversion may be inaccurate. Consider using '#align continuous.snd Continuous.sndₓ'. -/
/-- Postcomposing `f` with `prod.snd` is continuous -/
theorem Continuous.snd {f : α → β × γ} (hf : Continuous f) : Continuous fun a : α => (f a).2 :=
  continuous_snd.comp hf
#align continuous.snd Continuous.snd

/- warning: continuous.snd' -> Continuous.snd' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {f : β -> γ}, (Continuous.{u2, u3} β γ _inst_2 _inst_3 f) -> (Continuous.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3 (fun (x : Prod.{u1, u2} α β) => f (Prod.snd.{u1, u2} α β x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u1} γ] {f : β -> γ}, (Continuous.{u3, u1} β γ _inst_2 _inst_3 f) -> (Continuous.{max u2 u3, u1} (Prod.{u2, u3} α β) γ (instTopologicalSpaceProd.{u2, u3} α β _inst_1 _inst_2) _inst_3 (fun (x : Prod.{u2, u3} α β) => f (Prod.snd.{u2, u3} α β x)))
Case conversion may be inaccurate. Consider using '#align continuous.snd' Continuous.snd'ₓ'. -/
/-- Precomposing `f` with `prod.snd` is continuous -/
theorem Continuous.snd' {f : β → γ} (hf : Continuous f) : Continuous fun x : α × β => f x.snd :=
  hf.comp continuous_snd
#align continuous.snd' Continuous.snd'

/- warning: continuous_at_snd -> continuousAt_snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {p : Prod.{u1, u2} α β}, ContinuousAt.{max u1 u2, u2} (Prod.{u1, u2} α β) β (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_2 (Prod.snd.{u1, u2} α β) p
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {p : Prod.{u1, u2} α β}, ContinuousAt.{max u2 u1, u2} (Prod.{u1, u2} α β) β (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) _inst_2 (Prod.snd.{u1, u2} α β) p
Case conversion may be inaccurate. Consider using '#align continuous_at_snd continuousAt_sndₓ'. -/
theorem continuousAt_snd {p : α × β} : ContinuousAt Prod.snd p :=
  continuous_snd.ContinuousAt
#align continuous_at_snd continuousAt_snd

/- warning: continuous_at.snd -> ContinuousAt.snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {f : α -> (Prod.{u2, u3} β γ)} {x : α}, (ContinuousAt.{u1, max u2 u3} α (Prod.{u2, u3} β γ) _inst_1 (Prod.topologicalSpace.{u2, u3} β γ _inst_2 _inst_3) f x) -> (ContinuousAt.{u1, u3} α γ _inst_1 _inst_3 (fun (a : α) => Prod.snd.{u2, u3} β γ (f a)) x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u1} γ] {f : α -> (Prod.{u3, u1} β γ)} {x : α}, (ContinuousAt.{u2, max u3 u1} α (Prod.{u3, u1} β γ) _inst_1 (instTopologicalSpaceProd.{u3, u1} β γ _inst_2 _inst_3) f x) -> (ContinuousAt.{u2, u1} α γ _inst_1 _inst_3 (fun (a : α) => Prod.snd.{u3, u1} β γ (f a)) x)
Case conversion may be inaccurate. Consider using '#align continuous_at.snd ContinuousAt.sndₓ'. -/
/-- Postcomposing `f` with `prod.snd` is continuous at `x` -/
theorem ContinuousAt.snd {f : α → β × γ} {x : α} (hf : ContinuousAt f x) :
    ContinuousAt (fun a : α => (f a).2) x :=
  continuousAt_snd.comp hf
#align continuous_at.snd ContinuousAt.snd

/- warning: continuous_at.snd' -> ContinuousAt.snd' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {f : β -> γ} {x : α} {y : β}, (ContinuousAt.{u2, u3} β γ _inst_2 _inst_3 f y) -> (ContinuousAt.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3 (fun (x : Prod.{u1, u2} α β) => f (Prod.snd.{u1, u2} α β x)) (Prod.mk.{u1, u2} α β x y))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u1} γ] {f : β -> γ} {x : α} {y : β}, (ContinuousAt.{u3, u1} β γ _inst_2 _inst_3 f y) -> (ContinuousAt.{max u2 u3, u1} (Prod.{u2, u3} α β) γ (instTopologicalSpaceProd.{u2, u3} α β _inst_1 _inst_2) _inst_3 (fun (x : Prod.{u2, u3} α β) => f (Prod.snd.{u2, u3} α β x)) (Prod.mk.{u2, u3} α β x y))
Case conversion may be inaccurate. Consider using '#align continuous_at.snd' ContinuousAt.snd'ₓ'. -/
/-- Precomposing `f` with `prod.snd` is continuous at `(x, y)` -/
theorem ContinuousAt.snd' {f : β → γ} {x : α} {y : β} (hf : ContinuousAt f y) :
    ContinuousAt (fun x : α × β => f x.snd) (x, y) :=
  ContinuousAt.comp hf continuousAt_snd
#align continuous_at.snd' ContinuousAt.snd'

/- warning: continuous_at.snd'' -> ContinuousAt.snd'' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {f : β -> γ} {x : Prod.{u1, u2} α β}, (ContinuousAt.{u2, u3} β γ _inst_2 _inst_3 f (Prod.snd.{u1, u2} α β x)) -> (ContinuousAt.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3 (fun (x : Prod.{u1, u2} α β) => f (Prod.snd.{u1, u2} α β x)) x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u1} γ] {f : β -> γ} {x : Prod.{u2, u3} α β}, (ContinuousAt.{u3, u1} β γ _inst_2 _inst_3 f (Prod.snd.{u2, u3} α β x)) -> (ContinuousAt.{max u2 u3, u1} (Prod.{u2, u3} α β) γ (instTopologicalSpaceProd.{u2, u3} α β _inst_1 _inst_2) _inst_3 (fun (x : Prod.{u2, u3} α β) => f (Prod.snd.{u2, u3} α β x)) x)
Case conversion may be inaccurate. Consider using '#align continuous_at.snd'' ContinuousAt.snd''ₓ'. -/
/-- Precomposing `f` with `prod.snd` is continuous at `x : α × β` -/
theorem ContinuousAt.snd'' {f : β → γ} {x : α × β} (hf : ContinuousAt f x.snd) :
    ContinuousAt (fun x : α × β => f x.snd) x :=
  hf.comp continuousAt_snd
#align continuous_at.snd'' ContinuousAt.snd''

/- warning: continuous.prod_mk -> Continuous.prod_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {f : γ -> α} {g : γ -> β}, (Continuous.{u3, u1} γ α _inst_3 _inst_1 f) -> (Continuous.{u3, u2} γ β _inst_3 _inst_2 g) -> (Continuous.{u3, max u1 u2} γ (Prod.{u1, u2} α β) _inst_3 (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (fun (x : γ) => Prod.mk.{u1, u2} α β (f x) (g x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u1} γ] {f : γ -> α} {g : γ -> β}, (Continuous.{u1, u2} γ α _inst_3 _inst_1 f) -> (Continuous.{u1, u3} γ β _inst_3 _inst_2 g) -> (Continuous.{u1, max u3 u2} γ (Prod.{u2, u3} α β) _inst_3 (instTopologicalSpaceProd.{u2, u3} α β _inst_1 _inst_2) (fun (x : γ) => Prod.mk.{u2, u3} α β (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align continuous.prod_mk Continuous.prod_mkₓ'. -/
@[continuity]
theorem Continuous.prod_mk {f : γ → α} {g : γ → β} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => (f x, g x) :=
  continuous_inf_rng.2 ⟨continuous_induced_rng.2 hf, continuous_induced_rng.2 hg⟩
#align continuous.prod_mk Continuous.prod_mk

/- warning: continuous_prod_mk -> continuous_prod_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {f : α -> β} {g : α -> γ}, Iff (Continuous.{u1, max u2 u3} α (Prod.{u2, u3} β γ) _inst_1 (Prod.topologicalSpace.{u2, u3} β γ _inst_2 _inst_3) (fun (x : α) => Prod.mk.{u2, u3} β γ (f x) (g x))) (And (Continuous.{u1, u2} α β _inst_1 _inst_2 f) (Continuous.{u1, u3} α γ _inst_1 _inst_3 g))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u1} γ] {f : α -> β} {g : α -> γ}, Iff (Continuous.{u2, max u1 u3} α (Prod.{u3, u1} β γ) _inst_1 (instTopologicalSpaceProd.{u3, u1} β γ _inst_2 _inst_3) (fun (x : α) => Prod.mk.{u3, u1} β γ (f x) (g x))) (And (Continuous.{u2, u3} α β _inst_1 _inst_2 f) (Continuous.{u2, u1} α γ _inst_1 _inst_3 g))
Case conversion may be inaccurate. Consider using '#align continuous_prod_mk continuous_prod_mkₓ'. -/
@[simp]
theorem continuous_prod_mk {f : α → β} {g : α → γ} :
    (Continuous fun x => (f x, g x)) ↔ Continuous f ∧ Continuous g :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.prod_mk h.2⟩
#align continuous_prod_mk continuous_prod_mk

/- warning: continuous.prod.mk -> Continuous.Prod.mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (a : α), Continuous.{u2, max u1 u2} β (Prod.{u1, u2} α β) _inst_2 (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (fun (b : β) => Prod.mk.{u1, u2} α β a b)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (a : α), Continuous.{u2, max u2 u1} β (Prod.{u1, u2} α β) _inst_2 (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) (fun (b : β) => Prod.mk.{u1, u2} α β a b)
Case conversion may be inaccurate. Consider using '#align continuous.prod.mk Continuous.Prod.mkₓ'. -/
@[continuity]
theorem Continuous.Prod.mk (a : α) : Continuous fun b : β => (a, b) :=
  continuous_const.prod_mk continuous_id'
#align continuous.prod.mk Continuous.Prod.mk

/- warning: continuous.prod.mk_left -> Continuous.Prod.mk_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (b : β), Continuous.{u1, max u1 u2} α (Prod.{u1, u2} α β) _inst_1 (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (fun (a : α) => Prod.mk.{u1, u2} α β a b)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (b : β), Continuous.{u1, max u2 u1} α (Prod.{u1, u2} α β) _inst_1 (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) (fun (a : α) => Prod.mk.{u1, u2} α β a b)
Case conversion may be inaccurate. Consider using '#align continuous.prod.mk_left Continuous.Prod.mk_leftₓ'. -/
@[continuity]
theorem Continuous.Prod.mk_left (b : β) : Continuous fun a : α => (a, b) :=
  continuous_id'.prod_mk continuous_const
#align continuous.prod.mk_left Continuous.Prod.mk_left

/- warning: continuous.comp₂ -> Continuous.comp₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] {g : (Prod.{u1, u2} α β) -> γ}, (Continuous.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3 g) -> (forall {e : δ -> α}, (Continuous.{u4, u1} δ α _inst_4 _inst_1 e) -> (forall {f : δ -> β}, (Continuous.{u4, u2} δ β _inst_4 _inst_2 f) -> (Continuous.{u4, u3} δ γ _inst_4 _inst_3 (fun (x : δ) => g (Prod.mk.{u1, u2} α β (e x) (f x))))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {γ : Type.{u2}} {δ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u4} β] [_inst_3 : TopologicalSpace.{u2} γ] [_inst_4 : TopologicalSpace.{u1} δ] {g : (Prod.{u3, u4} α β) -> γ}, (Continuous.{max u3 u4, u2} (Prod.{u3, u4} α β) γ (instTopologicalSpaceProd.{u3, u4} α β _inst_1 _inst_2) _inst_3 g) -> (forall {e : δ -> α}, (Continuous.{u1, u3} δ α _inst_4 _inst_1 e) -> (forall {f : δ -> β}, (Continuous.{u1, u4} δ β _inst_4 _inst_2 f) -> (Continuous.{u1, u2} δ γ _inst_4 _inst_3 (fun (x : δ) => g (Prod.mk.{u3, u4} α β (e x) (f x))))))
Case conversion may be inaccurate. Consider using '#align continuous.comp₂ Continuous.comp₂ₓ'. -/
theorem Continuous.comp₂ {g : α × β → γ} (hg : Continuous g) {e : δ → α} (he : Continuous e)
    {f : δ → β} (hf : Continuous f) : Continuous fun x => g (e x, f x) :=
  hg.comp <| he.prod_mk hf
#align continuous.comp₂ Continuous.comp₂

/- warning: continuous.comp₃ -> Continuous.comp₃ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {ε : Type.{u5}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] [_inst_5 : TopologicalSpace.{u5} ε] {g : (Prod.{u1, max u2 u3} α (Prod.{u2, u3} β γ)) -> ε}, (Continuous.{max u1 u2 u3, u5} (Prod.{u1, max u2 u3} α (Prod.{u2, u3} β γ)) ε (Prod.topologicalSpace.{u1, max u2 u3} α (Prod.{u2, u3} β γ) _inst_1 (Prod.topologicalSpace.{u2, u3} β γ _inst_2 _inst_3)) _inst_5 g) -> (forall {e : δ -> α}, (Continuous.{u4, u1} δ α _inst_4 _inst_1 e) -> (forall {f : δ -> β}, (Continuous.{u4, u2} δ β _inst_4 _inst_2 f) -> (forall {k : δ -> γ}, (Continuous.{u4, u3} δ γ _inst_4 _inst_3 k) -> (Continuous.{u4, u5} δ ε _inst_4 _inst_5 (fun (x : δ) => g (Prod.mk.{u1, max u2 u3} α (Prod.{u2, u3} β γ) (e x) (Prod.mk.{u2, u3} β γ (f x) (k x))))))))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u5}} {γ : Type.{u3}} {δ : Type.{u1}} {ε : Type.{u2}} [_inst_1 : TopologicalSpace.{u4} α] [_inst_2 : TopologicalSpace.{u5} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u1} δ] [_inst_5 : TopologicalSpace.{u2} ε] {g : (Prod.{u4, max u3 u5} α (Prod.{u5, u3} β γ)) -> ε}, (Continuous.{max (max u4 u5) u3, u2} (Prod.{u4, max u3 u5} α (Prod.{u5, u3} β γ)) ε (instTopologicalSpaceProd.{u4, max u5 u3} α (Prod.{u5, u3} β γ) _inst_1 (instTopologicalSpaceProd.{u5, u3} β γ _inst_2 _inst_3)) _inst_5 g) -> (forall {e : δ -> α}, (Continuous.{u1, u4} δ α _inst_4 _inst_1 e) -> (forall {f : δ -> β}, (Continuous.{u1, u5} δ β _inst_4 _inst_2 f) -> (forall {k : δ -> γ}, (Continuous.{u1, u3} δ γ _inst_4 _inst_3 k) -> (Continuous.{u1, u2} δ ε _inst_4 _inst_5 (fun (x : δ) => g (Prod.mk.{u4, max u5 u3} α (Prod.{u5, u3} β γ) (e x) (Prod.mk.{u5, u3} β γ (f x) (k x))))))))
Case conversion may be inaccurate. Consider using '#align continuous.comp₃ Continuous.comp₃ₓ'. -/
theorem Continuous.comp₃ {g : α × β × γ → ε} (hg : Continuous g) {e : δ → α} (he : Continuous e)
    {f : δ → β} (hf : Continuous f) {k : δ → γ} (hk : Continuous k) :
    Continuous fun x => g (e x, f x, k x) :=
  hg.comp₂ he <| hf.prod_mk hk
#align continuous.comp₃ Continuous.comp₃

/- warning: continuous.comp₄ -> Continuous.comp₄ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {ε : Type.{u5}} {ζ : Type.{u6}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] [_inst_5 : TopologicalSpace.{u5} ε] [_inst_6 : TopologicalSpace.{u6} ζ] {g : (Prod.{u1, max u2 u3 u6} α (Prod.{u2, max u3 u6} β (Prod.{u3, u6} γ ζ))) -> ε}, (Continuous.{max u1 u2 u3 u6, u5} (Prod.{u1, max u2 u3 u6} α (Prod.{u2, max u3 u6} β (Prod.{u3, u6} γ ζ))) ε (Prod.topologicalSpace.{u1, max u2 u3 u6} α (Prod.{u2, max u3 u6} β (Prod.{u3, u6} γ ζ)) _inst_1 (Prod.topologicalSpace.{u2, max u3 u6} β (Prod.{u3, u6} γ ζ) _inst_2 (Prod.topologicalSpace.{u3, u6} γ ζ _inst_3 _inst_6))) _inst_5 g) -> (forall {e : δ -> α}, (Continuous.{u4, u1} δ α _inst_4 _inst_1 e) -> (forall {f : δ -> β}, (Continuous.{u4, u2} δ β _inst_4 _inst_2 f) -> (forall {k : δ -> γ}, (Continuous.{u4, u3} δ γ _inst_4 _inst_3 k) -> (forall {l : δ -> ζ}, (Continuous.{u4, u6} δ ζ _inst_4 _inst_6 l) -> (Continuous.{u4, u5} δ ε _inst_4 _inst_5 (fun (x : δ) => g (Prod.mk.{u1, max u2 u3 u6} α (Prod.{u2, max u3 u6} β (Prod.{u3, u6} γ ζ)) (e x) (Prod.mk.{u2, max u3 u6} β (Prod.{u3, u6} γ ζ) (f x) (Prod.mk.{u3, u6} γ ζ (k x) (l x))))))))))
but is expected to have type
  forall {α : Type.{u5}} {β : Type.{u6}} {γ : Type.{u3}} {δ : Type.{u1}} {ε : Type.{u2}} {ζ : Type.{u4}} [_inst_1 : TopologicalSpace.{u5} α] [_inst_2 : TopologicalSpace.{u6} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u1} δ] [_inst_5 : TopologicalSpace.{u2} ε] [_inst_6 : TopologicalSpace.{u4} ζ] {g : (Prod.{u5, max (max u4 u3) u6} α (Prod.{u6, max u4 u3} β (Prod.{u3, u4} γ ζ))) -> ε}, (Continuous.{max (max (max u5 u6) u3) u4, u2} (Prod.{u5, max (max u4 u3) u6} α (Prod.{u6, max u4 u3} β (Prod.{u3, u4} γ ζ))) ε (instTopologicalSpaceProd.{u5, max (max u6 u3) u4} α (Prod.{u6, max u4 u3} β (Prod.{u3, u4} γ ζ)) _inst_1 (instTopologicalSpaceProd.{u6, max u3 u4} β (Prod.{u3, u4} γ ζ) _inst_2 (instTopologicalSpaceProd.{u3, u4} γ ζ _inst_3 _inst_6))) _inst_5 g) -> (forall {e : δ -> α}, (Continuous.{u1, u5} δ α _inst_4 _inst_1 e) -> (forall {f : δ -> β}, (Continuous.{u1, u6} δ β _inst_4 _inst_2 f) -> (forall {k : δ -> γ}, (Continuous.{u1, u3} δ γ _inst_4 _inst_3 k) -> (forall {l : δ -> ζ}, (Continuous.{u1, u4} δ ζ _inst_4 _inst_6 l) -> (Continuous.{u1, u2} δ ε _inst_4 _inst_5 (fun (x : δ) => g (Prod.mk.{u5, max (max u6 u3) u4} α (Prod.{u6, max u4 u3} β (Prod.{u3, u4} γ ζ)) (e x) (Prod.mk.{u6, max u3 u4} β (Prod.{u3, u4} γ ζ) (f x) (Prod.mk.{u3, u4} γ ζ (k x) (l x))))))))))
Case conversion may be inaccurate. Consider using '#align continuous.comp₄ Continuous.comp₄ₓ'. -/
theorem Continuous.comp₄ {g : α × β × γ × ζ → ε} (hg : Continuous g) {e : δ → α} (he : Continuous e)
    {f : δ → β} (hf : Continuous f) {k : δ → γ} (hk : Continuous k) {l : δ → ζ}
    (hl : Continuous l) : Continuous fun x => g (e x, f x, k x, l x) :=
  hg.comp₃ he hf <| hk.prod_mk hl
#align continuous.comp₄ Continuous.comp₄

/- warning: continuous.prod_map -> Continuous.prod_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] {f : γ -> α} {g : δ -> β}, (Continuous.{u3, u1} γ α _inst_3 _inst_1 f) -> (Continuous.{u4, u2} δ β _inst_4 _inst_2 g) -> (Continuous.{max u3 u4, max u1 u2} (Prod.{u3, u4} γ δ) (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u3, u4} γ δ _inst_3 _inst_4) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (fun (x : Prod.{u3, u4} γ δ) => Prod.mk.{u1, u2} α β (f (Prod.fst.{u3, u4} γ δ x)) (g (Prod.snd.{u3, u4} γ δ x))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {γ : Type.{u2}} {δ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u4} β] [_inst_3 : TopologicalSpace.{u2} γ] [_inst_4 : TopologicalSpace.{u1} δ] {f : γ -> α} {g : δ -> β}, (Continuous.{u2, u3} γ α _inst_3 _inst_1 f) -> (Continuous.{u1, u4} δ β _inst_4 _inst_2 g) -> (Continuous.{max u2 u1, max u4 u3} (Prod.{u2, u1} γ δ) (Prod.{u3, u4} α β) (instTopologicalSpaceProd.{u2, u1} γ δ _inst_3 _inst_4) (instTopologicalSpaceProd.{u3, u4} α β _inst_1 _inst_2) (fun (x : Prod.{u2, u1} γ δ) => Prod.mk.{u3, u4} α β (f (Prod.fst.{u2, u1} γ δ x)) (g (Prod.snd.{u2, u1} γ δ x))))
Case conversion may be inaccurate. Consider using '#align continuous.prod_map Continuous.prod_mapₓ'. -/
theorem Continuous.prod_map {f : γ → α} {g : δ → β} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x : γ × δ => (f x.1, g x.2) :=
  hf.fst'.prod_mk hg.snd'
#align continuous.prod_map Continuous.prod_map

/- warning: continuous_inf_dom_left₂ -> continuous_inf_dom_left₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {ta1 : TopologicalSpace.{u1} α} {ta2 : TopologicalSpace.{u1} α} {tb1 : TopologicalSpace.{u2} β} {tb2 : TopologicalSpace.{u2} β} {tc1 : TopologicalSpace.{u3} γ}, (Continuous.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.topologicalSpace.{u1, u2} α β ta1 tb1) tc1 (fun (p : Prod.{u1, u2} α β) => f (Prod.fst.{u1, u2} α β p) (Prod.snd.{u1, u2} α β p))) -> (Continuous.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.topologicalSpace.{u1, u2} α β (HasInf.inf.{u1} (TopologicalSpace.{u1} α) (SemilatticeInf.toHasInf.{u1} (TopologicalSpace.{u1} α) (Lattice.toSemilatticeInf.{u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))))) ta1 ta2) (HasInf.inf.{u2} (TopologicalSpace.{u2} β) (SemilatticeInf.toHasInf.{u2} (TopologicalSpace.{u2} β) (Lattice.toSemilatticeInf.{u2} (TopologicalSpace.{u2} β) (ConditionallyCompleteLattice.toLattice.{u2} (TopologicalSpace.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.completeLattice.{u2} β))))) tb1 tb2)) tc1 (fun (p : Prod.{u1, u2} α β) => f (Prod.fst.{u1, u2} α β p) (Prod.snd.{u1, u2} α β p)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {f : α -> β -> γ} {ta1 : TopologicalSpace.{u3} α} {ta2 : TopologicalSpace.{u3} α} {tb1 : TopologicalSpace.{u2} β} {tb2 : TopologicalSpace.{u2} β} {tc1 : TopologicalSpace.{u1} γ}, (Continuous.{max u3 u2, u1} (Prod.{u3, u2} α β) γ (instTopologicalSpaceProd.{u3, u2} α β ta1 tb1) tc1 (fun (p : Prod.{u3, u2} α β) => f (Prod.fst.{u3, u2} α β p) (Prod.snd.{u3, u2} α β p))) -> (Continuous.{max u3 u2, u1} (Prod.{u3, u2} α β) γ (instTopologicalSpaceProd.{u3, u2} α β (HasInf.inf.{u3} (TopologicalSpace.{u3} α) (Lattice.toHasInf.{u3} (TopologicalSpace.{u3} α) (ConditionallyCompleteLattice.toLattice.{u3} (TopologicalSpace.{u3} α) (CompleteLattice.toConditionallyCompleteLattice.{u3} (TopologicalSpace.{u3} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u3} α)))) ta1 ta2) (HasInf.inf.{u2} (TopologicalSpace.{u2} β) (Lattice.toHasInf.{u2} (TopologicalSpace.{u2} β) (ConditionallyCompleteLattice.toLattice.{u2} (TopologicalSpace.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u2} β)))) tb1 tb2)) tc1 (fun (p : Prod.{u3, u2} α β) => f (Prod.fst.{u3, u2} α β p) (Prod.snd.{u3, u2} α β p)))
Case conversion may be inaccurate. Consider using '#align continuous_inf_dom_left₂ continuous_inf_dom_left₂ₓ'. -/
/-- A version of `continuous_inf_dom_left` for binary functions -/
theorem continuous_inf_dom_left₂ {α β γ} {f : α → β → γ} {ta1 ta2 : TopologicalSpace α}
    {tb1 tb2 : TopologicalSpace β} {tc1 : TopologicalSpace γ}
    (h : by haveI := ta1 <;> haveI := tb1 <;> exact Continuous fun p : α × β => f p.1 p.2) : by
    haveI := ta1 ⊓ ta2 <;> haveI := tb1 ⊓ tb2 <;> exact Continuous fun p : α × β => f p.1 p.2 :=
  by
  have ha := @continuous_inf_dom_left _ _ id ta1 ta2 ta1 (@continuous_id _ (id _))
  have hb := @continuous_inf_dom_left _ _ id tb1 tb2 tb1 (@continuous_id _ (id _))
  have h_continuous_id := @Continuous.prod_map _ _ _ _ ta1 tb1 (ta1 ⊓ ta2) (tb1 ⊓ tb2) _ _ ha hb
  exact @Continuous.comp _ _ _ (id _) (id _) _ _ _ h h_continuous_id
#align continuous_inf_dom_left₂ continuous_inf_dom_left₂

/- warning: continuous_inf_dom_right₂ -> continuous_inf_dom_right₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {ta1 : TopologicalSpace.{u1} α} {ta2 : TopologicalSpace.{u1} α} {tb1 : TopologicalSpace.{u2} β} {tb2 : TopologicalSpace.{u2} β} {tc1 : TopologicalSpace.{u3} γ}, (Continuous.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.topologicalSpace.{u1, u2} α β ta2 tb2) tc1 (fun (p : Prod.{u1, u2} α β) => f (Prod.fst.{u1, u2} α β p) (Prod.snd.{u1, u2} α β p))) -> (Continuous.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.topologicalSpace.{u1, u2} α β (HasInf.inf.{u1} (TopologicalSpace.{u1} α) (SemilatticeInf.toHasInf.{u1} (TopologicalSpace.{u1} α) (Lattice.toSemilatticeInf.{u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))))) ta1 ta2) (HasInf.inf.{u2} (TopologicalSpace.{u2} β) (SemilatticeInf.toHasInf.{u2} (TopologicalSpace.{u2} β) (Lattice.toSemilatticeInf.{u2} (TopologicalSpace.{u2} β) (ConditionallyCompleteLattice.toLattice.{u2} (TopologicalSpace.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.completeLattice.{u2} β))))) tb1 tb2)) tc1 (fun (p : Prod.{u1, u2} α β) => f (Prod.fst.{u1, u2} α β p) (Prod.snd.{u1, u2} α β p)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {f : α -> β -> γ} {ta1 : TopologicalSpace.{u3} α} {ta2 : TopologicalSpace.{u3} α} {tb1 : TopologicalSpace.{u2} β} {tb2 : TopologicalSpace.{u2} β} {tc1 : TopologicalSpace.{u1} γ}, (Continuous.{max u3 u2, u1} (Prod.{u3, u2} α β) γ (instTopologicalSpaceProd.{u3, u2} α β ta2 tb2) tc1 (fun (p : Prod.{u3, u2} α β) => f (Prod.fst.{u3, u2} α β p) (Prod.snd.{u3, u2} α β p))) -> (Continuous.{max u3 u2, u1} (Prod.{u3, u2} α β) γ (instTopologicalSpaceProd.{u3, u2} α β (HasInf.inf.{u3} (TopologicalSpace.{u3} α) (Lattice.toHasInf.{u3} (TopologicalSpace.{u3} α) (ConditionallyCompleteLattice.toLattice.{u3} (TopologicalSpace.{u3} α) (CompleteLattice.toConditionallyCompleteLattice.{u3} (TopologicalSpace.{u3} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u3} α)))) ta1 ta2) (HasInf.inf.{u2} (TopologicalSpace.{u2} β) (Lattice.toHasInf.{u2} (TopologicalSpace.{u2} β) (ConditionallyCompleteLattice.toLattice.{u2} (TopologicalSpace.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u2} β)))) tb1 tb2)) tc1 (fun (p : Prod.{u3, u2} α β) => f (Prod.fst.{u3, u2} α β p) (Prod.snd.{u3, u2} α β p)))
Case conversion may be inaccurate. Consider using '#align continuous_inf_dom_right₂ continuous_inf_dom_right₂ₓ'. -/
/-- A version of `continuous_inf_dom_right` for binary functions -/
theorem continuous_inf_dom_right₂ {α β γ} {f : α → β → γ} {ta1 ta2 : TopologicalSpace α}
    {tb1 tb2 : TopologicalSpace β} {tc1 : TopologicalSpace γ}
    (h : by haveI := ta2 <;> haveI := tb2 <;> exact Continuous fun p : α × β => f p.1 p.2) : by
    haveI := ta1 ⊓ ta2 <;> haveI := tb1 ⊓ tb2 <;> exact Continuous fun p : α × β => f p.1 p.2 :=
  by
  have ha := @continuous_inf_dom_right _ _ id ta1 ta2 ta2 (@continuous_id _ (id _))
  have hb := @continuous_inf_dom_right _ _ id tb1 tb2 tb2 (@continuous_id _ (id _))
  have h_continuous_id := @Continuous.prod_map _ _ _ _ ta2 tb2 (ta1 ⊓ ta2) (tb1 ⊓ tb2) _ _ ha hb
  exact @Continuous.comp _ _ _ (id _) (id _) _ _ _ h h_continuous_id
#align continuous_inf_dom_right₂ continuous_inf_dom_right₂

/- warning: continuous_Inf_dom₂ -> continuous_infₛ_dom₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β -> γ} {tas : Set.{u1} (TopologicalSpace.{u1} α)} {tbs : Set.{u2} (TopologicalSpace.{u2} β)} {ta : TopologicalSpace.{u1} α} {tb : TopologicalSpace.{u2} β} {tc : TopologicalSpace.{u3} γ}, (Membership.Mem.{u1, u1} (TopologicalSpace.{u1} α) (Set.{u1} (TopologicalSpace.{u1} α)) (Set.hasMem.{u1} (TopologicalSpace.{u1} α)) ta tas) -> (Membership.Mem.{u2, u2} (TopologicalSpace.{u2} β) (Set.{u2} (TopologicalSpace.{u2} β)) (Set.hasMem.{u2} (TopologicalSpace.{u2} β)) tb tbs) -> (Continuous.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.topologicalSpace.{u1, u2} α β ta tb) tc (fun (p : Prod.{u1, u2} α β) => f (Prod.fst.{u1, u2} α β p) (Prod.snd.{u1, u2} α β p))) -> (Continuous.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.topologicalSpace.{u1, u2} α β (InfSet.infₛ.{u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))) tas) (InfSet.infₛ.{u2} (TopologicalSpace.{u2} β) (ConditionallyCompleteLattice.toHasInf.{u2} (TopologicalSpace.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.completeLattice.{u2} β))) tbs)) tc (fun (p : Prod.{u1, u2} α β) => f (Prod.fst.{u1, u2} α β p) (Prod.snd.{u1, u2} α β p)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {f : α -> β -> γ} {tas : Set.{u3} (TopologicalSpace.{u3} α)} {tbs : Set.{u2} (TopologicalSpace.{u2} β)} {ta : TopologicalSpace.{u3} α} {tb : TopologicalSpace.{u2} β} {tc : TopologicalSpace.{u1} γ}, (Membership.mem.{u3, u3} (TopologicalSpace.{u3} α) (Set.{u3} (TopologicalSpace.{u3} α)) (Set.instMembershipSet.{u3} (TopologicalSpace.{u3} α)) ta tas) -> (Membership.mem.{u2, u2} (TopologicalSpace.{u2} β) (Set.{u2} (TopologicalSpace.{u2} β)) (Set.instMembershipSet.{u2} (TopologicalSpace.{u2} β)) tb tbs) -> (Continuous.{max u3 u2, u1} (Prod.{u3, u2} α β) γ (instTopologicalSpaceProd.{u3, u2} α β ta tb) tc (fun (p : Prod.{u3, u2} α β) => f (Prod.fst.{u3, u2} α β p) (Prod.snd.{u3, u2} α β p))) -> (Continuous.{max u3 u2, u1} (Prod.{u3, u2} α β) γ (instTopologicalSpaceProd.{u3, u2} α β (InfSet.infₛ.{u3} (TopologicalSpace.{u3} α) (ConditionallyCompleteLattice.toInfSet.{u3} (TopologicalSpace.{u3} α) (CompleteLattice.toConditionallyCompleteLattice.{u3} (TopologicalSpace.{u3} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u3} α))) tas) (InfSet.infₛ.{u2} (TopologicalSpace.{u2} β) (ConditionallyCompleteLattice.toInfSet.{u2} (TopologicalSpace.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u2} β))) tbs)) tc (fun (p : Prod.{u3, u2} α β) => f (Prod.fst.{u3, u2} α β p) (Prod.snd.{u3, u2} α β p)))
Case conversion may be inaccurate. Consider using '#align continuous_Inf_dom₂ continuous_infₛ_dom₂ₓ'. -/
/-- A version of `continuous_Inf_dom` for binary functions -/
theorem continuous_infₛ_dom₂ {α β γ} {f : α → β → γ} {tas : Set (TopologicalSpace α)}
    {tbs : Set (TopologicalSpace β)} {ta : TopologicalSpace α} {tb : TopologicalSpace β}
    {tc : TopologicalSpace γ} (ha : ta ∈ tas) (hb : tb ∈ tbs)
    (hf : Continuous fun p : α × β => f p.1 p.2) : by
    haveI := Inf tas <;> haveI := Inf tbs <;>
      exact @Continuous _ _ _ tc fun p : α × β => f p.1 p.2 :=
  by
  let t : TopologicalSpace (α × β) := Prod.topologicalSpace
  have ha := continuous_infₛ_dom ha continuous_id
  have hb := continuous_infₛ_dom hb continuous_id
  have h_continuous_id := @Continuous.prod_map _ _ _ _ ta tb (Inf tas) (Inf tbs) _ _ ha hb
  exact @Continuous.comp _ _ _ (id _) (id _) _ _ _ hf h_continuous_id
#align continuous_Inf_dom₂ continuous_infₛ_dom₂

/- warning: filter.eventually.prod_inl_nhds -> Filter.Eventually.prod_inl_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {p : α -> Prop} {a : α}, (Filter.Eventually.{u1} α (fun (x : α) => p x) (nhds.{u1} α _inst_1 a)) -> (forall (b : β), Filter.Eventually.{max u1 u2} (Prod.{u1, u2} α β) (fun (x : Prod.{u1, u2} α β) => p (Prod.fst.{u1, u2} α β x)) (nhds.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Prod.mk.{u1, u2} α β a b)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {p : α -> Prop} {a : α}, (Filter.Eventually.{u1} α (fun (x : α) => p x) (nhds.{u1} α _inst_1 a)) -> (forall (b : β), Filter.Eventually.{max u1 u2} (Prod.{u1, u2} α β) (fun (x : Prod.{u1, u2} α β) => p (Prod.fst.{u1, u2} α β x)) (nhds.{max u1 u2} (Prod.{u1, u2} α β) (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) (Prod.mk.{u1, u2} α β a b)))
Case conversion may be inaccurate. Consider using '#align filter.eventually.prod_inl_nhds Filter.Eventually.prod_inl_nhdsₓ'. -/
theorem Filter.Eventually.prod_inl_nhds {p : α → Prop} {a : α} (h : ∀ᶠ x in 𝓝 a, p x) (b : β) :
    ∀ᶠ x in 𝓝 (a, b), p (x : α × β).1 :=
  continuousAt_fst h
#align filter.eventually.prod_inl_nhds Filter.Eventually.prod_inl_nhds

/- warning: filter.eventually.prod_inr_nhds -> Filter.Eventually.prod_inr_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {p : β -> Prop} {b : β}, (Filter.Eventually.{u2} β (fun (x : β) => p x) (nhds.{u2} β _inst_2 b)) -> (forall (a : α), Filter.Eventually.{max u1 u2} (Prod.{u1, u2} α β) (fun (x : Prod.{u1, u2} α β) => p (Prod.snd.{u1, u2} α β x)) (nhds.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Prod.mk.{u1, u2} α β a b)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {p : β -> Prop} {b : β}, (Filter.Eventually.{u2} β (fun (x : β) => p x) (nhds.{u2} β _inst_2 b)) -> (forall (a : α), Filter.Eventually.{max u1 u2} (Prod.{u1, u2} α β) (fun (x : Prod.{u1, u2} α β) => p (Prod.snd.{u1, u2} α β x)) (nhds.{max u1 u2} (Prod.{u1, u2} α β) (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) (Prod.mk.{u1, u2} α β a b)))
Case conversion may be inaccurate. Consider using '#align filter.eventually.prod_inr_nhds Filter.Eventually.prod_inr_nhdsₓ'. -/
theorem Filter.Eventually.prod_inr_nhds {p : β → Prop} {b : β} (h : ∀ᶠ x in 𝓝 b, p x) (a : α) :
    ∀ᶠ x in 𝓝 (a, b), p (x : α × β).2 :=
  continuousAt_snd h
#align filter.eventually.prod_inr_nhds Filter.Eventually.prod_inr_nhds

/- warning: filter.eventually.prod_mk_nhds -> Filter.Eventually.prod_mk_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {pa : α -> Prop} {a : α}, (Filter.Eventually.{u1} α (fun (x : α) => pa x) (nhds.{u1} α _inst_1 a)) -> (forall {pb : β -> Prop} {b : β}, (Filter.Eventually.{u2} β (fun (y : β) => pb y) (nhds.{u2} β _inst_2 b)) -> (Filter.Eventually.{max u1 u2} (Prod.{u1, u2} α β) (fun (p : Prod.{u1, u2} α β) => And (pa (Prod.fst.{u1, u2} α β p)) (pb (Prod.snd.{u1, u2} α β p))) (nhds.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Prod.mk.{u1, u2} α β a b))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {pa : α -> Prop} {a : α}, (Filter.Eventually.{u1} α (fun (x : α) => pa x) (nhds.{u1} α _inst_1 a)) -> (forall {pb : β -> Prop} {b : β}, (Filter.Eventually.{u2} β (fun (y : β) => pb y) (nhds.{u2} β _inst_2 b)) -> (Filter.Eventually.{max u1 u2} (Prod.{u1, u2} α β) (fun (p : Prod.{u1, u2} α β) => And (pa (Prod.fst.{u1, u2} α β p)) (pb (Prod.snd.{u1, u2} α β p))) (nhds.{max u1 u2} (Prod.{u1, u2} α β) (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) (Prod.mk.{u1, u2} α β a b))))
Case conversion may be inaccurate. Consider using '#align filter.eventually.prod_mk_nhds Filter.Eventually.prod_mk_nhdsₓ'. -/
theorem Filter.Eventually.prod_mk_nhds {pa : α → Prop} {a} (ha : ∀ᶠ x in 𝓝 a, pa x) {pb : β → Prop}
    {b} (hb : ∀ᶠ y in 𝓝 b, pb y) : ∀ᶠ p in 𝓝 (a, b), pa (p : α × β).1 ∧ pb p.2 :=
  (ha.prod_inl_nhds b).And (hb.prod_inr_nhds a)
#align filter.eventually.prod_mk_nhds Filter.Eventually.prod_mk_nhds

/- warning: continuous_swap -> continuous_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], Continuous.{max u1 u2, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u2, u1} β α) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Prod.topologicalSpace.{u2, u1} β α _inst_2 _inst_1) (Prod.swap.{u1, u2} α β)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], Continuous.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u2, u1} β α) (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) (instTopologicalSpaceProd.{u2, u1} β α _inst_2 _inst_1) (Prod.swap.{u1, u2} α β)
Case conversion may be inaccurate. Consider using '#align continuous_swap continuous_swapₓ'. -/
theorem continuous_swap : Continuous (Prod.swap : α × β → β × α) :=
  continuous_snd.prod_mk continuous_fst
#align continuous_swap continuous_swap

/- warning: continuous_uncurry_left -> continuous_uncurry_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {f : α -> β -> γ} (a : α), (Continuous.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3 (Function.uncurry.{u1, u2, u3} α β γ f)) -> (Continuous.{u2, u3} β γ _inst_2 _inst_3 (f a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u1} γ] {f : α -> β -> γ} (a : α), (Continuous.{max u3 u2, u1} (Prod.{u2, u3} α β) γ (instTopologicalSpaceProd.{u2, u3} α β _inst_1 _inst_2) _inst_3 (Function.uncurry.{u2, u3, u1} α β γ f)) -> (Continuous.{u3, u1} β γ _inst_2 _inst_3 (f a))
Case conversion may be inaccurate. Consider using '#align continuous_uncurry_left continuous_uncurry_leftₓ'. -/
theorem continuous_uncurry_left {f : α → β → γ} (a : α) (h : Continuous (uncurry f)) :
    Continuous (f a) :=
  show Continuous (uncurry f ∘ fun b => (a, b)) from h.comp (by continuity)
#align continuous_uncurry_left continuous_uncurry_left

/- warning: continuous_uncurry_right -> continuous_uncurry_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {f : α -> β -> γ} (b : β), (Continuous.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3 (Function.uncurry.{u1, u2, u3} α β γ f)) -> (Continuous.{u1, u3} α γ _inst_1 _inst_3 (fun (a : α) => f a b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u1} γ] {f : α -> β -> γ} (b : β), (Continuous.{max u3 u2, u1} (Prod.{u2, u3} α β) γ (instTopologicalSpaceProd.{u2, u3} α β _inst_1 _inst_2) _inst_3 (Function.uncurry.{u2, u3, u1} α β γ f)) -> (Continuous.{u2, u1} α γ _inst_1 _inst_3 (fun (a : α) => f a b))
Case conversion may be inaccurate. Consider using '#align continuous_uncurry_right continuous_uncurry_rightₓ'. -/
theorem continuous_uncurry_right {f : α → β → γ} (b : β) (h : Continuous (uncurry f)) :
    Continuous fun a => f a b :=
  show Continuous (uncurry f ∘ fun a => (a, b)) from h.comp (by continuity)
#align continuous_uncurry_right continuous_uncurry_right

/- warning: continuous_curry -> continuous_curry is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {g : (Prod.{u1, u2} α β) -> γ} (a : α), (Continuous.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3 g) -> (Continuous.{u2, u3} β γ _inst_2 _inst_3 (Function.curry.{u1, u2, u3} α β γ g a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u1} γ] {g : (Prod.{u2, u3} α β) -> γ} (a : α), (Continuous.{max u2 u3, u1} (Prod.{u2, u3} α β) γ (instTopologicalSpaceProd.{u2, u3} α β _inst_1 _inst_2) _inst_3 g) -> (Continuous.{u3, u1} β γ _inst_2 _inst_3 (Function.curry.{u2, u3, u1} α β γ g a))
Case conversion may be inaccurate. Consider using '#align continuous_curry continuous_curryₓ'. -/
theorem continuous_curry {g : α × β → γ} (a : α) (h : Continuous g) : Continuous (curry g a) :=
  show Continuous (g ∘ fun b => (a, b)) from h.comp (by continuity)
#align continuous_curry continuous_curry

/- warning: is_open.prod -> IsOpen.prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{u1} α} {t : Set.{u2} β}, (IsOpen.{u1} α _inst_1 s) -> (IsOpen.{u2} β _inst_2 t) -> (IsOpen.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Set.prod.{u1, u2} α β s t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{u1} α} {t : Set.{u2} β}, (IsOpen.{u1} α _inst_1 s) -> (IsOpen.{u2} β _inst_2 t) -> (IsOpen.{max u2 u1} (Prod.{u1, u2} α β) (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) (Set.prod.{u1, u2} α β s t))
Case conversion may be inaccurate. Consider using '#align is_open.prod IsOpen.prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem IsOpen.prod {s : Set α} {t : Set β} (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ×ˢ t) :=
  (hs.Preimage continuous_fst).inter (ht.Preimage continuous_snd)
#align is_open.prod IsOpen.prod

/- warning: nhds_prod_eq -> nhds_prod_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {a : α} {b : β}, Eq.{succ (max u1 u2)} (Filter.{max u1 u2} (Prod.{u1, u2} α β)) (nhds.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Prod.mk.{u1, u2} α β a b)) (Filter.prod.{u1, u2} α β (nhds.{u1} α _inst_1 a) (nhds.{u2} β _inst_2 b))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {a : α} {b : β}, Eq.{max (succ u1) (succ u2)} (Filter.{max u2 u1} (Prod.{u1, u2} α β)) (nhds.{max u2 u1} (Prod.{u1, u2} α β) (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) (Prod.mk.{u1, u2} α β a b)) (Filter.prod.{u1, u2} α β (nhds.{u1} α _inst_1 a) (nhds.{u2} β _inst_2 b))
Case conversion may be inaccurate. Consider using '#align nhds_prod_eq nhds_prod_eqₓ'. -/
theorem nhds_prod_eq {a : α} {b : β} : 𝓝 (a, b) = 𝓝 a ×ᶠ 𝓝 b := by
  rw [Filter.prod, Prod.topologicalSpace, nhds_inf, nhds_induced, nhds_induced]
#align nhds_prod_eq nhds_prod_eq

/- warning: continuous_uncurry_of_discrete_topology -> continuous_uncurry_of_discreteTopology is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_7 : DiscreteTopology.{u1} α _inst_1] {f : α -> β -> γ}, (forall (a : α), Continuous.{u2, u3} β γ _inst_2 _inst_3 (f a)) -> (Continuous.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3 (Function.uncurry.{u1, u2, u3} α β γ f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u1} γ] [_inst_7 : DiscreteTopology.{u2} α _inst_1] {f : α -> β -> γ}, (forall (a : α), Continuous.{u3, u1} β γ _inst_2 _inst_3 (f a)) -> (Continuous.{max u3 u2, u1} (Prod.{u2, u3} α β) γ (instTopologicalSpaceProd.{u2, u3} α β _inst_1 _inst_2) _inst_3 (Function.uncurry.{u2, u3, u1} α β γ f))
Case conversion may be inaccurate. Consider using '#align continuous_uncurry_of_discrete_topology continuous_uncurry_of_discreteTopologyₓ'. -/
/-- If a function `f x y` is such that `y ↦ f x y` is continuous for all `x`, and `x` lives in a
discrete space, then `f` is continuous. -/
theorem continuous_uncurry_of_discreteTopology [DiscreteTopology α] {f : α → β → γ}
    (hf : ∀ a, Continuous (f a)) : Continuous (uncurry f) :=
  by
  apply continuous_iff_continuousAt.2
  rintro ⟨a, x⟩
  change map _ _ ≤ _
  rw [nhds_prod_eq, nhds_discrete, Filter.map_pure_prod]
  exact (hf a).ContinuousAt
#align continuous_uncurry_of_discrete_topology continuous_uncurry_of_discreteTopology

/- warning: mem_nhds_prod_iff -> mem_nhds_prod_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {a : α} {b : β} {s : Set.{max u1 u2} (Prod.{u1, u2} α β)}, Iff (Membership.Mem.{max u1 u2, max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Filter.{max u1 u2} (Prod.{u1, u2} α β)) (Filter.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) s (nhds.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Prod.mk.{u1, u2} α β a b))) (Exists.{succ u1} (Set.{u1} α) (fun (u : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) u (nhds.{u1} α _inst_1 a)) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) u (nhds.{u1} α _inst_1 a)) => Exists.{succ u2} (Set.{u2} β) (fun (v : Set.{u2} β) => Exists.{0} (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) v (nhds.{u2} β _inst_2 b)) (fun (H : Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) v (nhds.{u2} β _inst_2 b)) => HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.hasSubset.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β u v) s)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {a : α} {b : β} {s : Set.{max u2 u1} (Prod.{u1, u2} α β)}, Iff (Membership.mem.{max u1 u2, max u2 u1} (Set.{max u2 u1} (Prod.{u1, u2} α β)) (Filter.{max u2 u1} (Prod.{u1, u2} α β)) (instMembershipSetFilter.{max u1 u2} (Prod.{u1, u2} α β)) s (nhds.{max u2 u1} (Prod.{u1, u2} α β) (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) (Prod.mk.{u1, u2} α β a b))) (Exists.{succ u1} (Set.{u1} α) (fun (u : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) u (nhds.{u1} α _inst_1 a)) (Exists.{succ u2} (Set.{u2} β) (fun (v : Set.{u2} β) => And (Membership.mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (instMembershipSetFilter.{u2} β) v (nhds.{u2} β _inst_2 b)) (HasSubset.Subset.{max u2 u1} (Set.{max u2 u1} (Prod.{u1, u2} α β)) (Set.instHasSubsetSet.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β u v) s)))))
Case conversion may be inaccurate. Consider using '#align mem_nhds_prod_iff mem_nhds_prod_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem mem_nhds_prod_iff {a : α} {b : β} {s : Set (α × β)} :
    s ∈ 𝓝 (a, b) ↔ ∃ u ∈ 𝓝 a, ∃ v ∈ 𝓝 b, u ×ˢ v ⊆ s := by rw [nhds_prod_eq, mem_prod_iff]
#align mem_nhds_prod_iff mem_nhds_prod_iff

/- warning: mem_nhds_prod_iff' -> mem_nhds_prod_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {a : α} {b : β} {s : Set.{max u1 u2} (Prod.{u1, u2} α β)}, Iff (Membership.Mem.{max u1 u2, max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Filter.{max u1 u2} (Prod.{u1, u2} α β)) (Filter.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) s (nhds.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Prod.mk.{u1, u2} α β a b))) (Exists.{succ u1} (Set.{u1} α) (fun (u : Set.{u1} α) => Exists.{succ u2} (Set.{u2} β) (fun (v : Set.{u2} β) => And (IsOpen.{u1} α _inst_1 u) (And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a u) (And (IsOpen.{u2} β _inst_2 v) (And (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b v) (HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.hasSubset.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β u v) s)))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {a : α} {b : β} {s : Set.{max u2 u1} (Prod.{u1, u2} α β)}, Iff (Membership.mem.{max u1 u2, max u2 u1} (Set.{max u2 u1} (Prod.{u1, u2} α β)) (Filter.{max u2 u1} (Prod.{u1, u2} α β)) (instMembershipSetFilter.{max u1 u2} (Prod.{u1, u2} α β)) s (nhds.{max u2 u1} (Prod.{u1, u2} α β) (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) (Prod.mk.{u1, u2} α β a b))) (Exists.{succ u1} (Set.{u1} α) (fun (u : Set.{u1} α) => Exists.{succ u2} (Set.{u2} β) (fun (v : Set.{u2} β) => And (IsOpen.{u1} α _inst_1 u) (And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a u) (And (IsOpen.{u2} β _inst_2 v) (And (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b v) (HasSubset.Subset.{max u2 u1} (Set.{max u2 u1} (Prod.{u1, u2} α β)) (Set.instHasSubsetSet.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β u v) s)))))))
Case conversion may be inaccurate. Consider using '#align mem_nhds_prod_iff' mem_nhds_prod_iff'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem mem_nhds_prod_iff' {a : α} {b : β} {s : Set (α × β)} :
    s ∈ 𝓝 (a, b) ↔ ∃ (u : Set α)(v : Set β), IsOpen u ∧ a ∈ u ∧ IsOpen v ∧ b ∈ v ∧ u ×ˢ v ⊆ s :=
  by
  rw [mem_nhds_prod_iff]
  constructor
  · rintro ⟨u, Hu, v, Hv, h⟩
    rcases mem_nhds_iff.1 Hu with ⟨u', u'u, u'_open, Hu'⟩
    rcases mem_nhds_iff.1 Hv with ⟨v', v'v, v'_open, Hv'⟩
    exact ⟨u', v', u'_open, Hu', v'_open, Hv', (Set.prod_mono u'u v'v).trans h⟩
  · rintro ⟨u, v, u_open, au, v_open, bv, huv⟩
    exact ⟨u, u_open.mem_nhds au, v, v_open.mem_nhds bv, huv⟩
#align mem_nhds_prod_iff' mem_nhds_prod_iff'

/- warning: prod.tendsto_iff -> Prod.tendsto_iff is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {γ : Type.{u2}} [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : TopologicalSpace.{u2} γ] {α : Type.{u3}} (seq : α -> (Prod.{u1, u2} β γ)) {f : Filter.{u3} α} (x : Prod.{u1, u2} β γ), Iff (Filter.Tendsto.{u3, max u1 u2} α (Prod.{u1, u2} β γ) seq f (nhds.{max u1 u2} (Prod.{u1, u2} β γ) (Prod.topologicalSpace.{u1, u2} β γ _inst_2 _inst_3) x)) (And (Filter.Tendsto.{u3, u1} α β (fun (n : α) => Prod.fst.{u1, u2} β γ (seq n)) f (nhds.{u1} β _inst_2 (Prod.fst.{u1, u2} β γ x))) (Filter.Tendsto.{u3, u2} α γ (fun (n : α) => Prod.snd.{u1, u2} β γ (seq n)) f (nhds.{u2} γ _inst_3 (Prod.snd.{u1, u2} β γ x))))
but is expected to have type
  forall {β : Type.{u3}} {γ : Type.{u1}} [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u1} γ] {α : Type.{u2}} (seq : α -> (Prod.{u3, u1} β γ)) {f : Filter.{u2} α} (x : Prod.{u3, u1} β γ), Iff (Filter.Tendsto.{u2, max u3 u1} α (Prod.{u3, u1} β γ) seq f (nhds.{max u3 u1} (Prod.{u3, u1} β γ) (instTopologicalSpaceProd.{u3, u1} β γ _inst_2 _inst_3) x)) (And (Filter.Tendsto.{u2, u3} α β (fun (n : α) => Prod.fst.{u3, u1} β γ (seq n)) f (nhds.{u3} β _inst_2 (Prod.fst.{u3, u1} β γ x))) (Filter.Tendsto.{u2, u1} α γ (fun (n : α) => Prod.snd.{u3, u1} β γ (seq n)) f (nhds.{u1} γ _inst_3 (Prod.snd.{u3, u1} β γ x))))
Case conversion may be inaccurate. Consider using '#align prod.tendsto_iff Prod.tendsto_iffₓ'. -/
theorem Prod.tendsto_iff {α} (seq : α → β × γ) {f : Filter α} (x : β × γ) :
    Tendsto seq f (𝓝 x) ↔
      Tendsto (fun n => (seq n).fst) f (𝓝 x.fst) ∧ Tendsto (fun n => (seq n).snd) f (𝓝 x.snd) :=
  by
  cases x
  rw [nhds_prod_eq, Filter.tendsto_prod_iff']
#align prod.tendsto_iff Prod.tendsto_iff

/- warning: filter.has_basis.prod_nhds -> Filter.HasBasis.prod_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {ιa : Type.{u3}} {ιb : Type.{u4}} {pa : ιa -> Prop} {pb : ιb -> Prop} {sa : ιa -> (Set.{u1} α)} {sb : ιb -> (Set.{u2} β)} {a : α} {b : β}, (Filter.HasBasis.{u1, succ u3} α ιa (nhds.{u1} α _inst_1 a) pa sa) -> (Filter.HasBasis.{u2, succ u4} β ιb (nhds.{u2} β _inst_2 b) pb sb) -> (Filter.HasBasis.{max u1 u2, max (succ u3) (succ u4)} (Prod.{u1, u2} α β) (Prod.{u3, u4} ιa ιb) (nhds.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Prod.mk.{u1, u2} α β a b)) (fun (i : Prod.{u3, u4} ιa ιb) => And (pa (Prod.fst.{u3, u4} ιa ιb i)) (pb (Prod.snd.{u3, u4} ιa ιb i))) (fun (i : Prod.{u3, u4} ιa ιb) => Set.prod.{u1, u2} α β (sa (Prod.fst.{u3, u4} ιa ιb i)) (sb (Prod.snd.{u3, u4} ιa ιb i))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u4} β] {ιa : Type.{u2}} {ιb : Type.{u1}} {pa : ιa -> Prop} {pb : ιb -> Prop} {sa : ιa -> (Set.{u3} α)} {sb : ιb -> (Set.{u4} β)} {a : α} {b : β}, (Filter.HasBasis.{u3, succ u2} α ιa (nhds.{u3} α _inst_1 a) pa sa) -> (Filter.HasBasis.{u4, succ u1} β ιb (nhds.{u4} β _inst_2 b) pb sb) -> (Filter.HasBasis.{max u3 u4, max (succ u2) (succ u1)} (Prod.{u3, u4} α β) (Prod.{u2, u1} ιa ιb) (nhds.{max u4 u3} (Prod.{u3, u4} α β) (instTopologicalSpaceProd.{u3, u4} α β _inst_1 _inst_2) (Prod.mk.{u3, u4} α β a b)) (fun (i : Prod.{u2, u1} ιa ιb) => And (pa (Prod.fst.{u2, u1} ιa ιb i)) (pb (Prod.snd.{u2, u1} ιa ιb i))) (fun (i : Prod.{u2, u1} ιa ιb) => Set.prod.{u3, u4} α β (sa (Prod.fst.{u2, u1} ιa ιb i)) (sb (Prod.snd.{u2, u1} ιa ιb i))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.prod_nhds Filter.HasBasis.prod_nhdsₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Filter.HasBasis.prod_nhds {ιa ιb : Type _} {pa : ιa → Prop} {pb : ιb → Prop}
    {sa : ιa → Set α} {sb : ιb → Set β} {a : α} {b : β} (ha : (𝓝 a).HasBasis pa sa)
    (hb : (𝓝 b).HasBasis pb sb) :
    (𝓝 (a, b)).HasBasis (fun i : ιa × ιb => pa i.1 ∧ pb i.2) fun i => sa i.1 ×ˢ sb i.2 :=
  by
  rw [nhds_prod_eq]
  exact ha.prod hb
#align filter.has_basis.prod_nhds Filter.HasBasis.prod_nhds

/- warning: filter.has_basis.prod_nhds' -> Filter.HasBasis.prod_nhds' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {ιa : Type.{u3}} {ιb : Type.{u4}} {pa : ιa -> Prop} {pb : ιb -> Prop} {sa : ιa -> (Set.{u1} α)} {sb : ιb -> (Set.{u2} β)} {ab : Prod.{u1, u2} α β}, (Filter.HasBasis.{u1, succ u3} α ιa (nhds.{u1} α _inst_1 (Prod.fst.{u1, u2} α β ab)) pa sa) -> (Filter.HasBasis.{u2, succ u4} β ιb (nhds.{u2} β _inst_2 (Prod.snd.{u1, u2} α β ab)) pb sb) -> (Filter.HasBasis.{max u1 u2, max (succ u3) (succ u4)} (Prod.{u1, u2} α β) (Prod.{u3, u4} ιa ιb) (nhds.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) ab) (fun (i : Prod.{u3, u4} ιa ιb) => And (pa (Prod.fst.{u3, u4} ιa ιb i)) (pb (Prod.snd.{u3, u4} ιa ιb i))) (fun (i : Prod.{u3, u4} ιa ιb) => Set.prod.{u1, u2} α β (sa (Prod.fst.{u3, u4} ιa ιb i)) (sb (Prod.snd.{u3, u4} ιa ιb i))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u4} β] {ιa : Type.{u2}} {ιb : Type.{u1}} {pa : ιa -> Prop} {pb : ιb -> Prop} {sa : ιa -> (Set.{u3} α)} {sb : ιb -> (Set.{u4} β)} {ab : Prod.{u3, u4} α β}, (Filter.HasBasis.{u3, succ u2} α ιa (nhds.{u3} α _inst_1 (Prod.fst.{u3, u4} α β ab)) pa sa) -> (Filter.HasBasis.{u4, succ u1} β ιb (nhds.{u4} β _inst_2 (Prod.snd.{u3, u4} α β ab)) pb sb) -> (Filter.HasBasis.{max u3 u4, max (succ u2) (succ u1)} (Prod.{u3, u4} α β) (Prod.{u2, u1} ιa ιb) (nhds.{max u3 u4} (Prod.{u3, u4} α β) (instTopologicalSpaceProd.{u3, u4} α β _inst_1 _inst_2) ab) (fun (i : Prod.{u2, u1} ιa ιb) => And (pa (Prod.fst.{u2, u1} ιa ιb i)) (pb (Prod.snd.{u2, u1} ιa ιb i))) (fun (i : Prod.{u2, u1} ιa ιb) => Set.prod.{u3, u4} α β (sa (Prod.fst.{u2, u1} ιa ιb i)) (sb (Prod.snd.{u2, u1} ιa ιb i))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.prod_nhds' Filter.HasBasis.prod_nhds'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Filter.HasBasis.prod_nhds' {ιa ιb : Type _} {pa : ιa → Prop} {pb : ιb → Prop}
    {sa : ιa → Set α} {sb : ιb → Set β} {ab : α × β} (ha : (𝓝 ab.1).HasBasis pa sa)
    (hb : (𝓝 ab.2).HasBasis pb sb) :
    (𝓝 ab).HasBasis (fun i : ιa × ιb => pa i.1 ∧ pb i.2) fun i => sa i.1 ×ˢ sb i.2 :=
  by
  cases ab
  exact ha.prod_nhds hb
#align filter.has_basis.prod_nhds' Filter.HasBasis.prod_nhds'

instance [DiscreteTopology α] [DiscreteTopology β] : DiscreteTopology (α × β) :=
  discreteTopology_iff_nhds.2 fun ⟨a, b⟩ => by
    rw [nhds_prod_eq, nhds_discrete α, nhds_discrete β, Filter.prod_pure_pure]

/- warning: prod_mem_nhds_iff -> prod_mem_nhds_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{u1} α} {t : Set.{u2} β} {a : α} {b : β}, Iff (Membership.Mem.{max u1 u2, max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Filter.{max u1 u2} (Prod.{u1, u2} α β)) (Filter.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β s t) (nhds.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Prod.mk.{u1, u2} α β a b))) (And (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (nhds.{u1} α _inst_1 a)) (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) t (nhds.{u2} β _inst_2 b)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{u1} α} {t : Set.{u2} β} {a : α} {b : β}, Iff (Membership.mem.{max u2 u1, max u2 u1} (Set.{max u2 u1} (Prod.{u1, u2} α β)) (Filter.{max u2 u1} (Prod.{u1, u2} α β)) (instMembershipSetFilter.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β s t) (nhds.{max u2 u1} (Prod.{u1, u2} α β) (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) (Prod.mk.{u1, u2} α β a b))) (And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (nhds.{u1} α _inst_1 a)) (Membership.mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (instMembershipSetFilter.{u2} β) t (nhds.{u2} β _inst_2 b)))
Case conversion may be inaccurate. Consider using '#align prod_mem_nhds_iff prod_mem_nhds_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_mem_nhds_iff {s : Set α} {t : Set β} {a : α} {b : β} :
    s ×ˢ t ∈ 𝓝 (a, b) ↔ s ∈ 𝓝 a ∧ t ∈ 𝓝 b := by rw [nhds_prod_eq, prod_mem_prod_iff]
#align prod_mem_nhds_iff prod_mem_nhds_iff

/- warning: prod_mem_nhds -> prod_mem_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{u1} α} {t : Set.{u2} β} {a : α} {b : β}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (nhds.{u1} α _inst_1 a)) -> (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) t (nhds.{u2} β _inst_2 b)) -> (Membership.Mem.{max u1 u2, max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Filter.{max u1 u2} (Prod.{u1, u2} α β)) (Filter.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β s t) (nhds.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Prod.mk.{u1, u2} α β a b)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{u1} α} {t : Set.{u2} β} {a : α} {b : β}, (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (nhds.{u1} α _inst_1 a)) -> (Membership.mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (instMembershipSetFilter.{u2} β) t (nhds.{u2} β _inst_2 b)) -> (Membership.mem.{max u2 u1, max u2 u1} (Set.{max u2 u1} (Prod.{u1, u2} α β)) (Filter.{max u2 u1} (Prod.{u1, u2} α β)) (instMembershipSetFilter.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β s t) (nhds.{max u2 u1} (Prod.{u1, u2} α β) (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) (Prod.mk.{u1, u2} α β a b)))
Case conversion may be inaccurate. Consider using '#align prod_mem_nhds prod_mem_nhdsₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_mem_nhds {s : Set α} {t : Set β} {a : α} {b : β} (ha : s ∈ 𝓝 a) (hb : t ∈ 𝓝 b) :
    s ×ˢ t ∈ 𝓝 (a, b) :=
  prod_mem_nhds_iff.2 ⟨ha, hb⟩
#align prod_mem_nhds prod_mem_nhds

/- warning: filter.eventually.prod_nhds -> Filter.Eventually.prod_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {p : α -> Prop} {q : β -> Prop} {a : α} {b : β}, (Filter.Eventually.{u1} α (fun (x : α) => p x) (nhds.{u1} α _inst_1 a)) -> (Filter.Eventually.{u2} β (fun (y : β) => q y) (nhds.{u2} β _inst_2 b)) -> (Filter.Eventually.{max u1 u2} (Prod.{u1, u2} α β) (fun (z : Prod.{u1, u2} α β) => And (p (Prod.fst.{u1, u2} α β z)) (q (Prod.snd.{u1, u2} α β z))) (nhds.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Prod.mk.{u1, u2} α β a b)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {p : α -> Prop} {q : β -> Prop} {a : α} {b : β}, (Filter.Eventually.{u1} α (fun (x : α) => p x) (nhds.{u1} α _inst_1 a)) -> (Filter.Eventually.{u2} β (fun (y : β) => q y) (nhds.{u2} β _inst_2 b)) -> (Filter.Eventually.{max u1 u2} (Prod.{u1, u2} α β) (fun (z : Prod.{u1, u2} α β) => And (p (Prod.fst.{u1, u2} α β z)) (q (Prod.snd.{u1, u2} α β z))) (nhds.{max u1 u2} (Prod.{u1, u2} α β) (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) (Prod.mk.{u1, u2} α β a b)))
Case conversion may be inaccurate. Consider using '#align filter.eventually.prod_nhds Filter.Eventually.prod_nhdsₓ'. -/
theorem Filter.Eventually.prod_nhds {p : α → Prop} {q : β → Prop} {a : α} {b : β}
    (ha : ∀ᶠ x in 𝓝 a, p x) (hb : ∀ᶠ y in 𝓝 b, q y) : ∀ᶠ z : α × β in 𝓝 (a, b), p z.1 ∧ q z.2 :=
  prod_mem_nhds ha hb
#align filter.eventually.prod_nhds Filter.Eventually.prod_nhds

/- warning: nhds_swap -> nhds_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (a : α) (b : β), Eq.{succ (max u1 u2)} (Filter.{max u1 u2} (Prod.{u1, u2} α β)) (nhds.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Prod.mk.{u1, u2} α β a b)) (Filter.map.{max u2 u1, max u1 u2} (Prod.{u2, u1} β α) (Prod.{u1, u2} α β) (Prod.swap.{u2, u1} β α) (nhds.{max u2 u1} (Prod.{u2, u1} β α) (Prod.topologicalSpace.{u2, u1} β α _inst_2 _inst_1) (Prod.mk.{u2, u1} β α b a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (a : α) (b : β), Eq.{max (succ u1) (succ u2)} (Filter.{max u2 u1} (Prod.{u1, u2} α β)) (nhds.{max u2 u1} (Prod.{u1, u2} α β) (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) (Prod.mk.{u1, u2} α β a b)) (Filter.map.{max u1 u2, max u1 u2} (Prod.{u2, u1} β α) (Prod.{u1, u2} α β) (Prod.swap.{u2, u1} β α) (nhds.{max u1 u2} (Prod.{u2, u1} β α) (instTopologicalSpaceProd.{u2, u1} β α _inst_2 _inst_1) (Prod.mk.{u2, u1} β α b a)))
Case conversion may be inaccurate. Consider using '#align nhds_swap nhds_swapₓ'. -/
theorem nhds_swap (a : α) (b : β) : 𝓝 (a, b) = (𝓝 (b, a)).map Prod.swap := by
  rw [nhds_prod_eq, Filter.prod_comm, nhds_prod_eq] <;> rfl
#align nhds_swap nhds_swap

/- warning: filter.tendsto.prod_mk_nhds -> Filter.Tendsto.prod_mk_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {γ : Type.{u3}} {a : α} {b : β} {f : Filter.{u3} γ} {ma : γ -> α} {mb : γ -> β}, (Filter.Tendsto.{u3, u1} γ α ma f (nhds.{u1} α _inst_1 a)) -> (Filter.Tendsto.{u3, u2} γ β mb f (nhds.{u2} β _inst_2 b)) -> (Filter.Tendsto.{u3, max u1 u2} γ (Prod.{u1, u2} α β) (fun (c : γ) => Prod.mk.{u1, u2} α β (ma c) (mb c)) f (nhds.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Prod.mk.{u1, u2} α β a b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] {γ : Type.{u1}} {a : α} {b : β} {f : Filter.{u1} γ} {ma : γ -> α} {mb : γ -> β}, (Filter.Tendsto.{u1, u2} γ α ma f (nhds.{u2} α _inst_1 a)) -> (Filter.Tendsto.{u1, u3} γ β mb f (nhds.{u3} β _inst_2 b)) -> (Filter.Tendsto.{u1, max u3 u2} γ (Prod.{u2, u3} α β) (fun (c : γ) => Prod.mk.{u2, u3} α β (ma c) (mb c)) f (nhds.{max u2 u3} (Prod.{u2, u3} α β) (instTopologicalSpaceProd.{u2, u3} α β _inst_1 _inst_2) (Prod.mk.{u2, u3} α β a b)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.prod_mk_nhds Filter.Tendsto.prod_mk_nhdsₓ'. -/
theorem Filter.Tendsto.prod_mk_nhds {γ} {a : α} {b : β} {f : Filter γ} {ma : γ → α} {mb : γ → β}
    (ha : Tendsto ma f (𝓝 a)) (hb : Tendsto mb f (𝓝 b)) :
    Tendsto (fun c => (ma c, mb c)) f (𝓝 (a, b)) := by
  rw [nhds_prod_eq] <;> exact Filter.Tendsto.prod_mk ha hb
#align filter.tendsto.prod_mk_nhds Filter.Tendsto.prod_mk_nhds

/- warning: filter.eventually.curry_nhds -> Filter.Eventually.curry_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {p : (Prod.{u1, u2} α β) -> Prop} {x : α} {y : β}, (Filter.Eventually.{max u1 u2} (Prod.{u1, u2} α β) (fun (x : Prod.{u1, u2} α β) => p x) (nhds.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Prod.mk.{u1, u2} α β x y))) -> (Filter.Eventually.{u1} α (fun (x' : α) => Filter.Eventually.{u2} β (fun (y' : β) => p (Prod.mk.{u1, u2} α β x' y')) (nhds.{u2} β _inst_2 y)) (nhds.{u1} α _inst_1 x))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {p : (Prod.{u1, u2} α β) -> Prop} {x : α} {y : β}, (Filter.Eventually.{max u1 u2} (Prod.{u1, u2} α β) (fun (x : Prod.{u1, u2} α β) => p x) (nhds.{max u1 u2} (Prod.{u1, u2} α β) (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) (Prod.mk.{u1, u2} α β x y))) -> (Filter.Eventually.{u1} α (fun (x' : α) => Filter.Eventually.{u2} β (fun (y' : β) => p (Prod.mk.{u1, u2} α β x' y')) (nhds.{u2} β _inst_2 y)) (nhds.{u1} α _inst_1 x))
Case conversion may be inaccurate. Consider using '#align filter.eventually.curry_nhds Filter.Eventually.curry_nhdsₓ'. -/
theorem Filter.Eventually.curry_nhds {p : α × β → Prop} {x : α} {y : β}
    (h : ∀ᶠ x in 𝓝 (x, y), p x) : ∀ᶠ x' in 𝓝 x, ∀ᶠ y' in 𝓝 y, p (x', y') :=
  by
  rw [nhds_prod_eq] at h
  exact h.curry
#align filter.eventually.curry_nhds Filter.Eventually.curry_nhds

/- warning: continuous_at.prod -> ContinuousAt.prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {f : α -> β} {g : α -> γ} {x : α}, (ContinuousAt.{u1, u2} α β _inst_1 _inst_2 f x) -> (ContinuousAt.{u1, u3} α γ _inst_1 _inst_3 g x) -> (ContinuousAt.{u1, max u2 u3} α (Prod.{u2, u3} β γ) _inst_1 (Prod.topologicalSpace.{u2, u3} β γ _inst_2 _inst_3) (fun (x : α) => Prod.mk.{u2, u3} β γ (f x) (g x)) x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u1} γ] {f : α -> β} {g : α -> γ} {x : α}, (ContinuousAt.{u2, u3} α β _inst_1 _inst_2 f x) -> (ContinuousAt.{u2, u1} α γ _inst_1 _inst_3 g x) -> (ContinuousAt.{u2, max u1 u3} α (Prod.{u3, u1} β γ) _inst_1 (instTopologicalSpaceProd.{u3, u1} β γ _inst_2 _inst_3) (fun (x : α) => Prod.mk.{u3, u1} β γ (f x) (g x)) x)
Case conversion may be inaccurate. Consider using '#align continuous_at.prod ContinuousAt.prodₓ'. -/
theorem ContinuousAt.prod {f : α → β} {g : α → γ} {x : α} (hf : ContinuousAt f x)
    (hg : ContinuousAt g x) : ContinuousAt (fun x => (f x, g x)) x :=
  hf.prod_mk_nhds hg
#align continuous_at.prod ContinuousAt.prod

/- warning: continuous_at.prod_map -> ContinuousAt.prod_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] {f : α -> γ} {g : β -> δ} {p : Prod.{u1, u2} α β}, (ContinuousAt.{u1, u3} α γ _inst_1 _inst_3 f (Prod.fst.{u1, u2} α β p)) -> (ContinuousAt.{u2, u4} β δ _inst_2 _inst_4 g (Prod.snd.{u1, u2} α β p)) -> (ContinuousAt.{max u1 u2, max u3 u4} (Prod.{u1, u2} α β) (Prod.{u3, u4} γ δ) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Prod.topologicalSpace.{u3, u4} γ δ _inst_3 _inst_4) (fun (p : Prod.{u1, u2} α β) => Prod.mk.{u3, u4} γ δ (f (Prod.fst.{u1, u2} α β p)) (g (Prod.snd.{u1, u2} α β p))) p)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {γ : Type.{u2}} {δ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u4} β] [_inst_3 : TopologicalSpace.{u2} γ] [_inst_4 : TopologicalSpace.{u1} δ] {f : α -> γ} {g : β -> δ} {p : Prod.{u3, u4} α β}, (ContinuousAt.{u3, u2} α γ _inst_1 _inst_3 f (Prod.fst.{u3, u4} α β p)) -> (ContinuousAt.{u4, u1} β δ _inst_2 _inst_4 g (Prod.snd.{u3, u4} α β p)) -> (ContinuousAt.{max u3 u4, max u1 u2} (Prod.{u3, u4} α β) (Prod.{u2, u1} γ δ) (instTopologicalSpaceProd.{u3, u4} α β _inst_1 _inst_2) (instTopologicalSpaceProd.{u2, u1} γ δ _inst_3 _inst_4) (fun (p : Prod.{u3, u4} α β) => Prod.mk.{u2, u1} γ δ (f (Prod.fst.{u3, u4} α β p)) (g (Prod.snd.{u3, u4} α β p))) p)
Case conversion may be inaccurate. Consider using '#align continuous_at.prod_map ContinuousAt.prod_mapₓ'. -/
theorem ContinuousAt.prod_map {f : α → γ} {g : β → δ} {p : α × β} (hf : ContinuousAt f p.fst)
    (hg : ContinuousAt g p.snd) : ContinuousAt (fun p : α × β => (f p.1, g p.2)) p :=
  hf.fst''.Prod hg.snd''
#align continuous_at.prod_map ContinuousAt.prod_map

/- warning: continuous_at.prod_map' -> ContinuousAt.prod_map' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] {f : α -> γ} {g : β -> δ} {x : α} {y : β}, (ContinuousAt.{u1, u3} α γ _inst_1 _inst_3 f x) -> (ContinuousAt.{u2, u4} β δ _inst_2 _inst_4 g y) -> (ContinuousAt.{max u1 u2, max u3 u4} (Prod.{u1, u2} α β) (Prod.{u3, u4} γ δ) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Prod.topologicalSpace.{u3, u4} γ δ _inst_3 _inst_4) (fun (p : Prod.{u1, u2} α β) => Prod.mk.{u3, u4} γ δ (f (Prod.fst.{u1, u2} α β p)) (g (Prod.snd.{u1, u2} α β p))) (Prod.mk.{u1, u2} α β x y))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {γ : Type.{u2}} {δ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u4} β] [_inst_3 : TopologicalSpace.{u2} γ] [_inst_4 : TopologicalSpace.{u1} δ] {f : α -> γ} {g : β -> δ} {x : α} {y : β}, (ContinuousAt.{u3, u2} α γ _inst_1 _inst_3 f x) -> (ContinuousAt.{u4, u1} β δ _inst_2 _inst_4 g y) -> (ContinuousAt.{max u3 u4, max u1 u2} (Prod.{u3, u4} α β) (Prod.{u2, u1} γ δ) (instTopologicalSpaceProd.{u3, u4} α β _inst_1 _inst_2) (instTopologicalSpaceProd.{u2, u1} γ δ _inst_3 _inst_4) (fun (p : Prod.{u3, u4} α β) => Prod.mk.{u2, u1} γ δ (f (Prod.fst.{u3, u4} α β p)) (g (Prod.snd.{u3, u4} α β p))) (Prod.mk.{u3, u4} α β x y))
Case conversion may be inaccurate. Consider using '#align continuous_at.prod_map' ContinuousAt.prod_map'ₓ'. -/
theorem ContinuousAt.prod_map' {f : α → γ} {g : β → δ} {x : α} {y : β} (hf : ContinuousAt f x)
    (hg : ContinuousAt g y) : ContinuousAt (fun p : α × β => (f p.1, g p.2)) (x, y) :=
  hf.fst'.Prod hg.snd'
#align continuous_at.prod_map' ContinuousAt.prod_map'

/- warning: prod_generate_from_generate_from_eq -> prod_generateFrom_generateFrom_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} (Set.{u1} α)} {t : Set.{u2} (Set.{u2} β)}, (Eq.{succ u1} (Set.{u1} α) (Set.unionₛ.{u1} α s) (Set.univ.{u1} α)) -> (Eq.{succ u2} (Set.{u2} β) (Set.unionₛ.{u2} β t) (Set.univ.{u2} β)) -> (Eq.{succ (max u1 u2)} (TopologicalSpace.{max u1 u2} (Prod.{u1, u2} α β)) (Prod.topologicalSpace.{u1, u2} α β (TopologicalSpace.generateFrom.{u1} α s) (TopologicalSpace.generateFrom.{u2} β t)) (TopologicalSpace.generateFrom.{max u1 u2} (Prod.{u1, u2} α β) (setOf.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (fun (g : Set.{max u1 u2} (Prod.{u1, u2} α β)) => Exists.{succ u1} (Set.{u1} α) (fun (u : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) u s) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) u s) => Exists.{succ u2} (Set.{u2} β) (fun (v : Set.{u2} β) => Exists.{0} (Membership.Mem.{u2, u2} (Set.{u2} β) (Set.{u2} (Set.{u2} β)) (Set.hasMem.{u2} (Set.{u2} β)) v t) (fun (H : Membership.Mem.{u2, u2} (Set.{u2} β) (Set.{u2} (Set.{u2} β)) (Set.hasMem.{u2} (Set.{u2} β)) v t) => Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) g (Set.prod.{u1, u2} α β u v)))))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} (Set.{u2} α)} {t : Set.{u1} (Set.{u1} β)}, (Eq.{succ u2} (Set.{u2} α) (Set.unionₛ.{u2} α s) (Set.univ.{u2} α)) -> (Eq.{succ u1} (Set.{u1} β) (Set.unionₛ.{u1} β t) (Set.univ.{u1} β)) -> (Eq.{max (succ u2) (succ u1)} (TopologicalSpace.{max u1 u2} (Prod.{u2, u1} α β)) (instTopologicalSpaceProd.{u2, u1} α β (TopologicalSpace.generateFrom.{u2} α s) (TopologicalSpace.generateFrom.{u1} β t)) (TopologicalSpace.generateFrom.{max u2 u1} (Prod.{u2, u1} α β) (setOf.{max u2 u1} (Set.{max u2 u1} (Prod.{u2, u1} α β)) (fun (g : Set.{max u2 u1} (Prod.{u2, u1} α β)) => Exists.{succ u2} (Set.{u2} α) (fun (u : Set.{u2} α) => And (Membership.mem.{u2, u2} (Set.{u2} α) (Set.{u2} (Set.{u2} α)) (Set.instMembershipSet.{u2} (Set.{u2} α)) u s) (Exists.{succ u1} (Set.{u1} β) (fun (v : Set.{u1} β) => And (Membership.mem.{u1, u1} (Set.{u1} β) (Set.{u1} (Set.{u1} β)) (Set.instMembershipSet.{u1} (Set.{u1} β)) v t) (Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (Prod.{u2, u1} α β)) g (Set.prod.{u2, u1} α β u v)))))))))
Case conversion may be inaccurate. Consider using '#align prod_generate_from_generate_from_eq prod_generateFrom_generateFrom_eqₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_generateFrom_generateFrom_eq {α β : Type _} {s : Set (Set α)} {t : Set (Set β)}
    (hs : ⋃₀ s = univ) (ht : ⋃₀ t = univ) :
    @Prod.topologicalSpace α β (generateFrom s) (generateFrom t) =
      generateFrom { g | ∃ u ∈ s, ∃ v ∈ t, g = u ×ˢ v } :=
  let G := generateFrom { g | ∃ u ∈ s, ∃ v ∈ t, g = u ×ˢ v }
  le_antisymm
    (le_generateFrom fun g ⟨u, hu, v, hv, g_eq⟩ =>
      g_eq.symm ▸
        @IsOpen.prod _ _ (generateFrom s) (generateFrom t) _ _ (GenerateOpen.basic _ hu)
          (GenerateOpen.basic _ hv))
    (le_inf
      (coinduced_le_iff_le_induced.mp <|
        le_generateFrom fun u hu =>
          have : (⋃ v ∈ t, u ×ˢ v) = Prod.fst ⁻¹' u := by
            simp_rw [← prod_Union, ← sUnion_eq_bUnion, ht, prod_univ]
          show G.IsOpen (Prod.fst ⁻¹' u) by
            rw [← this]
            exact
              isOpen_unionᵢ fun v =>
                isOpen_unionᵢ fun hv => generate_open.basic _ ⟨_, hu, _, hv, rfl⟩)
      (coinduced_le_iff_le_induced.mp <|
        le_generateFrom fun v hv =>
          have : (⋃ u ∈ s, u ×ˢ v) = Prod.snd ⁻¹' v := by
            simp_rw [← Union_prod_const, ← sUnion_eq_bUnion, hs, univ_prod]
          show G.IsOpen (Prod.snd ⁻¹' v) by
            rw [← this]
            exact
              isOpen_unionᵢ fun u =>
                isOpen_unionᵢ fun hu => generate_open.basic _ ⟨_, hu, _, hv, rfl⟩))
#align prod_generate_from_generate_from_eq prod_generateFrom_generateFrom_eq

/- warning: prod_eq_generate_from -> prod_eq_generateFrom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], Eq.{succ (max u1 u2)} (TopologicalSpace.{max u1 u2} (Prod.{u1, u2} α β)) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (TopologicalSpace.generateFrom.{max u1 u2} (Prod.{u1, u2} α β) (setOf.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (fun (g : Set.{max u1 u2} (Prod.{u1, u2} α β)) => Exists.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => Exists.{succ u2} (Set.{u2} β) (fun (t : Set.{u2} β) => And (IsOpen.{u1} α _inst_1 s) (And (IsOpen.{u2} β _inst_2 t) (Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) g (Set.prod.{u1, u2} α β s t))))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], Eq.{max (succ u1) (succ u2)} (TopologicalSpace.{max u2 u1} (Prod.{u1, u2} α β)) (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) (TopologicalSpace.generateFrom.{max u1 u2} (Prod.{u1, u2} α β) (setOf.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (fun (g : Set.{max u1 u2} (Prod.{u1, u2} α β)) => Exists.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => Exists.{succ u2} (Set.{u2} β) (fun (t : Set.{u2} β) => And (IsOpen.{u1} α _inst_1 s) (And (IsOpen.{u2} β _inst_2 t) (Eq.{max (succ u1) (succ u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) g (Set.prod.{u1, u2} α β s t))))))))
Case conversion may be inaccurate. Consider using '#align prod_eq_generate_from prod_eq_generateFromₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_eq_generateFrom :
    Prod.topologicalSpace =
      generateFrom { g | ∃ (s : Set α)(t : Set β), IsOpen s ∧ IsOpen t ∧ g = s ×ˢ t } :=
  le_antisymm (le_generateFrom fun g ⟨s, t, hs, ht, g_eq⟩ => g_eq.symm ▸ hs.Prod ht)
    (le_inf
      (ball_image_of_ball fun t ht =>
        GenerateOpen.basic _ ⟨t, univ, by simpa [Set.prod_eq] using ht⟩)
      (ball_image_of_ball fun t ht =>
        GenerateOpen.basic _ ⟨univ, t, by simpa [Set.prod_eq] using ht⟩))
#align prod_eq_generate_from prod_eq_generateFrom

/- warning: is_open_prod_iff -> isOpen_prod_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{max u1 u2} (Prod.{u1, u2} α β)}, Iff (IsOpen.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) s) (forall (a : α) (b : β), (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) (Prod.mk.{u1, u2} α β a b) s) -> (Exists.{succ u1} (Set.{u1} α) (fun (u : Set.{u1} α) => Exists.{succ u2} (Set.{u2} β) (fun (v : Set.{u2} β) => And (IsOpen.{u1} α _inst_1 u) (And (IsOpen.{u2} β _inst_2 v) (And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a u) (And (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b v) (HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.hasSubset.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β u v) s))))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{max u2 u1} (Prod.{u1, u2} α β)}, Iff (IsOpen.{max u1 u2} (Prod.{u1, u2} α β) (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) s) (forall (a : α) (b : β), (Membership.mem.{max u2 u1, max u1 u2} (Prod.{u1, u2} α β) (Set.{max u2 u1} (Prod.{u1, u2} α β)) (Set.instMembershipSet.{max u2 u1} (Prod.{u1, u2} α β)) (Prod.mk.{u1, u2} α β a b) s) -> (Exists.{succ u1} (Set.{u1} α) (fun (u : Set.{u1} α) => Exists.{succ u2} (Set.{u2} β) (fun (v : Set.{u2} β) => And (IsOpen.{u1} α _inst_1 u) (And (IsOpen.{u2} β _inst_2 v) (And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a u) (And (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b v) (HasSubset.Subset.{max u2 u1} (Set.{max u2 u1} (Prod.{u1, u2} α β)) (Set.instHasSubsetSet.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β u v) s))))))))
Case conversion may be inaccurate. Consider using '#align is_open_prod_iff isOpen_prod_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem isOpen_prod_iff {s : Set (α × β)} :
    IsOpen s ↔
      ∀ a b,
        (a, b) ∈ s → ∃ (u : Set α)(v : Set β), IsOpen u ∧ IsOpen v ∧ a ∈ u ∧ b ∈ v ∧ u ×ˢ v ⊆ s :=
  by
  rw [isOpen_iff_nhds]
  simp_rw [le_principal_iff, Prod.forall,
    ((nhds_basis_opens _).prod_nhds (nhds_basis_opens _)).mem_iff, Prod.exists, exists_prop]
  simp only [and_assoc', and_left_comm]
#align is_open_prod_iff isOpen_prod_iff

/- warning: prod_induced_induced -> prod_induced_induced is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {δ : Type.{u2}} [_inst_2 : TopologicalSpace.{u1} β] [_inst_4 : TopologicalSpace.{u2} δ] {α : Type.{u3}} {γ : Type.{u4}} (f : α -> β) (g : γ -> δ), Eq.{succ (max u3 u4)} (TopologicalSpace.{max u3 u4} (Prod.{u3, u4} α γ)) (Prod.topologicalSpace.{u3, u4} α γ (TopologicalSpace.induced.{u3, u1} α β f _inst_2) (TopologicalSpace.induced.{u4, u2} γ δ g _inst_4)) (TopologicalSpace.induced.{max u3 u4, max u1 u2} (Prod.{u3, u4} α γ) (Prod.{u1, u2} β δ) (fun (p : Prod.{u3, u4} α γ) => Prod.mk.{u1, u2} β δ (f (Prod.fst.{u3, u4} α γ p)) (g (Prod.snd.{u3, u4} α γ p))) (Prod.topologicalSpace.{u1, u2} β δ _inst_2 _inst_4))
but is expected to have type
  forall {β : Type.{u3}} {δ : Type.{u4}} {_inst_2 : Type.{u2}} {_inst_4 : Type.{u1}} [α : TopologicalSpace.{u4} δ] [γ : TopologicalSpace.{u1} _inst_4] (f : β -> δ) (g : _inst_2 -> _inst_4), Eq.{max (succ u3) (succ u2)} (TopologicalSpace.{max u2 u3} (Prod.{u3, u2} β _inst_2)) (instTopologicalSpaceProd.{u3, u2} β _inst_2 (TopologicalSpace.induced.{u3, u4} β δ f α) (TopologicalSpace.induced.{u2, u1} _inst_2 _inst_4 g γ)) (TopologicalSpace.induced.{max u3 u2, max u1 u4} (Prod.{u3, u2} β _inst_2) (Prod.{u4, u1} δ _inst_4) (fun (p : Prod.{u3, u2} β _inst_2) => Prod.mk.{u4, u1} δ _inst_4 (f (Prod.fst.{u3, u2} β _inst_2 p)) (g (Prod.snd.{u3, u2} β _inst_2 p))) (instTopologicalSpaceProd.{u4, u1} δ _inst_4 α γ))
Case conversion may be inaccurate. Consider using '#align prod_induced_induced prod_induced_inducedₓ'. -/
/-- A product of induced topologies is induced by the product map -/
theorem prod_induced_induced {α γ : Type _} (f : α → β) (g : γ → δ) :
    @Prod.topologicalSpace α γ (induced f ‹_›) (induced g ‹_›) =
      induced (fun p => (f p.1, g p.2)) Prod.topologicalSpace :=
  by simp_rw [Prod.topologicalSpace, induced_inf, induced_compose]
#align prod_induced_induced prod_induced_induced

/- warning: continuous_uncurry_of_discrete_topology_left -> continuous_uncurry_of_discreteTopology_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_7 : DiscreteTopology.{u1} α _inst_1] {f : α -> β -> γ}, (forall (a : α), Continuous.{u2, u3} β γ _inst_2 _inst_3 (f a)) -> (Continuous.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3 (Function.uncurry.{u1, u2, u3} α β γ f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u1} γ] [_inst_7 : DiscreteTopology.{u2} α _inst_1] {f : α -> β -> γ}, (forall (a : α), Continuous.{u3, u1} β γ _inst_2 _inst_3 (f a)) -> (Continuous.{max u3 u2, u1} (Prod.{u2, u3} α β) γ (instTopologicalSpaceProd.{u2, u3} α β _inst_1 _inst_2) _inst_3 (Function.uncurry.{u2, u3, u1} α β γ f))
Case conversion may be inaccurate. Consider using '#align continuous_uncurry_of_discrete_topology_left continuous_uncurry_of_discreteTopology_leftₓ'. -/
theorem continuous_uncurry_of_discreteTopology_left [DiscreteTopology α] {f : α → β → γ}
    (h : ∀ a, Continuous (f a)) : Continuous (uncurry f) :=
  continuous_iff_continuousAt.2 fun ⟨a, b⟩ => by
    simp only [ContinuousAt, nhds_prod_eq, nhds_discrete α, pure_prod, tendsto_map'_iff, (· ∘ ·),
      uncurry, (h a).Tendsto]
#align continuous_uncurry_of_discrete_topology_left continuous_uncurry_of_discreteTopology_left

/- warning: exists_nhds_square -> exists_nhds_square is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} (Prod.{u1, u1} α α)} {x : α}, (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) s (nhds.{u1} (Prod.{u1, u1} α α) (Prod.topologicalSpace.{u1, u1} α α _inst_1 _inst_1) (Prod.mk.{u1, u1} α α x x))) -> (Exists.{succ u1} (Set.{u1} α) (fun (U : Set.{u1} α) => And (IsOpen.{u1} α _inst_1 U) (And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x U) (HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasSubset.{u1} (Prod.{u1, u1} α α)) (Set.prod.{u1, u1} α α U U) s))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} (Prod.{u1, u1} α α)} {x : α}, (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) s (nhds.{u1} (Prod.{u1, u1} α α) (instTopologicalSpaceProd.{u1, u1} α α _inst_1 _inst_1) (Prod.mk.{u1, u1} α α x x))) -> (Exists.{succ u1} (Set.{u1} α) (fun (U : Set.{u1} α) => And (IsOpen.{u1} α _inst_1 U) (And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x U) (HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instHasSubsetSet.{u1} (Prod.{u1, u1} α α)) (Set.prod.{u1, u1} α α U U) s))))
Case conversion may be inaccurate. Consider using '#align exists_nhds_square exists_nhds_squareₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Given a neighborhood `s` of `(x, x)`, then `(x, x)` has a square open neighborhood
  that is a subset of `s`. -/
theorem exists_nhds_square {s : Set (α × α)} {x : α} (hx : s ∈ 𝓝 (x, x)) :
    ∃ U : Set α, IsOpen U ∧ x ∈ U ∧ U ×ˢ U ⊆ s := by
  simpa [nhds_prod_eq, (nhds_basis_opens x).prod_self.mem_iff, and_assoc, and_left_comm] using hx
#align exists_nhds_square exists_nhds_square

/- warning: map_fst_nhds_within -> map_fst_nhdsWithin is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (x : Prod.{u1, u2} α β), Eq.{succ u1} (Filter.{u1} α) (Filter.map.{max u1 u2, u1} (Prod.{u1, u2} α β) α (Prod.fst.{u1, u2} α β) (nhdsWithin.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) x (Set.preimage.{max u1 u2, u2} (Prod.{u1, u2} α β) β (Prod.snd.{u1, u2} α β) (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) (Prod.snd.{u1, u2} α β x))))) (nhds.{u1} α _inst_1 (Prod.fst.{u1, u2} α β x))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (x : Prod.{u1, u2} α β), Eq.{succ u1} (Filter.{u1} α) (Filter.map.{max u2 u1, u1} (Prod.{u1, u2} α β) α (Prod.fst.{u1, u2} α β) (nhdsWithin.{max u2 u1} (Prod.{u1, u2} α β) (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) x (Set.preimage.{max u1 u2, u2} (Prod.{u1, u2} α β) β (Prod.snd.{u1, u2} α β) (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.instSingletonSet.{u2} β) (Prod.snd.{u1, u2} α β x))))) (nhds.{u1} α _inst_1 (Prod.fst.{u1, u2} α β x))
Case conversion may be inaccurate. Consider using '#align map_fst_nhds_within map_fst_nhdsWithinₓ'. -/
/-- `prod.fst` maps neighborhood of `x : α × β` within the section `prod.snd ⁻¹' {x.2}`
to `𝓝 x.1`. -/
theorem map_fst_nhdsWithin (x : α × β) : map Prod.fst (𝓝[Prod.snd ⁻¹' {x.2}] x) = 𝓝 x.1 :=
  by
  refine' le_antisymm (continuous_at_fst.mono_left inf_le_left) fun s hs => _
  rcases x with ⟨x, y⟩
  rw [mem_map, nhdsWithin, mem_inf_principal, mem_nhds_prod_iff] at hs
  rcases hs with ⟨u, hu, v, hv, H⟩
  simp only [prod_subset_iff, mem_singleton_iff, mem_set_of_eq, mem_preimage] at H
  exact mem_of_superset hu fun z hz => H _ hz _ (mem_of_mem_nhds hv) rfl
#align map_fst_nhds_within map_fst_nhdsWithin

/- warning: map_fst_nhds -> map_fst_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (x : Prod.{u1, u2} α β), Eq.{succ u1} (Filter.{u1} α) (Filter.map.{max u1 u2, u1} (Prod.{u1, u2} α β) α (Prod.fst.{u1, u2} α β) (nhds.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) x)) (nhds.{u1} α _inst_1 (Prod.fst.{u1, u2} α β x))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (x : Prod.{u1, u2} α β), Eq.{succ u1} (Filter.{u1} α) (Filter.map.{max u2 u1, u1} (Prod.{u1, u2} α β) α (Prod.fst.{u1, u2} α β) (nhds.{max u2 u1} (Prod.{u1, u2} α β) (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) x)) (nhds.{u1} α _inst_1 (Prod.fst.{u1, u2} α β x))
Case conversion may be inaccurate. Consider using '#align map_fst_nhds map_fst_nhdsₓ'. -/
@[simp]
theorem map_fst_nhds (x : α × β) : map Prod.fst (𝓝 x) = 𝓝 x.1 :=
  le_antisymm continuousAt_fst <| (map_fst_nhdsWithin x).symm.trans_le (map_mono inf_le_left)
#align map_fst_nhds map_fst_nhds

/- warning: is_open_map_fst -> isOpenMap_fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], IsOpenMap.{max u1 u2, u1} (Prod.{u1, u2} α β) α (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_1 (Prod.fst.{u1, u2} α β)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], IsOpenMap.{max u1 u2, u1} (Prod.{u1, u2} α β) α (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) _inst_1 (Prod.fst.{u1, u2} α β)
Case conversion may be inaccurate. Consider using '#align is_open_map_fst isOpenMap_fstₓ'. -/
/-- The first projection in a product of topological spaces sends open sets to open sets. -/
theorem isOpenMap_fst : IsOpenMap (@Prod.fst α β) :=
  isOpenMap_iff_nhds_le.2 fun x => (map_fst_nhds x).ge
#align is_open_map_fst isOpenMap_fst

/- warning: map_snd_nhds_within -> map_snd_nhdsWithin is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (x : Prod.{u1, u2} α β), Eq.{succ u2} (Filter.{u2} β) (Filter.map.{max u1 u2, u2} (Prod.{u1, u2} α β) β (Prod.snd.{u1, u2} α β) (nhdsWithin.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) x (Set.preimage.{max u1 u2, u1} (Prod.{u1, u2} α β) α (Prod.fst.{u1, u2} α β) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) (Prod.fst.{u1, u2} α β x))))) (nhds.{u2} β _inst_2 (Prod.snd.{u1, u2} α β x))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (x : Prod.{u1, u2} α β), Eq.{succ u2} (Filter.{u2} β) (Filter.map.{max u2 u1, u2} (Prod.{u1, u2} α β) β (Prod.snd.{u1, u2} α β) (nhdsWithin.{max u2 u1} (Prod.{u1, u2} α β) (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) x (Set.preimage.{max u1 u2, u1} (Prod.{u1, u2} α β) α (Prod.fst.{u1, u2} α β) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) (Prod.fst.{u1, u2} α β x))))) (nhds.{u2} β _inst_2 (Prod.snd.{u1, u2} α β x))
Case conversion may be inaccurate. Consider using '#align map_snd_nhds_within map_snd_nhdsWithinₓ'. -/
/-- `prod.snd` maps neighborhood of `x : α × β` within the section `prod.fst ⁻¹' {x.1}`
to `𝓝 x.2`. -/
theorem map_snd_nhdsWithin (x : α × β) : map Prod.snd (𝓝[Prod.fst ⁻¹' {x.1}] x) = 𝓝 x.2 :=
  by
  refine' le_antisymm (continuous_at_snd.mono_left inf_le_left) fun s hs => _
  rcases x with ⟨x, y⟩
  rw [mem_map, nhdsWithin, mem_inf_principal, mem_nhds_prod_iff] at hs
  rcases hs with ⟨u, hu, v, hv, H⟩
  simp only [prod_subset_iff, mem_singleton_iff, mem_set_of_eq, mem_preimage] at H
  exact mem_of_superset hv fun z hz => H _ (mem_of_mem_nhds hu) _ hz rfl
#align map_snd_nhds_within map_snd_nhdsWithin

/- warning: map_snd_nhds -> map_snd_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (x : Prod.{u1, u2} α β), Eq.{succ u2} (Filter.{u2} β) (Filter.map.{max u1 u2, u2} (Prod.{u1, u2} α β) β (Prod.snd.{u1, u2} α β) (nhds.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) x)) (nhds.{u2} β _inst_2 (Prod.snd.{u1, u2} α β x))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (x : Prod.{u1, u2} α β), Eq.{succ u2} (Filter.{u2} β) (Filter.map.{max u2 u1, u2} (Prod.{u1, u2} α β) β (Prod.snd.{u1, u2} α β) (nhds.{max u2 u1} (Prod.{u1, u2} α β) (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) x)) (nhds.{u2} β _inst_2 (Prod.snd.{u1, u2} α β x))
Case conversion may be inaccurate. Consider using '#align map_snd_nhds map_snd_nhdsₓ'. -/
@[simp]
theorem map_snd_nhds (x : α × β) : map Prod.snd (𝓝 x) = 𝓝 x.2 :=
  le_antisymm continuousAt_snd <| (map_snd_nhdsWithin x).symm.trans_le (map_mono inf_le_left)
#align map_snd_nhds map_snd_nhds

/- warning: is_open_map_snd -> isOpenMap_snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], IsOpenMap.{max u1 u2, u2} (Prod.{u1, u2} α β) β (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_2 (Prod.snd.{u1, u2} α β)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], IsOpenMap.{max u1 u2, u2} (Prod.{u1, u2} α β) β (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) _inst_2 (Prod.snd.{u1, u2} α β)
Case conversion may be inaccurate. Consider using '#align is_open_map_snd isOpenMap_sndₓ'. -/
/-- The second projection in a product of topological spaces sends open sets to open sets. -/
theorem isOpenMap_snd : IsOpenMap (@Prod.snd α β) :=
  isOpenMap_iff_nhds_le.2 fun x => (map_snd_nhds x).ge
#align is_open_map_snd isOpenMap_snd

/- warning: is_open_prod_iff' -> isOpen_prod_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{u1} α} {t : Set.{u2} β}, Iff (IsOpen.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Set.prod.{u1, u2} α β s t)) (Or (And (IsOpen.{u1} α _inst_1 s) (IsOpen.{u2} β _inst_2 t)) (Or (Eq.{succ u1} (Set.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Eq.{succ u2} (Set.{u2} β) t (EmptyCollection.emptyCollection.{u2} (Set.{u2} β) (Set.hasEmptyc.{u2} β)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{u1} α} {t : Set.{u2} β}, Iff (IsOpen.{max u2 u1} (Prod.{u1, u2} α β) (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) (Set.prod.{u1, u2} α β s t)) (Or (And (IsOpen.{u1} α _inst_1 s) (IsOpen.{u2} β _inst_2 t)) (Or (Eq.{succ u1} (Set.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (Eq.{succ u2} (Set.{u2} β) t (EmptyCollection.emptyCollection.{u2} (Set.{u2} β) (Set.instEmptyCollectionSet.{u2} β)))))
Case conversion may be inaccurate. Consider using '#align is_open_prod_iff' isOpen_prod_iff'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- A product set is open in a product space if and only if each factor is open, or one of them is
empty -/
theorem isOpen_prod_iff' {s : Set α} {t : Set β} :
    IsOpen (s ×ˢ t) ↔ IsOpen s ∧ IsOpen t ∨ s = ∅ ∨ t = ∅ :=
  by
  cases' (s ×ˢ t).eq_empty_or_nonempty with h h
  · simp [h, prod_eq_empty_iff.1 h]
  · have st : s.nonempty ∧ t.nonempty := prod_nonempty_iff.1 h
    constructor
    · intro (H : IsOpen (s ×ˢ t))
      refine' Or.inl ⟨_, _⟩
      show IsOpen s
      · rw [← fst_image_prod s st.2]
        exact isOpenMap_fst _ H
      show IsOpen t
      · rw [← snd_image_prod st.1 t]
        exact isOpenMap_snd _ H
    · intro H
      simp only [st.1.ne_empty, st.2.ne_empty, not_false_iff, or_false_iff] at H
      exact H.1.Prod H.2
#align is_open_prod_iff' isOpen_prod_iff'

/- warning: closure_prod_eq -> closure_prod_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{u1} α} {t : Set.{u2} β}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (closure.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Set.prod.{u1, u2} α β s t)) (Set.prod.{u1, u2} α β (closure.{u1} α _inst_1 s) (closure.{u2} β _inst_2 t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{u1} α} {t : Set.{u2} β}, Eq.{max (succ u1) (succ u2)} (Set.{max u2 u1} (Prod.{u1, u2} α β)) (closure.{max u2 u1} (Prod.{u1, u2} α β) (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) (Set.prod.{u1, u2} α β s t)) (Set.prod.{u1, u2} α β (closure.{u1} α _inst_1 s) (closure.{u2} β _inst_2 t))
Case conversion may be inaccurate. Consider using '#align closure_prod_eq closure_prod_eqₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem closure_prod_eq {s : Set α} {t : Set β} : closure (s ×ˢ t) = closure s ×ˢ closure t :=
  Set.ext fun ⟨a, b⟩ =>
    by
    have : (𝓝 a ×ᶠ 𝓝 b) ⊓ 𝓟 (s ×ˢ t) = 𝓝 a ⊓ 𝓟 s ×ᶠ 𝓝 b ⊓ 𝓟 t := by
      rw [← prod_inf_prod, prod_principal_principal]
    simp [closure_eq_cluster_pts, ClusterPt, nhds_prod_eq, this] <;> exact prod_ne_bot
#align closure_prod_eq closure_prod_eq

/- warning: interior_prod_eq -> interior_prod_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (s : Set.{u1} α) (t : Set.{u2} β), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (interior.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Set.prod.{u1, u2} α β s t)) (Set.prod.{u1, u2} α β (interior.{u1} α _inst_1 s) (interior.{u2} β _inst_2 t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (s : Set.{u1} α) (t : Set.{u2} β), Eq.{max (succ u1) (succ u2)} (Set.{max u2 u1} (Prod.{u1, u2} α β)) (interior.{max u2 u1} (Prod.{u1, u2} α β) (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) (Set.prod.{u1, u2} α β s t)) (Set.prod.{u1, u2} α β (interior.{u1} α _inst_1 s) (interior.{u2} β _inst_2 t))
Case conversion may be inaccurate. Consider using '#align interior_prod_eq interior_prod_eqₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem interior_prod_eq (s : Set α) (t : Set β) : interior (s ×ˢ t) = interior s ×ˢ interior t :=
  Set.ext fun ⟨a, b⟩ => by simp only [mem_interior_iff_mem_nhds, mem_prod, prod_mem_nhds_iff]
#align interior_prod_eq interior_prod_eq

/- warning: frontier_prod_eq -> frontier_prod_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (s : Set.{u1} α) (t : Set.{u2} β), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (frontier.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Set.prod.{u1, u2} α β s t)) (Union.union.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.hasUnion.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β (closure.{u1} α _inst_1 s) (frontier.{u2} β _inst_2 t)) (Set.prod.{u1, u2} α β (frontier.{u1} α _inst_1 s) (closure.{u2} β _inst_2 t)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (s : Set.{u1} α) (t : Set.{u2} β), Eq.{max (succ u1) (succ u2)} (Set.{max u2 u1} (Prod.{u1, u2} α β)) (frontier.{max u2 u1} (Prod.{u1, u2} α β) (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) (Set.prod.{u1, u2} α β s t)) (Union.union.{max u2 u1} (Set.{max u2 u1} (Prod.{u1, u2} α β)) (Set.instUnionSet.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β (closure.{u1} α _inst_1 s) (frontier.{u2} β _inst_2 t)) (Set.prod.{u1, u2} α β (frontier.{u1} α _inst_1 s) (closure.{u2} β _inst_2 t)))
Case conversion may be inaccurate. Consider using '#align frontier_prod_eq frontier_prod_eqₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem frontier_prod_eq (s : Set α) (t : Set β) :
    frontier (s ×ˢ t) = closure s ×ˢ frontier t ∪ frontier s ×ˢ closure t := by
  simp only [frontier, closure_prod_eq, interior_prod_eq, prod_diff_prod]
#align frontier_prod_eq frontier_prod_eq

/- warning: frontier_prod_univ_eq -> frontier_prod_univ_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (s : Set.{u1} α), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (frontier.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Set.prod.{u1, u2} α β s (Set.univ.{u2} β))) (Set.prod.{u1, u2} α β (frontier.{u1} α _inst_1 s) (Set.univ.{u2} β))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (s : Set.{u1} α), Eq.{max (succ u1) (succ u2)} (Set.{max u2 u1} (Prod.{u1, u2} α β)) (frontier.{max u2 u1} (Prod.{u1, u2} α β) (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) (Set.prod.{u1, u2} α β s (Set.univ.{u2} β))) (Set.prod.{u1, u2} α β (frontier.{u1} α _inst_1 s) (Set.univ.{u2} β))
Case conversion may be inaccurate. Consider using '#align frontier_prod_univ_eq frontier_prod_univ_eqₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem frontier_prod_univ_eq (s : Set α) : frontier (s ×ˢ (univ : Set β)) = frontier s ×ˢ univ :=
  by simp [frontier_prod_eq]
#align frontier_prod_univ_eq frontier_prod_univ_eq

/- warning: frontier_univ_prod_eq -> frontier_univ_prod_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (s : Set.{u2} β), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (frontier.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Set.prod.{u1, u2} α β (Set.univ.{u1} α) s)) (Set.prod.{u1, u2} α β (Set.univ.{u1} α) (frontier.{u2} β _inst_2 s))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (s : Set.{u2} β), Eq.{max (succ u1) (succ u2)} (Set.{max u2 u1} (Prod.{u1, u2} α β)) (frontier.{max u2 u1} (Prod.{u1, u2} α β) (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) (Set.prod.{u1, u2} α β (Set.univ.{u1} α) s)) (Set.prod.{u1, u2} α β (Set.univ.{u1} α) (frontier.{u2} β _inst_2 s))
Case conversion may be inaccurate. Consider using '#align frontier_univ_prod_eq frontier_univ_prod_eqₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem frontier_univ_prod_eq (s : Set β) : frontier ((univ : Set α) ×ˢ s) = univ ×ˢ frontier s :=
  by simp [frontier_prod_eq]
#align frontier_univ_prod_eq frontier_univ_prod_eq

/- warning: map_mem_closure₂ -> map_mem_closure₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {f : α -> β -> γ} {a : α} {b : β} {s : Set.{u1} α} {t : Set.{u2} β} {u : Set.{u3} γ}, (Continuous.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3 (Function.uncurry.{u1, u2, u3} α β γ f)) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (closure.{u1} α _inst_1 s)) -> (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (closure.{u2} β _inst_2 t)) -> (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (forall (b : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b t) -> (Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) (f a b) u))) -> (Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) (f a b) (closure.{u3} γ _inst_3 u))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u1} γ] {f : α -> β -> γ} {a : α} {b : β} {s : Set.{u2} α} {t : Set.{u3} β} {u : Set.{u1} γ}, (Continuous.{max u3 u2, u1} (Prod.{u2, u3} α β) γ (instTopologicalSpaceProd.{u2, u3} α β _inst_1 _inst_2) _inst_3 (Function.uncurry.{u2, u3, u1} α β γ f)) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (closure.{u2} α _inst_1 s)) -> (Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) b (closure.{u3} β _inst_2 t)) -> (forall (a : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) -> (forall (b : β), (Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) b t) -> (Membership.mem.{u1, u1} γ (Set.{u1} γ) (Set.instMembershipSet.{u1} γ) (f a b) u))) -> (Membership.mem.{u1, u1} γ (Set.{u1} γ) (Set.instMembershipSet.{u1} γ) (f a b) (closure.{u1} γ _inst_3 u))
Case conversion may be inaccurate. Consider using '#align map_mem_closure₂ map_mem_closure₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem map_mem_closure₂ {f : α → β → γ} {a : α} {b : β} {s : Set α} {t : Set β} {u : Set γ}
    (hf : Continuous (uncurry f)) (ha : a ∈ closure s) (hb : b ∈ closure t)
    (h : ∀ a ∈ s, ∀ b ∈ t, f a b ∈ u) : f a b ∈ closure u :=
  have H₁ : (a, b) ∈ closure (s ×ˢ t) := by simpa only [closure_prod_eq] using mk_mem_prod ha hb
  have H₂ : MapsTo (uncurry f) (s ×ˢ t) u := forall_prod_set.2 h
  H₂.closure hf H₁
#align map_mem_closure₂ map_mem_closure₂

/- warning: is_closed.prod -> IsClosed.prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s₁ : Set.{u1} α} {s₂ : Set.{u2} β}, (IsClosed.{u1} α _inst_1 s₁) -> (IsClosed.{u2} β _inst_2 s₂) -> (IsClosed.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Set.prod.{u1, u2} α β s₁ s₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s₁ : Set.{u1} α} {s₂ : Set.{u2} β}, (IsClosed.{u1} α _inst_1 s₁) -> (IsClosed.{u2} β _inst_2 s₂) -> (IsClosed.{max u2 u1} (Prod.{u1, u2} α β) (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) (Set.prod.{u1, u2} α β s₁ s₂))
Case conversion may be inaccurate. Consider using '#align is_closed.prod IsClosed.prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem IsClosed.prod {s₁ : Set α} {s₂ : Set β} (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) :
    IsClosed (s₁ ×ˢ s₂) :=
  closure_eq_iff_isClosed.mp <| by simp only [h₁.closure_eq, h₂.closure_eq, closure_prod_eq]
#align is_closed.prod IsClosed.prod

/- warning: dense.prod -> Dense.prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{u1} α} {t : Set.{u2} β}, (Dense.{u1} α _inst_1 s) -> (Dense.{u2} β _inst_2 t) -> (Dense.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Set.prod.{u1, u2} α β s t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{u1} α} {t : Set.{u2} β}, (Dense.{u1} α _inst_1 s) -> (Dense.{u2} β _inst_2 t) -> (Dense.{max u2 u1} (Prod.{u1, u2} α β) (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) (Set.prod.{u1, u2} α β s t))
Case conversion may be inaccurate. Consider using '#align dense.prod Dense.prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The product of two dense sets is a dense set. -/
theorem Dense.prod {s : Set α} {t : Set β} (hs : Dense s) (ht : Dense t) : Dense (s ×ˢ t) :=
  fun x => by
  rw [closure_prod_eq]
  exact ⟨hs x.1, ht x.2⟩
#align dense.prod Dense.prod

/- warning: dense_range.prod_map -> DenseRange.prod_map is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {γ : Type.{u2}} [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : TopologicalSpace.{u2} γ] {ι : Type.{u3}} {κ : Type.{u4}} {f : ι -> β} {g : κ -> γ}, (DenseRange.{u1, u3} β _inst_2 ι f) -> (DenseRange.{u2, u4} γ _inst_3 κ g) -> (DenseRange.{max u1 u2, max u3 u4} (Prod.{u1, u2} β γ) (Prod.topologicalSpace.{u1, u2} β γ _inst_2 _inst_3) (Prod.{u3, u4} ι κ) (Prod.map.{u3, u1, u4, u2} ι β κ γ f g))
but is expected to have type
  forall {β : Type.{u4}} {γ : Type.{u1}} [_inst_2 : TopologicalSpace.{u4} β] [_inst_3 : TopologicalSpace.{u1} γ] {ι : Type.{u3}} {κ : Type.{u2}} {f : ι -> β} {g : κ -> γ}, (DenseRange.{u4, u3} β _inst_2 ι f) -> (DenseRange.{u1, u2} γ _inst_3 κ g) -> (DenseRange.{max u1 u4, max u2 u3} (Prod.{u4, u1} β γ) (instTopologicalSpaceProd.{u4, u1} β γ _inst_2 _inst_3) (Prod.{u3, u2} ι κ) (Prod.map.{u3, u4, u2, u1} ι β κ γ f g))
Case conversion may be inaccurate. Consider using '#align dense_range.prod_map DenseRange.prod_mapₓ'. -/
/-- If `f` and `g` are maps with dense range, then `prod.map f g` has dense range. -/
theorem DenseRange.prod_map {ι : Type _} {κ : Type _} {f : ι → β} {g : κ → γ} (hf : DenseRange f)
    (hg : DenseRange g) : DenseRange (Prod.map f g) := by
  simpa only [DenseRange, prod_range_range_eq] using hf.prod hg
#align dense_range.prod_map DenseRange.prod_map

/- warning: inducing.prod_mk -> Inducing.prod_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] {f : α -> β} {g : γ -> δ}, (Inducing.{u1, u2} α β _inst_1 _inst_2 f) -> (Inducing.{u3, u4} γ δ _inst_3 _inst_4 g) -> (Inducing.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) (Prod.topologicalSpace.{u1, u3} α γ _inst_1 _inst_3) (Prod.topologicalSpace.{u2, u4} β δ _inst_2 _inst_4) (fun (x : Prod.{u1, u3} α γ) => Prod.mk.{u2, u4} β δ (f (Prod.fst.{u1, u3} α γ x)) (g (Prod.snd.{u1, u3} α γ x))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {γ : Type.{u2}} {δ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u4} β] [_inst_3 : TopologicalSpace.{u2} γ] [_inst_4 : TopologicalSpace.{u1} δ] {f : α -> β} {g : γ -> δ}, (Inducing.{u3, u4} α β _inst_1 _inst_2 f) -> (Inducing.{u2, u1} γ δ _inst_3 _inst_4 g) -> (Inducing.{max u2 u3, max u1 u4} (Prod.{u3, u2} α γ) (Prod.{u4, u1} β δ) (instTopologicalSpaceProd.{u3, u2} α γ _inst_1 _inst_3) (instTopologicalSpaceProd.{u4, u1} β δ _inst_2 _inst_4) (Prod.map.{u3, u4, u2, u1} α β γ δ f g))
Case conversion may be inaccurate. Consider using '#align inducing.prod_mk Inducing.prod_mapₓ'. -/
theorem Inducing.prod_map {f : α → β} {g : γ → δ} (hf : Inducing f) (hg : Inducing g) :
    Inducing fun x : α × γ => (f x.1, g x.2) :=
  ⟨by
    rw [Prod.topologicalSpace, Prod.topologicalSpace, hf.induced, hg.induced, induced_compose,
      induced_compose, induced_inf, induced_compose, induced_compose]⟩
#align inducing.prod_mk Inducing.prod_map

/- warning: embedding.prod_mk -> Embedding.prod_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] {f : α -> β} {g : γ -> δ}, (Embedding.{u1, u2} α β _inst_1 _inst_2 f) -> (Embedding.{u3, u4} γ δ _inst_3 _inst_4 g) -> (Embedding.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) (Prod.topologicalSpace.{u1, u3} α γ _inst_1 _inst_3) (Prod.topologicalSpace.{u2, u4} β δ _inst_2 _inst_4) (fun (x : Prod.{u1, u3} α γ) => Prod.mk.{u2, u4} β δ (f (Prod.fst.{u1, u3} α γ x)) (g (Prod.snd.{u1, u3} α γ x))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {γ : Type.{u2}} {δ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u4} β] [_inst_3 : TopologicalSpace.{u2} γ] [_inst_4 : TopologicalSpace.{u1} δ] {f : α -> β} {g : γ -> δ}, (Embedding.{u3, u4} α β _inst_1 _inst_2 f) -> (Embedding.{u2, u1} γ δ _inst_3 _inst_4 g) -> (Embedding.{max u2 u3, max u1 u4} (Prod.{u3, u2} α γ) (Prod.{u4, u1} β δ) (instTopologicalSpaceProd.{u3, u2} α γ _inst_1 _inst_3) (instTopologicalSpaceProd.{u4, u1} β δ _inst_2 _inst_4) (Prod.map.{u3, u4, u2, u1} α β γ δ f g))
Case conversion may be inaccurate. Consider using '#align embedding.prod_mk Embedding.prod_mapₓ'. -/
theorem Embedding.prod_map {f : α → β} {g : γ → δ} (hf : Embedding f) (hg : Embedding g) :
    Embedding fun x : α × γ => (f x.1, g x.2) :=
  { hf.to_inducing.prod_mk hg.to_inducing with
    inj := fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ => by simp <;> exact fun h₁ h₂ => ⟨hf.inj h₁, hg.inj h₂⟩ }
#align embedding.prod_mk Embedding.prod_map

/- warning: is_open_map.prod -> IsOpenMap.prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] {f : α -> β} {g : γ -> δ}, (IsOpenMap.{u1, u2} α β _inst_1 _inst_2 f) -> (IsOpenMap.{u3, u4} γ δ _inst_3 _inst_4 g) -> (IsOpenMap.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) (Prod.topologicalSpace.{u1, u3} α γ _inst_1 _inst_3) (Prod.topologicalSpace.{u2, u4} β δ _inst_2 _inst_4) (fun (p : Prod.{u1, u3} α γ) => Prod.mk.{u2, u4} β δ (f (Prod.fst.{u1, u3} α γ p)) (g (Prod.snd.{u1, u3} α γ p))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {γ : Type.{u2}} {δ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u4} β] [_inst_3 : TopologicalSpace.{u2} γ] [_inst_4 : TopologicalSpace.{u1} δ] {f : α -> β} {g : γ -> δ}, (IsOpenMap.{u3, u4} α β _inst_1 _inst_2 f) -> (IsOpenMap.{u2, u1} γ δ _inst_3 _inst_4 g) -> (IsOpenMap.{max u3 u2, max u1 u4} (Prod.{u3, u2} α γ) (Prod.{u4, u1} β δ) (instTopologicalSpaceProd.{u3, u2} α γ _inst_1 _inst_3) (instTopologicalSpaceProd.{u4, u1} β δ _inst_2 _inst_4) (fun (p : Prod.{u3, u2} α γ) => Prod.mk.{u4, u1} β δ (f (Prod.fst.{u3, u2} α γ p)) (g (Prod.snd.{u3, u2} α γ p))))
Case conversion may be inaccurate. Consider using '#align is_open_map.prod IsOpenMap.prodₓ'. -/
protected theorem IsOpenMap.prod {f : α → β} {g : γ → δ} (hf : IsOpenMap f) (hg : IsOpenMap g) :
    IsOpenMap fun p : α × γ => (f p.1, g p.2) :=
  by
  rw [isOpenMap_iff_nhds_le]
  rintro ⟨a, b⟩
  rw [nhds_prod_eq, nhds_prod_eq, ← Filter.prod_map_map_eq]
  exact Filter.prod_mono (hf.nhds_le a) (hg.nhds_le b)
#align is_open_map.prod IsOpenMap.prod

/- warning: open_embedding.prod -> OpenEmbedding.prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] {f : α -> β} {g : γ -> δ}, (OpenEmbedding.{u1, u2} α β _inst_1 _inst_2 f) -> (OpenEmbedding.{u3, u4} γ δ _inst_3 _inst_4 g) -> (OpenEmbedding.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) (Prod.topologicalSpace.{u1, u3} α γ _inst_1 _inst_3) (Prod.topologicalSpace.{u2, u4} β δ _inst_2 _inst_4) (fun (x : Prod.{u1, u3} α γ) => Prod.mk.{u2, u4} β δ (f (Prod.fst.{u1, u3} α γ x)) (g (Prod.snd.{u1, u3} α γ x))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {γ : Type.{u2}} {δ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u4} β] [_inst_3 : TopologicalSpace.{u2} γ] [_inst_4 : TopologicalSpace.{u1} δ] {f : α -> β} {g : γ -> δ}, (OpenEmbedding.{u3, u4} α β _inst_1 _inst_2 f) -> (OpenEmbedding.{u2, u1} γ δ _inst_3 _inst_4 g) -> (OpenEmbedding.{max u3 u2, max u1 u4} (Prod.{u3, u2} α γ) (Prod.{u4, u1} β δ) (instTopologicalSpaceProd.{u3, u2} α γ _inst_1 _inst_3) (instTopologicalSpaceProd.{u4, u1} β δ _inst_2 _inst_4) (fun (x : Prod.{u3, u2} α γ) => Prod.mk.{u4, u1} β δ (f (Prod.fst.{u3, u2} α γ x)) (g (Prod.snd.{u3, u2} α γ x))))
Case conversion may be inaccurate. Consider using '#align open_embedding.prod OpenEmbedding.prodₓ'. -/
protected theorem OpenEmbedding.prod {f : α → β} {g : γ → δ} (hf : OpenEmbedding f)
    (hg : OpenEmbedding g) : OpenEmbedding fun x : α × γ => (f x.1, g x.2) :=
  openEmbedding_of_embedding_open (hf.1.prod_mk hg.1) (hf.IsOpenMap.Prod hg.IsOpenMap)
#align open_embedding.prod OpenEmbedding.prod

/- warning: embedding_graph -> embedding_graph is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β}, (Continuous.{u1, u2} α β _inst_1 _inst_2 f) -> (Embedding.{u1, max u1 u2} α (Prod.{u1, u2} α β) _inst_1 (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (fun (x : α) => Prod.mk.{u1, u2} α β x (f x)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β}, (Continuous.{u1, u2} α β _inst_1 _inst_2 f) -> (Embedding.{u1, max u2 u1} α (Prod.{u1, u2} α β) _inst_1 (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) (fun (x : α) => Prod.mk.{u1, u2} α β x (f x)))
Case conversion may be inaccurate. Consider using '#align embedding_graph embedding_graphₓ'. -/
theorem embedding_graph {f : α → β} (hf : Continuous f) : Embedding fun x => (x, f x) :=
  embedding_of_embedding_compose (continuous_id.prod_mk hf) continuous_fst embedding_id
#align embedding_graph embedding_graph

end Prod

section Sum

open Sum

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

/- warning: continuous_inl -> continuous_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], Continuous.{u1, max u1 u2} α (Sum.{u1, u2} α β) _inst_1 (Sum.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Sum.inl.{u1, u2} α β)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], Continuous.{u1, max u1 u2} α (Sum.{u1, u2} α β) _inst_1 (instTopologicalSpaceSum.{u1, u2} α β _inst_1 _inst_2) (Sum.inl.{u1, u2} α β)
Case conversion may be inaccurate. Consider using '#align continuous_inl continuous_inlₓ'. -/
@[continuity]
theorem continuous_inl : Continuous (@inl α β) :=
  continuous_sup_rng_left continuous_coinduced_rng
#align continuous_inl continuous_inl

/- warning: continuous_inr -> continuous_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], Continuous.{u2, max u1 u2} β (Sum.{u1, u2} α β) _inst_2 (Sum.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Sum.inr.{u1, u2} α β)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], Continuous.{u2, max u1 u2} β (Sum.{u1, u2} α β) _inst_2 (instTopologicalSpaceSum.{u1, u2} α β _inst_1 _inst_2) (Sum.inr.{u1, u2} α β)
Case conversion may be inaccurate. Consider using '#align continuous_inr continuous_inrₓ'. -/
@[continuity]
theorem continuous_inr : Continuous (@inr α β) :=
  continuous_sup_rng_right continuous_coinduced_rng
#align continuous_inr continuous_inr

/- warning: is_open_sum_iff -> isOpen_sum_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{max u1 u2} (Sum.{u1, u2} α β)}, Iff (IsOpen.{max u1 u2} (Sum.{u1, u2} α β) (Sum.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) s) (And (IsOpen.{u1} α _inst_1 (Set.preimage.{u1, max u1 u2} α (Sum.{u1, u2} α β) (Sum.inl.{u1, u2} α β) s)) (IsOpen.{u2} β _inst_2 (Set.preimage.{u2, max u1 u2} β (Sum.{u1, u2} α β) (Sum.inr.{u1, u2} α β) s)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{max u2 u1} (Sum.{u1, u2} α β)}, Iff (IsOpen.{max u1 u2} (Sum.{u1, u2} α β) (instTopologicalSpaceSum.{u1, u2} α β _inst_1 _inst_2) s) (And (IsOpen.{u1} α _inst_1 (Set.preimage.{u1, max u2 u1} α (Sum.{u1, u2} α β) (Sum.inl.{u1, u2} α β) s)) (IsOpen.{u2} β _inst_2 (Set.preimage.{u2, max u2 u1} β (Sum.{u1, u2} α β) (Sum.inr.{u1, u2} α β) s)))
Case conversion may be inaccurate. Consider using '#align is_open_sum_iff isOpen_sum_iffₓ'. -/
theorem isOpen_sum_iff {s : Set (Sum α β)} : IsOpen s ↔ IsOpen (inl ⁻¹' s) ∧ IsOpen (inr ⁻¹' s) :=
  Iff.rfl
#align is_open_sum_iff isOpen_sum_iff

/- warning: is_open_map_inl -> isOpenMap_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], IsOpenMap.{u1, max u1 u2} α (Sum.{u1, u2} α β) _inst_1 (Sum.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Sum.inl.{u1, u2} α β)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], IsOpenMap.{u1, max u1 u2} α (Sum.{u1, u2} α β) _inst_1 (instTopologicalSpaceSum.{u1, u2} α β _inst_1 _inst_2) (Sum.inl.{u1, u2} α β)
Case conversion may be inaccurate. Consider using '#align is_open_map_inl isOpenMap_inlₓ'. -/
theorem isOpenMap_inl : IsOpenMap (@inl α β) := fun u hu => by
  simpa [isOpen_sum_iff, preimage_image_eq u Sum.inl_injective]
#align is_open_map_inl isOpenMap_inl

/- warning: is_open_map_inr -> isOpenMap_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], IsOpenMap.{u2, max u1 u2} β (Sum.{u1, u2} α β) _inst_2 (Sum.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Sum.inr.{u1, u2} α β)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], IsOpenMap.{u2, max u1 u2} β (Sum.{u1, u2} α β) _inst_2 (instTopologicalSpaceSum.{u1, u2} α β _inst_1 _inst_2) (Sum.inr.{u1, u2} α β)
Case conversion may be inaccurate. Consider using '#align is_open_map_inr isOpenMap_inrₓ'. -/
theorem isOpenMap_inr : IsOpenMap (@inr α β) := fun u hu => by
  simpa [isOpen_sum_iff, preimage_image_eq u Sum.inr_injective]
#align is_open_map_inr isOpenMap_inr

/- warning: open_embedding_inl -> openEmbedding_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], OpenEmbedding.{u1, max u1 u2} α (Sum.{u1, u2} α β) _inst_1 (Sum.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Sum.inl.{u1, u2} α β)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], OpenEmbedding.{u1, max u1 u2} α (Sum.{u1, u2} α β) _inst_1 (instTopologicalSpaceSum.{u1, u2} α β _inst_1 _inst_2) (Sum.inl.{u1, u2} α β)
Case conversion may be inaccurate. Consider using '#align open_embedding_inl openEmbedding_inlₓ'. -/
theorem openEmbedding_inl : OpenEmbedding (@inl α β) :=
  openEmbedding_of_continuous_injective_open continuous_inl inl_injective isOpenMap_inl
#align open_embedding_inl openEmbedding_inl

/- warning: open_embedding_inr -> openEmbedding_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], OpenEmbedding.{u2, max u1 u2} β (Sum.{u1, u2} α β) _inst_2 (Sum.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Sum.inr.{u1, u2} α β)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], OpenEmbedding.{u2, max u1 u2} β (Sum.{u1, u2} α β) _inst_2 (instTopologicalSpaceSum.{u1, u2} α β _inst_1 _inst_2) (Sum.inr.{u1, u2} α β)
Case conversion may be inaccurate. Consider using '#align open_embedding_inr openEmbedding_inrₓ'. -/
theorem openEmbedding_inr : OpenEmbedding (@inr α β) :=
  openEmbedding_of_continuous_injective_open continuous_inr inr_injective isOpenMap_inr
#align open_embedding_inr openEmbedding_inr

/- warning: embedding_inl -> embedding_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], Embedding.{u1, max u1 u2} α (Sum.{u1, u2} α β) _inst_1 (Sum.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Sum.inl.{u1, u2} α β)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], Embedding.{u1, max u1 u2} α (Sum.{u1, u2} α β) _inst_1 (instTopologicalSpaceSum.{u1, u2} α β _inst_1 _inst_2) (Sum.inl.{u1, u2} α β)
Case conversion may be inaccurate. Consider using '#align embedding_inl embedding_inlₓ'. -/
theorem embedding_inl : Embedding (@inl α β) :=
  openEmbedding_inl.1
#align embedding_inl embedding_inl

/- warning: embedding_inr -> embedding_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], Embedding.{u2, max u1 u2} β (Sum.{u1, u2} α β) _inst_2 (Sum.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Sum.inr.{u1, u2} α β)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], Embedding.{u2, max u1 u2} β (Sum.{u1, u2} α β) _inst_2 (instTopologicalSpaceSum.{u1, u2} α β _inst_1 _inst_2) (Sum.inr.{u1, u2} α β)
Case conversion may be inaccurate. Consider using '#align embedding_inr embedding_inrₓ'. -/
theorem embedding_inr : Embedding (@inr α β) :=
  openEmbedding_inr.1
#align embedding_inr embedding_inr

/- warning: is_open_range_inl -> isOpen_range_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], IsOpen.{max u1 u2} (Sum.{u1, u2} α β) (Sum.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Set.range.{max u1 u2, succ u1} (Sum.{u1, u2} α β) α (Sum.inl.{u1, u2} α β))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], IsOpen.{max u1 u2} (Sum.{u1, u2} α β) (instTopologicalSpaceSum.{u1, u2} α β _inst_1 _inst_2) (Set.range.{max u1 u2, succ u1} (Sum.{u1, u2} α β) α (Sum.inl.{u1, u2} α β))
Case conversion may be inaccurate. Consider using '#align is_open_range_inl isOpen_range_inlₓ'. -/
theorem isOpen_range_inl : IsOpen (range (inl : α → Sum α β)) :=
  openEmbedding_inl.2
#align is_open_range_inl isOpen_range_inl

/- warning: is_open_range_inr -> isOpen_range_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], IsOpen.{max u1 u2} (Sum.{u1, u2} α β) (Sum.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Set.range.{max u1 u2, succ u2} (Sum.{u1, u2} α β) β (Sum.inr.{u1, u2} α β))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], IsOpen.{max u1 u2} (Sum.{u1, u2} α β) (instTopologicalSpaceSum.{u1, u2} α β _inst_1 _inst_2) (Set.range.{max u1 u2, succ u2} (Sum.{u1, u2} α β) β (Sum.inr.{u1, u2} α β))
Case conversion may be inaccurate. Consider using '#align is_open_range_inr isOpen_range_inrₓ'. -/
theorem isOpen_range_inr : IsOpen (range (inr : β → Sum α β)) :=
  openEmbedding_inr.2
#align is_open_range_inr isOpen_range_inr

/- warning: is_closed_range_inl -> isClosed_range_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], IsClosed.{max u1 u2} (Sum.{u1, u2} α β) (Sum.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Set.range.{max u1 u2, succ u1} (Sum.{u1, u2} α β) α (Sum.inl.{u1, u2} α β))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], IsClosed.{max u1 u2} (Sum.{u1, u2} α β) (instTopologicalSpaceSum.{u1, u2} α β _inst_1 _inst_2) (Set.range.{max u1 u2, succ u1} (Sum.{u1, u2} α β) α (Sum.inl.{u1, u2} α β))
Case conversion may be inaccurate. Consider using '#align is_closed_range_inl isClosed_range_inlₓ'. -/
theorem isClosed_range_inl : IsClosed (range (inl : α → Sum α β)) :=
  by
  rw [← isOpen_compl_iff, compl_range_inl]
  exact isOpen_range_inr
#align is_closed_range_inl isClosed_range_inl

/- warning: is_closed_range_inr -> isClosed_range_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], IsClosed.{max u1 u2} (Sum.{u1, u2} α β) (Sum.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Set.range.{max u1 u2, succ u2} (Sum.{u1, u2} α β) β (Sum.inr.{u1, u2} α β))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], IsClosed.{max u1 u2} (Sum.{u1, u2} α β) (instTopologicalSpaceSum.{u1, u2} α β _inst_1 _inst_2) (Set.range.{max u1 u2, succ u2} (Sum.{u1, u2} α β) β (Sum.inr.{u1, u2} α β))
Case conversion may be inaccurate. Consider using '#align is_closed_range_inr isClosed_range_inrₓ'. -/
theorem isClosed_range_inr : IsClosed (range (inr : β → Sum α β)) :=
  by
  rw [← isOpen_compl_iff, compl_range_inr]
  exact isOpen_range_inl
#align is_closed_range_inr isClosed_range_inr

/- warning: closed_embedding_inl -> closedEmbedding_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], ClosedEmbedding.{u1, max u1 u2} α (Sum.{u1, u2} α β) _inst_1 (Sum.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Sum.inl.{u1, u2} α β)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], ClosedEmbedding.{u1, max u1 u2} α (Sum.{u1, u2} α β) _inst_1 (instTopologicalSpaceSum.{u1, u2} α β _inst_1 _inst_2) (Sum.inl.{u1, u2} α β)
Case conversion may be inaccurate. Consider using '#align closed_embedding_inl closedEmbedding_inlₓ'. -/
theorem closedEmbedding_inl : ClosedEmbedding (inl : α → Sum α β) :=
  ⟨embedding_inl, isClosed_range_inl⟩
#align closed_embedding_inl closedEmbedding_inl

/- warning: closed_embedding_inr -> closedEmbedding_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], ClosedEmbedding.{u2, max u1 u2} β (Sum.{u1, u2} α β) _inst_2 (Sum.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Sum.inr.{u1, u2} α β)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], ClosedEmbedding.{u2, max u1 u2} β (Sum.{u1, u2} α β) _inst_2 (instTopologicalSpaceSum.{u1, u2} α β _inst_1 _inst_2) (Sum.inr.{u1, u2} α β)
Case conversion may be inaccurate. Consider using '#align closed_embedding_inr closedEmbedding_inrₓ'. -/
theorem closedEmbedding_inr : ClosedEmbedding (inr : β → Sum α β) :=
  ⟨embedding_inr, isClosed_range_inr⟩
#align closed_embedding_inr closedEmbedding_inr

/- warning: nhds_inl -> nhds_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (x : α), Eq.{succ (max u1 u2)} (Filter.{max u1 u2} (Sum.{u1, u2} α β)) (nhds.{max u1 u2} (Sum.{u1, u2} α β) (Sum.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Sum.inl.{u1, u2} α β x)) (Filter.map.{u1, max u1 u2} α (Sum.{u1, u2} α β) (Sum.inl.{u1, u2} α β) (nhds.{u1} α _inst_1 x))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (x : α), Eq.{max (succ u1) (succ u2)} (Filter.{max u1 u2} (Sum.{u1, u2} α β)) (nhds.{max u1 u2} (Sum.{u1, u2} α β) (instTopologicalSpaceSum.{u1, u2} α β _inst_1 _inst_2) (Sum.inl.{u1, u2} α β x)) (Filter.map.{u1, max u2 u1} α (Sum.{u1, u2} α β) (Sum.inl.{u1, u2} α β) (nhds.{u1} α _inst_1 x))
Case conversion may be inaccurate. Consider using '#align nhds_inl nhds_inlₓ'. -/
theorem nhds_inl (x : α) : 𝓝 (inl x : Sum α β) = map inl (𝓝 x) :=
  (openEmbedding_inl.map_nhds_eq _).symm
#align nhds_inl nhds_inl

/- warning: nhds_inr -> nhds_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (x : β), Eq.{succ (max u1 u2)} (Filter.{max u1 u2} (Sum.{u1, u2} α β)) (nhds.{max u1 u2} (Sum.{u1, u2} α β) (Sum.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Sum.inr.{u1, u2} α β x)) (Filter.map.{u2, max u1 u2} β (Sum.{u1, u2} α β) (Sum.inr.{u1, u2} α β) (nhds.{u2} β _inst_2 x))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (x : β), Eq.{max (succ u1) (succ u2)} (Filter.{max u1 u2} (Sum.{u1, u2} α β)) (nhds.{max u1 u2} (Sum.{u1, u2} α β) (instTopologicalSpaceSum.{u1, u2} α β _inst_1 _inst_2) (Sum.inr.{u1, u2} α β x)) (Filter.map.{u2, max u2 u1} β (Sum.{u1, u2} α β) (Sum.inr.{u1, u2} α β) (nhds.{u2} β _inst_2 x))
Case conversion may be inaccurate. Consider using '#align nhds_inr nhds_inrₓ'. -/
theorem nhds_inr (x : β) : 𝓝 (inr x : Sum α β) = map inr (𝓝 x) :=
  (openEmbedding_inr.map_nhds_eq _).symm
#align nhds_inr nhds_inr

/- warning: continuous_sum_elim -> continuous_sum_elim is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {f : α -> γ} {g : β -> γ}, Iff (Continuous.{max u1 u2, u3} (Sum.{u1, u2} α β) γ (Sum.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3 (Sum.elim.{u1, u2, succ u3} α β γ f g)) (And (Continuous.{u1, u3} α γ _inst_1 _inst_3 f) (Continuous.{u2, u3} β γ _inst_2 _inst_3 g))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u1} γ] {f : α -> γ} {g : β -> γ}, Iff (Continuous.{max u3 u2, u1} (Sum.{u2, u3} α β) γ (instTopologicalSpaceSum.{u2, u3} α β _inst_1 _inst_2) _inst_3 (Sum.elim.{u2, u3, succ u1} α β γ f g)) (And (Continuous.{u2, u1} α γ _inst_1 _inst_3 f) (Continuous.{u3, u1} β γ _inst_2 _inst_3 g))
Case conversion may be inaccurate. Consider using '#align continuous_sum_elim continuous_sum_elimₓ'. -/
theorem continuous_sum_elim {f : α → γ} {g : β → γ} :
    Continuous (Sum.elim f g) ↔ Continuous f ∧ Continuous g := by
  simp only [continuous_sup_dom, continuous_coinduced_dom, Sum.elim_comp_inl, Sum.elim_comp_inr]
#align continuous_sum_elim continuous_sum_elim

/- warning: continuous.sum_elim -> Continuous.sum_elim is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {f : α -> γ} {g : β -> γ}, (Continuous.{u1, u3} α γ _inst_1 _inst_3 f) -> (Continuous.{u2, u3} β γ _inst_2 _inst_3 g) -> (Continuous.{max u1 u2, u3} (Sum.{u1, u2} α β) γ (Sum.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3 (Sum.elim.{u1, u2, succ u3} α β γ f g))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u1} γ] {f : α -> γ} {g : β -> γ}, (Continuous.{u2, u1} α γ _inst_1 _inst_3 f) -> (Continuous.{u3, u1} β γ _inst_2 _inst_3 g) -> (Continuous.{max u3 u2, u1} (Sum.{u2, u3} α β) γ (instTopologicalSpaceSum.{u2, u3} α β _inst_1 _inst_2) _inst_3 (Sum.elim.{u2, u3, succ u1} α β γ f g))
Case conversion may be inaccurate. Consider using '#align continuous.sum_elim Continuous.sum_elimₓ'. -/
@[continuity]
theorem Continuous.sum_elim {f : α → γ} {g : β → γ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (Sum.elim f g) :=
  continuous_sum_elim.2 ⟨hf, hg⟩
#align continuous.sum_elim Continuous.sum_elim

/- warning: continuous_sum_map -> continuous_sum_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] {f : α -> β} {g : γ -> δ}, Iff (Continuous.{max u1 u3, max u2 u4} (Sum.{u1, u3} α γ) (Sum.{u2, u4} β δ) (Sum.topologicalSpace.{u1, u3} α γ _inst_1 _inst_3) (Sum.topologicalSpace.{u2, u4} β δ _inst_2 _inst_4) (Sum.map.{u1, u3, u2, u4} α β γ δ f g)) (And (Continuous.{u1, u2} α β _inst_1 _inst_2 f) (Continuous.{u3, u4} γ δ _inst_3 _inst_4 g))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {γ : Type.{u2}} {δ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u4} β] [_inst_3 : TopologicalSpace.{u2} γ] [_inst_4 : TopologicalSpace.{u1} δ] {f : α -> β} {g : γ -> δ}, Iff (Continuous.{max u2 u3, max u1 u4} (Sum.{u3, u2} α γ) (Sum.{u4, u1} β δ) (instTopologicalSpaceSum.{u3, u2} α γ _inst_1 _inst_3) (instTopologicalSpaceSum.{u4, u1} β δ _inst_2 _inst_4) (Sum.map.{u3, u2, u4, u1} α β γ δ f g)) (And (Continuous.{u3, u4} α β _inst_1 _inst_2 f) (Continuous.{u2, u1} γ δ _inst_3 _inst_4 g))
Case conversion may be inaccurate. Consider using '#align continuous_sum_map continuous_sum_mapₓ'. -/
@[simp]
theorem continuous_sum_map {f : α → β} {g : γ → δ} :
    Continuous (Sum.map f g) ↔ Continuous f ∧ Continuous g :=
  continuous_sum_elim.trans <|
    embedding_inl.continuous_iff.symm.And embedding_inr.continuous_iff.symm
#align continuous_sum_map continuous_sum_map

/- warning: continuous.sum_map -> Continuous.sum_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] {f : α -> β} {g : γ -> δ}, (Continuous.{u1, u2} α β _inst_1 _inst_2 f) -> (Continuous.{u3, u4} γ δ _inst_3 _inst_4 g) -> (Continuous.{max u1 u3, max u2 u4} (Sum.{u1, u3} α γ) (Sum.{u2, u4} β δ) (Sum.topologicalSpace.{u1, u3} α γ _inst_1 _inst_3) (Sum.topologicalSpace.{u2, u4} β δ _inst_2 _inst_4) (Sum.map.{u1, u3, u2, u4} α β γ δ f g))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {γ : Type.{u2}} {δ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u4} β] [_inst_3 : TopologicalSpace.{u2} γ] [_inst_4 : TopologicalSpace.{u1} δ] {f : α -> β} {g : γ -> δ}, (Continuous.{u3, u4} α β _inst_1 _inst_2 f) -> (Continuous.{u2, u1} γ δ _inst_3 _inst_4 g) -> (Continuous.{max u2 u3, max u1 u4} (Sum.{u3, u2} α γ) (Sum.{u4, u1} β δ) (instTopologicalSpaceSum.{u3, u2} α γ _inst_1 _inst_3) (instTopologicalSpaceSum.{u4, u1} β δ _inst_2 _inst_4) (Sum.map.{u3, u2, u4, u1} α β γ δ f g))
Case conversion may be inaccurate. Consider using '#align continuous.sum_map Continuous.sum_mapₓ'. -/
@[continuity]
theorem Continuous.sum_map {f : α → β} {g : γ → δ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (Sum.map f g) :=
  continuous_sum_map.2 ⟨hf, hg⟩
#align continuous.sum_map Continuous.sum_map

/- warning: is_open_map_sum -> isOpenMap_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {f : (Sum.{u1, u2} α β) -> γ}, Iff (IsOpenMap.{max u1 u2, u3} (Sum.{u1, u2} α β) γ (Sum.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3 f) (And (IsOpenMap.{u1, u3} α γ _inst_1 _inst_3 (fun (a : α) => f (Sum.inl.{u1, u2} α β a))) (IsOpenMap.{u2, u3} β γ _inst_2 _inst_3 (fun (b : β) => f (Sum.inr.{u1, u2} α β b))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u1} γ] {f : (Sum.{u2, u3} α β) -> γ}, Iff (IsOpenMap.{max u2 u3, u1} (Sum.{u2, u3} α β) γ (instTopologicalSpaceSum.{u2, u3} α β _inst_1 _inst_2) _inst_3 f) (And (IsOpenMap.{u2, u1} α γ _inst_1 _inst_3 (fun (a : α) => f (Sum.inl.{u2, u3} α β a))) (IsOpenMap.{u3, u1} β γ _inst_2 _inst_3 (fun (b : β) => f (Sum.inr.{u2, u3} α β b))))
Case conversion may be inaccurate. Consider using '#align is_open_map_sum isOpenMap_sumₓ'. -/
theorem isOpenMap_sum {f : Sum α β → γ} :
    IsOpenMap f ↔ (IsOpenMap fun a => f (inl a)) ∧ IsOpenMap fun b => f (inr b) := by
  simp only [isOpenMap_iff_nhds_le, Sum.forall, nhds_inl, nhds_inr, Filter.map_map]
#align is_open_map_sum isOpenMap_sum

/- warning: is_open_map_sum_elim -> isOpenMap_sum_elim is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {f : α -> γ} {g : β -> γ}, Iff (IsOpenMap.{max u1 u2, u3} (Sum.{u1, u2} α β) γ (Sum.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3 (Sum.elim.{u1, u2, succ u3} α β γ f g)) (And (IsOpenMap.{u1, u3} α γ _inst_1 _inst_3 f) (IsOpenMap.{u2, u3} β γ _inst_2 _inst_3 g))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u1} γ] {f : α -> γ} {g : β -> γ}, Iff (IsOpenMap.{max u3 u2, u1} (Sum.{u2, u3} α β) γ (instTopologicalSpaceSum.{u2, u3} α β _inst_1 _inst_2) _inst_3 (Sum.elim.{u2, u3, succ u1} α β γ f g)) (And (IsOpenMap.{u2, u1} α γ _inst_1 _inst_3 f) (IsOpenMap.{u3, u1} β γ _inst_2 _inst_3 g))
Case conversion may be inaccurate. Consider using '#align is_open_map_sum_elim isOpenMap_sum_elimₓ'. -/
@[simp]
theorem isOpenMap_sum_elim {f : α → γ} {g : β → γ} :
    IsOpenMap (Sum.elim f g) ↔ IsOpenMap f ∧ IsOpenMap g := by
  simp only [isOpenMap_sum, elim_inl, elim_inr]
#align is_open_map_sum_elim isOpenMap_sum_elim

/- warning: is_open_map.sum_elim -> IsOpenMap.sum_elim is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {f : α -> γ} {g : β -> γ}, (IsOpenMap.{u1, u3} α γ _inst_1 _inst_3 f) -> (IsOpenMap.{u2, u3} β γ _inst_2 _inst_3 g) -> (IsOpenMap.{max u1 u2, u3} (Sum.{u1, u2} α β) γ (Sum.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3 (Sum.elim.{u1, u2, succ u3} α β γ f g))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u1} γ] {f : α -> γ} {g : β -> γ}, (IsOpenMap.{u2, u1} α γ _inst_1 _inst_3 f) -> (IsOpenMap.{u3, u1} β γ _inst_2 _inst_3 g) -> (IsOpenMap.{max u3 u2, u1} (Sum.{u2, u3} α β) γ (instTopologicalSpaceSum.{u2, u3} α β _inst_1 _inst_2) _inst_3 (Sum.elim.{u2, u3, succ u1} α β γ f g))
Case conversion may be inaccurate. Consider using '#align is_open_map.sum_elim IsOpenMap.sum_elimₓ'. -/
theorem IsOpenMap.sum_elim {f : α → γ} {g : β → γ} (hf : IsOpenMap f) (hg : IsOpenMap g) :
    IsOpenMap (Sum.elim f g) :=
  isOpenMap_sum_elim.2 ⟨hf, hg⟩
#align is_open_map.sum_elim IsOpenMap.sum_elim

end Sum

section Subtype

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] {p : α → Prop}

#print inducing_subtype_val /-
theorem inducing_subtype_val {b : Set β} : Inducing (coe : b → β) :=
  ⟨rfl⟩
#align inducing_coe inducing_subtype_val
-/

#print Inducing.of_codRestrict /-
theorem Inducing.of_codRestrict {f : α → β} {b : Set β} (hb : ∀ a, f a ∈ b)
    (h : Inducing (b.codRestrict f hb)) : Inducing f :=
  inducing_subtype_val.comp h
#align inducing.of_cod_restrict Inducing.of_codRestrict
-/

#print embedding_subtype_val /-
theorem embedding_subtype_val : Embedding (coe : Subtype p → α) :=
  ⟨⟨rfl⟩, Subtype.coe_injective⟩
#align embedding_subtype_coe embedding_subtype_val
-/

#print closedEmbedding_subtype_val /-
theorem closedEmbedding_subtype_val (h : IsClosed { a | p a }) :
    ClosedEmbedding (coe : Subtype p → α) :=
  ⟨embedding_subtype_val, by rwa [Subtype.range_coe_subtype]⟩
#align closed_embedding_subtype_coe closedEmbedding_subtype_val
-/

#print continuous_subtype_val /-
@[continuity]
theorem continuous_subtype_val : Continuous (@Subtype.val α p) :=
  continuous_induced_dom
#align continuous_subtype_val continuous_subtype_val
-/

/- warning: continuous_subtype_coe clashes with continuous_subtype_val -> continuous_subtype_val
Case conversion may be inaccurate. Consider using '#align continuous_subtype_coe continuous_subtype_valₓ'. -/
#print continuous_subtype_val /-
theorem continuous_subtype_val : Continuous (coe : Subtype p → α) :=
  continuous_subtype_val
#align continuous_subtype_coe continuous_subtype_val
-/

#print Continuous.subtype_val /-
theorem Continuous.subtype_val {f : β → Subtype p} (hf : Continuous f) :
    Continuous fun x => (f x : α) :=
  continuous_subtype_val.comp hf
#align continuous.subtype_coe Continuous.subtype_val
-/

#print IsOpen.openEmbedding_subtype_val /-
theorem IsOpen.openEmbedding_subtype_val {s : Set α} (hs : IsOpen s) :
    OpenEmbedding (coe : s → α) :=
  { induced := rfl
    inj := Subtype.coe_injective
    open_range := (Subtype.range_coe : range coe = s).symm ▸ hs }
#align is_open.open_embedding_subtype_coe IsOpen.openEmbedding_subtype_val
-/

#print IsOpen.isOpenMap_subtype_val /-
theorem IsOpen.isOpenMap_subtype_val {s : Set α} (hs : IsOpen s) : IsOpenMap (coe : s → α) :=
  hs.openEmbedding_subtype_val.IsOpenMap
#align is_open.is_open_map_subtype_coe IsOpen.isOpenMap_subtype_val
-/

#print IsOpenMap.restrict /-
theorem IsOpenMap.restrict {f : α → β} (hf : IsOpenMap f) {s : Set α} (hs : IsOpen s) :
    IsOpenMap (s.restrict f) :=
  hf.comp hs.isOpenMap_subtype_val
#align is_open_map.restrict IsOpenMap.restrict
-/

#print IsClosed.closedEmbedding_subtype_val /-
theorem IsClosed.closedEmbedding_subtype_val {s : Set α} (hs : IsClosed s) :
    ClosedEmbedding (coe : { x // x ∈ s } → α) :=
  { induced := rfl
    inj := Subtype.coe_injective
    closed_range := (Subtype.range_coe : range coe = s).symm ▸ hs }
#align is_closed.closed_embedding_subtype_coe IsClosed.closedEmbedding_subtype_val
-/

#print Continuous.subtype_mk /-
@[continuity]
theorem Continuous.subtype_mk {f : β → α} (h : Continuous f) (hp : ∀ x, p (f x)) :
    Continuous fun x => (⟨f x, hp x⟩ : Subtype p) :=
  continuous_induced_rng.2 h
#align continuous.subtype_mk Continuous.subtype_mk
-/

#print Continuous.subtype_map /-
theorem Continuous.subtype_map {f : α → β} (h : Continuous f) {q : β → Prop}
    (hpq : ∀ x, p x → q (f x)) : Continuous (Subtype.map f hpq) :=
  (h.comp continuous_subtype_val).subtype_mk _
#align continuous.subtype_map Continuous.subtype_map
-/

#print continuous_inclusion /-
theorem continuous_inclusion {s t : Set α} (h : s ⊆ t) : Continuous (inclusion h) :=
  continuous_id.subtypeMap h
#align continuous_inclusion continuous_inclusion
-/

#print continuousAt_subtype_val /-
theorem continuousAt_subtype_val {p : α → Prop} {a : Subtype p} :
    ContinuousAt (coe : Subtype p → α) a :=
  continuous_iff_continuousAt.mp continuous_subtype_val _
#align continuous_at_subtype_coe continuousAt_subtype_val
-/

#print Subtype.dense_iff /-
theorem Subtype.dense_iff {s : Set α} {t : Set s} : Dense t ↔ s ⊆ closure (coe '' t) :=
  by
  rw [inducing_coe.dense_iff, SetCoe.forall]
  rfl
#align subtype.dense_iff Subtype.dense_iff
-/

#print map_nhds_subtype_coe_eq_nhds /-
theorem map_nhds_subtype_coe_eq_nhds {a : α} (ha : p a) (h : { a | p a } ∈ 𝓝 a) :
    map (coe : Subtype p → α) (𝓝 ⟨a, ha⟩) = 𝓝 a :=
  map_nhds_induced_of_mem <| by simpa only [Subtype.coe_mk, Subtype.range_coe] using h
#align map_nhds_subtype_coe_eq map_nhds_subtype_coe_eq_nhds
-/

#print nhds_subtype_eq_comap /-
theorem nhds_subtype_eq_comap {a : α} {h : p a} : 𝓝 (⟨a, h⟩ : Subtype p) = comap coe (𝓝 a) :=
  nhds_induced _ _
#align nhds_subtype_eq_comap nhds_subtype_eq_comap
-/

/- warning: tendsto_subtype_rng -> tendsto_subtype_rng is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} {p : α -> Prop} {b : Filter.{u2} β} {f : β -> (Subtype.{succ u1} α p)} {a : Subtype.{succ u1} α p}, Iff (Filter.Tendsto.{u2, u1} β (Subtype.{succ u1} α p) f b (nhds.{u1} (Subtype.{succ u1} α p) (Subtype.topologicalSpace.{u1} α p _inst_1) a)) (Filter.Tendsto.{u2, u1} β α (fun (x : β) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α p) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α p) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α p) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α p) α (coeSubtype.{succ u1} α (fun (x : α) => p x))))) (f x)) b (nhds.{u1} α _inst_1 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α p) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α p) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α p) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α p) α (coeSubtype.{succ u1} α (fun (x : α) => p x))))) a)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} {p : α -> Prop} {b : Filter.{u1} β} {f : β -> (Subtype.{succ u2} α p)} {a : Subtype.{succ u2} α p}, Iff (Filter.Tendsto.{u1, u2} β (Subtype.{succ u2} α p) f b (nhds.{u2} (Subtype.{succ u2} α p) (instTopologicalSpaceSubtype.{u2} α p _inst_1) a)) (Filter.Tendsto.{u1, u2} β α (fun (x : β) => Subtype.val.{succ u2} α p (f x)) b (nhds.{u2} α _inst_1 (Subtype.val.{succ u2} α p a)))
Case conversion may be inaccurate. Consider using '#align tendsto_subtype_rng tendsto_subtype_rngₓ'. -/
theorem tendsto_subtype_rng {β : Type _} {p : α → Prop} {b : Filter β} {f : β → Subtype p} :
    ∀ {a : Subtype p}, Tendsto f b (𝓝 a) ↔ Tendsto (fun x => (f x : α)) b (𝓝 (a : α))
  | ⟨a, ha⟩ => by rw [nhds_subtype_eq_comap, tendsto_comap_iff, Subtype.coe_mk]
#align tendsto_subtype_rng tendsto_subtype_rng

/- warning: continuous_subtype_nhds_cover -> continuous_subtype_nhds_cover is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {ι : Sort.{u3}} {f : α -> β} {c : ι -> α -> Prop}, (forall (x : α), Exists.{u3} ι (fun (i : ι) => Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (setOf.{u1} α (fun (x : α) => c i x)) (nhds.{u1} α _inst_1 x))) -> (forall (i : ι), Continuous.{u1, u2} (Subtype.{succ u1} α (c i)) β (Subtype.topologicalSpace.{u1} α (c i) _inst_1) _inst_2 (fun (x : Subtype.{succ u1} α (c i)) => f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (c i)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (c i)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (c i)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (c i)) α (coeSubtype.{succ u1} α (fun (x : α) => c i x))))) x))) -> (Continuous.{u1, u2} α β _inst_1 _inst_2 f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u3} β] {ι : Sort.{u1}} {f : α -> β} {c : ι -> α -> Prop}, (forall (x : α), Exists.{u1} ι (fun (i : ι) => Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) (setOf.{u2} α (fun (x : α) => c i x)) (nhds.{u2} α _inst_1 x))) -> (forall (i : ι), Continuous.{u2, u3} (Subtype.{succ u2} α (c i)) β (instTopologicalSpaceSubtype.{u2} α (c i) _inst_1) _inst_2 (fun (x : Subtype.{succ u2} α (c i)) => f (Subtype.val.{succ u2} α (c i) x))) -> (Continuous.{u2, u3} α β _inst_1 _inst_2 f)
Case conversion may be inaccurate. Consider using '#align continuous_subtype_nhds_cover continuous_subtype_nhds_coverₓ'. -/
theorem continuous_subtype_nhds_cover {ι : Sort _} {f : α → β} {c : ι → α → Prop}
    (c_cover : ∀ x : α, ∃ i, { x | c i x } ∈ 𝓝 x)
    (f_cont : ∀ i, Continuous fun x : Subtype (c i) => f x) : Continuous f :=
  continuous_iff_continuousAt.mpr fun x =>
    let ⟨i, (c_sets : { x | c i x } ∈ 𝓝 x)⟩ := c_cover x
    let x' : Subtype (c i) := ⟨x, mem_of_mem_nhds c_sets⟩
    calc
      map f (𝓝 x) = map f (map coe (𝓝 x')) :=
        congr_arg (map f) (map_nhds_subtype_coe_eq_nhds _ <| c_sets).symm
      _ = map (fun x : Subtype (c i) => f x) (𝓝 x') := rfl
      _ ≤ 𝓝 (f x) := continuous_iff_continuousAt.mp (f_cont i) x'
      
#align continuous_subtype_nhds_cover continuous_subtype_nhds_cover

/- warning: continuous_subtype_is_closed_cover clashes with [anonymous] -> [anonymous]
warning: continuous_subtype_is_closed_cover -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} [_inst_1 : TopologicalSpace.{u} α] [_inst_2 : TopologicalSpace.{v} β] {ι : Type.{u_1}} {f : α -> β} (c : ι -> α -> Prop), (LocallyFinite.{u_1, u} ι α _inst_1 (fun (i : ι) => setOf.{u} α (fun (x : α) => c i x))) -> (forall (i : ι), IsClosed.{u} α _inst_1 (setOf.{u} α (fun (x : α) => c i x))) -> (forall (x : α), Exists.{succ u_1} ι (fun (i : ι) => c i x)) -> (forall (i : ι), Continuous.{u, v} (Subtype.{succ u} α (c i)) β (Subtype.topologicalSpace.{u} α (c i) _inst_1) _inst_2 (fun (x : Subtype.{succ u} α (c i)) => f ((fun (a : Sort.{max 1 (succ u)}) (b : Type.{u}) [self : HasLiftT.{max 1 (succ u), succ u} a b] => self.0) (Subtype.{succ u} α (c i)) α (HasLiftT.mk.{max 1 (succ u), succ u} (Subtype.{succ u} α (c i)) α (CoeTCₓ.coe.{max 1 (succ u), succ u} (Subtype.{succ u} α (c i)) α (coeBase.{max 1 (succ u), succ u} (Subtype.{succ u} α (c i)) α (coeSubtype.{succ u} α (fun (x : α) => c i x))))) x))) -> (Continuous.{u, v} α β _inst_1 _inst_2 f)
but is expected to have type
  forall {α : Type.{u}} {β : Type.{v}}, (Nat -> α -> β) -> Nat -> (List.{u} α) -> (List.{v} β)
Case conversion may be inaccurate. Consider using '#align continuous_subtype_is_closed_cover [anonymous]ₓ'. -/
theorem [anonymous] {ι : Sort _} {f : α → β} (c : ι → α → Prop)
    (h_lf : LocallyFinite fun i => { x | c i x }) (h_is_closed : ∀ i, IsClosed { x | c i x })
    (h_cover : ∀ x, ∃ i, c i x) (f_cont : ∀ i, Continuous fun x : Subtype (c i) => f x) :
    Continuous f :=
  continuous_iff_isClosed.mpr fun s hs =>
    by
    have : ∀ i, IsClosed ((coe : { x | c i x } → α) '' (f ∘ coe ⁻¹' s)) := fun i =>
      (closedEmbedding_subtype_val (h_is_closed _)).IsClosedMap _ (hs.Preimage (f_cont i))
    have : IsClosed (⋃ i, (coe : { x | c i x } → α) '' (f ∘ coe ⁻¹' s)) :=
      LocallyFinite.isClosed_unionᵢ (h_lf.Subset fun i x ⟨⟨x', hx'⟩, _, HEq⟩ => HEq ▸ hx') this
    have : f ⁻¹' s = ⋃ i, (coe : { x | c i x } → α) '' (f ∘ coe ⁻¹' s) :=
      by
      apply Set.ext
      have : ∀ x : α, f x ∈ s ↔ ∃ i : ι, c i x ∧ f x ∈ s := fun x =>
        ⟨fun hx =>
          let ⟨i, hi⟩ := h_cover x
          ⟨i, hi, hx⟩,
          fun ⟨i, hi, hx⟩ => hx⟩
      simpa [and_comm, @and_left_comm (c _ _), ← exists_and_right]
    rwa [this]
#align continuous_subtype_is_closed_cover [anonymous]

#print closure_subtype /-
theorem closure_subtype {x : { a // p a }} {s : Set { a // p a }} :
    x ∈ closure s ↔ (x : α) ∈ closure ((coe : _ → α) '' s) :=
  closure_induced
#align closure_subtype closure_subtype
-/

#print continuousAt_codRestrict_iff /-
theorem continuousAt_codRestrict_iff {f : α → β} {t : Set β} (h1 : ∀ x, f x ∈ t) {x : α} :
    ContinuousAt (codRestrict f t h1) x ↔ ContinuousAt f x := by
  simp_rw [inducing_coe.continuous_at_iff, Function.comp, coe_cod_restrict_apply]
#align continuous_at_cod_restrict_iff continuousAt_codRestrict_iff
-/

alias continuousAt_codRestrict_iff ↔ _ ContinuousAt.codRestrict
#align continuous_at.cod_restrict ContinuousAt.codRestrict

#print ContinuousAt.restrict /-
theorem ContinuousAt.restrict {f : α → β} {s : Set α} {t : Set β} (h1 : MapsTo f s t) {x : s}
    (h2 : ContinuousAt f x) : ContinuousAt (h1.restrict f s t) x :=
  (h2.comp continuousAt_subtype_val).codRestrict _
#align continuous_at.restrict ContinuousAt.restrict
-/

#print ContinuousAt.restrictPreimage /-
theorem ContinuousAt.restrictPreimage {f : α → β} {s : Set β} {x : f ⁻¹' s} (h : ContinuousAt f x) :
    ContinuousAt (s.restrictPreimage f) x :=
  h.restrict _
#align continuous_at.restrict_preimage ContinuousAt.restrictPreimage
-/

#print Continuous.codRestrict /-
@[continuity]
theorem Continuous.codRestrict {f : α → β} {s : Set β} (hf : Continuous f) (hs : ∀ a, f a ∈ s) :
    Continuous (s.codRestrict f hs) :=
  hf.subtype_mk hs
#align continuous.cod_restrict Continuous.codRestrict
-/

#print Inducing.codRestrict /-
theorem Inducing.codRestrict {e : α → β} (he : Inducing e) {s : Set β} (hs : ∀ x, e x ∈ s) :
    Inducing (codRestrict e s hs) :=
  inducing_of_inducing_compose (he.Continuous.codRestrict hs) continuous_subtype_val he
#align inducing.cod_restrict Inducing.codRestrict
-/

#print Embedding.codRestrict /-
theorem Embedding.codRestrict {e : α → β} (he : Embedding e) (s : Set β) (hs : ∀ x, e x ∈ s) :
    Embedding (codRestrict e s hs) :=
  embedding_of_embedding_compose (he.Continuous.codRestrict hs) continuous_subtype_val he
#align embedding.cod_restrict Embedding.codRestrict
-/

#print embedding_inclusion /-
theorem embedding_inclusion {s t : Set α} (h : s ⊆ t) : Embedding (Set.inclusion h) :=
  embedding_subtype_val.codRestrict _ _
#align embedding_inclusion embedding_inclusion
-/

#print DiscreteTopology.of_subset /-
/-- Let `s, t ⊆ X` be two subsets of a topological space `X`.  If `t ⊆ s` and the topology induced
by `X`on `s` is discrete, then also the topology induces on `t` is discrete.  -/
theorem DiscreteTopology.of_subset {X : Type _} [TopologicalSpace X] {s t : Set X}
    (ds : DiscreteTopology s) (ts : t ⊆ s) : DiscreteTopology t :=
  (embedding_inclusion ts).DiscreteTopology
#align discrete_topology.of_subset DiscreteTopology.of_subset
-/

end Subtype

section Quotient

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

variable {r : α → α → Prop} {s : Setoid α}

#print quotientMap_quot_mk /-
theorem quotientMap_quot_mk : QuotientMap (@Quot.mk α r) :=
  ⟨Quot.exists_rep, rfl⟩
#align quotient_map_quot_mk quotientMap_quot_mk
-/

#print continuous_quot_mk /-
@[continuity]
theorem continuous_quot_mk : Continuous (@Quot.mk α r) :=
  continuous_coinduced_rng
#align continuous_quot_mk continuous_quot_mk
-/

#print continuous_quot_lift /-
@[continuity]
theorem continuous_quot_lift {f : α → β} (hr : ∀ a b, r a b → f a = f b) (h : Continuous f) :
    Continuous (Quot.lift f hr : Quot r → β) :=
  continuous_coinduced_dom.2 h
#align continuous_quot_lift continuous_quot_lift
-/

#print quotientMap_quotient_mk' /-
theorem quotientMap_quotient_mk' : QuotientMap (@Quotient.mk' α s) :=
  quotientMap_quot_mk
#align quotient_map_quotient_mk quotientMap_quotient_mk'
-/

#print continuous_quotient_mk' /-
theorem continuous_quotient_mk' : Continuous (@Quotient.mk' α s) :=
  continuous_coinduced_rng
#align continuous_quotient_mk continuous_quotient_mk'
-/

#print Continuous.quotient_lift /-
theorem Continuous.quotient_lift {f : α → β} (h : Continuous f) (hs : ∀ a b, a ≈ b → f a = f b) :
    Continuous (Quotient.lift f hs : Quotient s → β) :=
  continuous_coinduced_dom.2 h
#align continuous.quotient_lift Continuous.quotient_lift
-/

#print Continuous.quotient_liftOn' /-
theorem Continuous.quotient_liftOn' {f : α → β} (h : Continuous f)
    (hs : ∀ a b, @Setoid.r _ s a b → f a = f b) :
    Continuous (fun x => Quotient.liftOn' x f hs : Quotient s → β) :=
  h.quotient_lift hs
#align continuous.quotient_lift_on' Continuous.quotient_liftOn'
-/

#print Continuous.quotient_map' /-
theorem Continuous.quotient_map' {t : Setoid β} {f : α → β} (hf : Continuous f)
    (H : (s.R ⇒ t.R) f f) : Continuous (Quotient.map' f H) :=
  (continuous_quotient_mk'.comp hf).quotient_lift _
#align continuous.quotient_map' Continuous.quotient_map'
-/

end Quotient

section Pi

variable {ι : Type _} {π : ι → Type _} {κ : Type _} [TopologicalSpace α]
  [∀ i, TopologicalSpace (π i)] {f : α → ∀ i : ι, π i}

/- warning: continuous_pi_iff -> continuous_pi_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {π : ι -> Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : forall (i : ι), TopologicalSpace.{u3} (π i)] {f : α -> (forall (i : ι), π i)}, Iff (Continuous.{u1, max u2 u3} α (forall (i : ι), π i) _inst_1 (Pi.topologicalSpace.{u2, u3} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_2 a)) f) (forall (i : ι), Continuous.{u1, u3} α (π i) _inst_1 (_inst_2 i) (fun (a : α) => f a i))
but is expected to have type
  forall {α : Type.{u3}} {ι : Type.{u2}} {π : ι -> Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : forall (i : ι), TopologicalSpace.{u1} (π i)] {f : α -> (forall (i : ι), π i)}, Iff (Continuous.{u3, max u2 u1} α (forall (i : ι), π i) _inst_1 (Pi.topologicalSpace.{u2, u1} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_2 a)) f) (forall (i : ι), Continuous.{u3, u1} α (π i) _inst_1 (_inst_2 i) (fun (a : α) => f a i))
Case conversion may be inaccurate. Consider using '#align continuous_pi_iff continuous_pi_iffₓ'. -/
theorem continuous_pi_iff : Continuous f ↔ ∀ i, Continuous fun a => f a i := by
  simp only [continuous_infᵢ_rng, continuous_induced_rng]
#align continuous_pi_iff continuous_pi_iff

/- warning: continuous_pi -> continuous_pi is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {π : ι -> Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : forall (i : ι), TopologicalSpace.{u3} (π i)] {f : α -> (forall (i : ι), π i)}, (forall (i : ι), Continuous.{u1, u3} α (π i) _inst_1 (_inst_2 i) (fun (a : α) => f a i)) -> (Continuous.{u1, max u2 u3} α (forall (i : ι), π i) _inst_1 (Pi.topologicalSpace.{u2, u3} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_2 a)) f)
but is expected to have type
  forall {α : Type.{u3}} {ι : Type.{u1}} {π : ι -> Type.{u2}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : forall (i : ι), TopologicalSpace.{u2} (π i)] {f : α -> (forall (i : ι), π i)}, (forall (i : ι), Continuous.{u3, u2} α (π i) _inst_1 (_inst_2 i) (fun (a : α) => f a i)) -> (Continuous.{u3, max u1 u2} α (forall (i : ι), π i) _inst_1 (Pi.topologicalSpace.{u1, u2} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_2 a)) f)
Case conversion may be inaccurate. Consider using '#align continuous_pi continuous_piₓ'. -/
@[continuity]
theorem continuous_pi (h : ∀ i, Continuous fun a => f a i) : Continuous f :=
  continuous_pi_iff.2 h
#align continuous_pi continuous_pi

/- warning: continuous_apply -> continuous_apply is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {π : ι -> Type.{u2}} [_inst_2 : forall (i : ι), TopologicalSpace.{u2} (π i)] (i : ι), Continuous.{max u1 u2, u2} (forall (i : ι), π i) (π i) (Pi.topologicalSpace.{u1, u2} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_2 a)) (_inst_2 i) (fun (p : forall (i : ι), π i) => p i)
but is expected to have type
  forall {ι : Type.{u2}} {π : ι -> Type.{u1}} [_inst_2 : forall (i : ι), TopologicalSpace.{u1} (π i)] (i : ι), Continuous.{max u2 u1, u1} (forall (i : ι), π i) (π i) (Pi.topologicalSpace.{u2, u1} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_2 a)) (_inst_2 i) (fun (p : forall (i : ι), π i) => p i)
Case conversion may be inaccurate. Consider using '#align continuous_apply continuous_applyₓ'. -/
@[continuity]
theorem continuous_apply (i : ι) : Continuous fun p : ∀ i, π i => p i :=
  continuous_infᵢ_dom continuous_induced_dom
#align continuous_apply continuous_apply

/- warning: continuous_apply_apply -> continuous_apply_apply is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {κ : Type.{u2}} {ρ : κ -> ι -> Type.{u3}} [_inst_3 : forall (j : κ) (i : ι), TopologicalSpace.{u3} (ρ j i)] (j : κ) (i : ι), Continuous.{max u2 u1 u3, u3} (forall (j : κ) (i : ι), ρ j i) (ρ j i) (Pi.topologicalSpace.{u2, max u1 u3} κ (fun (j : κ) => forall (i : ι), ρ j i) (fun (a : κ) => Pi.topologicalSpace.{u1, u3} ι (fun (i : ι) => ρ a i) (fun (a_1 : ι) => _inst_3 a a_1))) (_inst_3 j i) (fun (p : forall (j : κ) (i : ι), ρ j i) => p j i)
but is expected to have type
  forall {ι : Type.{u2}} {κ : Type.{u1}} {ρ : κ -> ι -> Type.{u3}} [_inst_3 : forall (j : κ) (i : ι), TopologicalSpace.{u3} (ρ j i)] (j : κ) (i : ι), Continuous.{max (max u2 u1) u3, u3} (forall (j : κ) (i : ι), ρ j i) (ρ j i) (Pi.topologicalSpace.{u1, max u2 u3} κ (fun (j : κ) => forall (i : ι), ρ j i) (fun (a : κ) => Pi.topologicalSpace.{u2, u3} ι (fun (i : ι) => ρ a i) (fun (a_1 : ι) => _inst_3 a a_1))) (_inst_3 j i) (fun (p : forall (j : κ) (i : ι), ρ j i) => p j i)
Case conversion may be inaccurate. Consider using '#align continuous_apply_apply continuous_apply_applyₓ'. -/
@[continuity]
theorem continuous_apply_apply {ρ : κ → ι → Type _} [∀ j i, TopologicalSpace (ρ j i)] (j : κ)
    (i : ι) : Continuous fun p : ∀ j, ∀ i, ρ j i => p j i :=
  (continuous_apply i).comp (continuous_apply j)
#align continuous_apply_apply continuous_apply_apply

/- warning: continuous_at_apply -> continuousAt_apply is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {π : ι -> Type.{u2}} [_inst_2 : forall (i : ι), TopologicalSpace.{u2} (π i)] (i : ι) (x : forall (i : ι), π i), ContinuousAt.{max u1 u2, u2} (forall (i : ι), π i) (π i) (Pi.topologicalSpace.{u1, u2} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_2 a)) (_inst_2 i) (fun (p : forall (i : ι), π i) => p i) x
but is expected to have type
  forall {ι : Type.{u2}} {π : ι -> Type.{u1}} [_inst_2 : forall (i : ι), TopologicalSpace.{u1} (π i)] (i : ι) (x : forall (i : ι), π i), ContinuousAt.{max u2 u1, u1} (forall (i : ι), π i) (π i) (Pi.topologicalSpace.{u2, u1} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_2 a)) (_inst_2 i) (fun (p : forall (i : ι), π i) => p i) x
Case conversion may be inaccurate. Consider using '#align continuous_at_apply continuousAt_applyₓ'. -/
theorem continuousAt_apply (i : ι) (x : ∀ i, π i) : ContinuousAt (fun p : ∀ i, π i => p i) x :=
  (continuous_apply i).ContinuousAt
#align continuous_at_apply continuousAt_apply

/- warning: filter.tendsto.apply -> Filter.Tendsto.apply is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {ι : Type.{u2}} {π : ι -> Type.{u3}} [_inst_2 : forall (i : ι), TopologicalSpace.{u3} (π i)] {l : Filter.{u1} β} {f : β -> (forall (i : ι), π i)} {x : forall (i : ι), π i}, (Filter.Tendsto.{u1, max u2 u3} β (forall (i : ι), π i) f l (nhds.{max u2 u3} (forall (i : ι), π i) (Pi.topologicalSpace.{u2, u3} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_2 a)) x)) -> (forall (i : ι), Filter.Tendsto.{u1, u3} β (π i) (fun (a : β) => f a i) l (nhds.{u3} (π i) (_inst_2 i) (x i)))
but is expected to have type
  forall {β : Type.{u3}} {ι : Type.{u2}} {π : ι -> Type.{u1}} [_inst_2 : forall (i : ι), TopologicalSpace.{u1} (π i)] {l : Filter.{u3} β} {f : β -> (forall (i : ι), π i)} {x : forall (i : ι), π i}, (Filter.Tendsto.{u3, max u2 u1} β (forall (i : ι), π i) f l (nhds.{max u2 u1} (forall (i : ι), π i) (Pi.topologicalSpace.{u2, u1} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_2 a)) x)) -> (forall (i : ι), Filter.Tendsto.{u3, u1} β (π i) (fun (a : β) => f a i) l (nhds.{u1} (π i) (_inst_2 i) (x i)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.apply Filter.Tendsto.applyₓ'. -/
theorem Filter.Tendsto.apply {l : Filter β} {f : β → ∀ i, π i} {x : ∀ i, π i}
    (h : Tendsto f l (𝓝 x)) (i : ι) : Tendsto (fun a => f a i) l (𝓝 <| x i) :=
  (continuousAt_apply i _).Tendsto.comp h
#align filter.tendsto.apply Filter.Tendsto.apply

/- warning: nhds_pi -> nhds_pi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {π : ι -> Type.{u2}} [_inst_2 : forall (i : ι), TopologicalSpace.{u2} (π i)] {a : forall (i : ι), π i}, Eq.{succ (max u1 u2)} (Filter.{max u1 u2} (forall (i : ι), π i)) (nhds.{max u1 u2} (forall (i : ι), π i) (Pi.topologicalSpace.{u1, u2} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_2 a)) a) (Filter.pi.{u1, u2} ι (fun (i : ι) => π i) (fun (i : ι) => nhds.{u2} (π i) (_inst_2 i) (a i)))
but is expected to have type
  forall {ι : Type.{u2}} {π : ι -> Type.{u1}} [_inst_2 : forall (i : ι), TopologicalSpace.{u1} (π i)] {a : forall (i : ι), π i}, Eq.{max (succ u2) (succ u1)} (Filter.{max u2 u1} (forall (i : ι), π i)) (nhds.{max u2 u1} (forall (i : ι), π i) (Pi.topologicalSpace.{u2, u1} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_2 a)) a) (Filter.pi.{u2, u1} ι (fun (i : ι) => π i) (fun (i : ι) => nhds.{u1} (π i) (_inst_2 i) (a i)))
Case conversion may be inaccurate. Consider using '#align nhds_pi nhds_piₓ'. -/
theorem nhds_pi {a : ∀ i, π i} : 𝓝 a = pi fun i => 𝓝 (a i) := by
  simp only [nhds_infᵢ, nhds_induced, Filter.pi]
#align nhds_pi nhds_pi

/- warning: tendsto_pi_nhds -> tendsto_pi_nhds is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {ι : Type.{u2}} {π : ι -> Type.{u3}} [_inst_2 : forall (i : ι), TopologicalSpace.{u3} (π i)] {f : β -> (forall (i : ι), π i)} {g : forall (i : ι), π i} {u : Filter.{u1} β}, Iff (Filter.Tendsto.{u1, max u2 u3} β (forall (i : ι), π i) f u (nhds.{max u2 u3} (forall (i : ι), π i) (Pi.topologicalSpace.{u2, u3} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_2 a)) g)) (forall (x : ι), Filter.Tendsto.{u1, u3} β (π x) (fun (i : β) => f i x) u (nhds.{u3} (π x) (_inst_2 x) (g x)))
but is expected to have type
  forall {β : Type.{u3}} {ι : Type.{u2}} {π : ι -> Type.{u1}} [_inst_2 : forall (i : ι), TopologicalSpace.{u1} (π i)] {f : β -> (forall (i : ι), π i)} {g : forall (i : ι), π i} {u : Filter.{u3} β}, Iff (Filter.Tendsto.{u3, max u2 u1} β (forall (i : ι), π i) f u (nhds.{max u2 u1} (forall (i : ι), π i) (Pi.topologicalSpace.{u2, u1} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_2 a)) g)) (forall (x : ι), Filter.Tendsto.{u3, u1} β (π x) (fun (i : β) => f i x) u (nhds.{u1} (π x) (_inst_2 x) (g x)))
Case conversion may be inaccurate. Consider using '#align tendsto_pi_nhds tendsto_pi_nhdsₓ'. -/
theorem tendsto_pi_nhds {f : β → ∀ i, π i} {g : ∀ i, π i} {u : Filter β} :
    Tendsto f u (𝓝 g) ↔ ∀ x, Tendsto (fun i => f i x) u (𝓝 (g x)) := by
  rw [nhds_pi, Filter.tendsto_pi]
#align tendsto_pi_nhds tendsto_pi_nhds

/- warning: continuous_at_pi -> continuousAt_pi is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {π : ι -> Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : forall (i : ι), TopologicalSpace.{u3} (π i)] {f : α -> (forall (i : ι), π i)} {x : α}, Iff (ContinuousAt.{u1, max u2 u3} α (forall (i : ι), π i) _inst_1 (Pi.topologicalSpace.{u2, u3} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_2 a)) f x) (forall (i : ι), ContinuousAt.{u1, u3} α (π i) _inst_1 (_inst_2 i) (fun (y : α) => f y i) x)
but is expected to have type
  forall {α : Type.{u3}} {ι : Type.{u2}} {π : ι -> Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : forall (i : ι), TopologicalSpace.{u1} (π i)] {f : α -> (forall (i : ι), π i)} {x : α}, Iff (ContinuousAt.{u3, max u2 u1} α (forall (i : ι), π i) _inst_1 (Pi.topologicalSpace.{u2, u1} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_2 a)) f x) (forall (i : ι), ContinuousAt.{u3, u1} α (π i) _inst_1 (_inst_2 i) (fun (y : α) => f y i) x)
Case conversion may be inaccurate. Consider using '#align continuous_at_pi continuousAt_piₓ'. -/
theorem continuousAt_pi {f : α → ∀ i, π i} {x : α} :
    ContinuousAt f x ↔ ∀ i, ContinuousAt (fun y => f y i) x :=
  tendsto_pi_nhds
#align continuous_at_pi continuousAt_pi

/- warning: filter.tendsto.update -> Filter.Tendsto.update is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {ι : Type.{u2}} {π : ι -> Type.{u3}} [_inst_2 : forall (i : ι), TopologicalSpace.{u3} (π i)] [_inst_3 : DecidableEq.{succ u2} ι] {l : Filter.{u1} β} {f : β -> (forall (i : ι), π i)} {x : forall (i : ι), π i}, (Filter.Tendsto.{u1, max u2 u3} β (forall (i : ι), π i) f l (nhds.{max u2 u3} (forall (i : ι), π i) (Pi.topologicalSpace.{u2, u3} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_2 a)) x)) -> (forall (i : ι) {g : β -> (π i)} {xi : π i}, (Filter.Tendsto.{u1, u3} β (π i) g l (nhds.{u3} (π i) (_inst_2 i) xi)) -> (Filter.Tendsto.{u1, max u2 u3} β (forall (a : ι), π a) (fun (a : β) => Function.update.{succ u2, succ u3} ι (fun (i : ι) => π i) (fun (a : ι) (b : ι) => _inst_3 a b) (f a) i (g a)) l (nhds.{max u2 u3} (forall (a : ι), π a) (Pi.topologicalSpace.{u2, u3} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_2 a)) (Function.update.{succ u2, succ u3} ι (fun (a : ι) => π a) (fun (a : ι) (b : ι) => _inst_3 a b) x i xi))))
but is expected to have type
  forall {β : Type.{u3}} {ι : Type.{u2}} {π : ι -> Type.{u1}} [_inst_2 : forall (i : ι), TopologicalSpace.{u1} (π i)] [_inst_3 : DecidableEq.{succ u2} ι] {l : Filter.{u3} β} {f : β -> (forall (i : ι), π i)} {x : forall (i : ι), π i}, (Filter.Tendsto.{u3, max u2 u1} β (forall (i : ι), π i) f l (nhds.{max u2 u1} (forall (i : ι), π i) (Pi.topologicalSpace.{u2, u1} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_2 a)) x)) -> (forall (i : ι) {g : β -> (π i)} {xi : π i}, (Filter.Tendsto.{u3, u1} β (π i) g l (nhds.{u1} (π i) (_inst_2 i) xi)) -> (Filter.Tendsto.{u3, max u2 u1} β (forall (a : ι), π a) (fun (a : β) => Function.update.{succ u2, succ u1} ι (fun (i : ι) => π i) (fun (a : ι) (b : ι) => _inst_3 a b) (f a) i (g a)) l (nhds.{max u2 u1} (forall (a : ι), π a) (Pi.topologicalSpace.{u2, u1} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_2 a)) (Function.update.{succ u2, succ u1} ι (fun (a : ι) => π a) (fun (a : ι) (b : ι) => _inst_3 a b) x i xi))))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.update Filter.Tendsto.updateₓ'. -/
theorem Filter.Tendsto.update [DecidableEq ι] {l : Filter β} {f : β → ∀ i, π i} {x : ∀ i, π i}
    (hf : Tendsto f l (𝓝 x)) (i : ι) {g : β → π i} {xi : π i} (hg : Tendsto g l (𝓝 xi)) :
    Tendsto (fun a => update (f a) i (g a)) l (𝓝 <| update x i xi) :=
  tendsto_pi_nhds.2 fun j => by rcases em (j = i) with (rfl | hj) <;> simp [*, hf.apply]
#align filter.tendsto.update Filter.Tendsto.update

/- warning: continuous_at.update -> ContinuousAt.update is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {π : ι -> Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : forall (i : ι), TopologicalSpace.{u3} (π i)] {f : α -> (forall (i : ι), π i)} [_inst_3 : DecidableEq.{succ u2} ι] {a : α}, (ContinuousAt.{u1, max u2 u3} α (forall (i : ι), π i) _inst_1 (Pi.topologicalSpace.{u2, u3} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_2 a)) f a) -> (forall (i : ι) {g : α -> (π i)}, (ContinuousAt.{u1, u3} α (π i) _inst_1 (_inst_2 i) g a) -> (ContinuousAt.{u1, max u2 u3} α (forall (a : ι), π a) _inst_1 (Pi.topologicalSpace.{u2, u3} ι (fun (a : ι) => π a) (fun (a : ι) => _inst_2 a)) (fun (a : α) => Function.update.{succ u2, succ u3} ι (fun (i : ι) => π i) (fun (a : ι) (b : ι) => _inst_3 a b) (f a) i (g a)) a))
but is expected to have type
  forall {α : Type.{u3}} {ι : Type.{u2}} {π : ι -> Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : forall (i : ι), TopologicalSpace.{u1} (π i)] {f : α -> (forall (i : ι), π i)} [_inst_3 : DecidableEq.{succ u2} ι] {a : α}, (ContinuousAt.{u3, max u2 u1} α (forall (i : ι), π i) _inst_1 (Pi.topologicalSpace.{u2, u1} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_2 a)) f a) -> (forall (i : ι) {g : α -> (π i)}, (ContinuousAt.{u3, u1} α (π i) _inst_1 (_inst_2 i) g a) -> (ContinuousAt.{u3, max u2 u1} α (forall (a : ι), π a) _inst_1 (Pi.topologicalSpace.{u2, u1} ι (fun (a : ι) => π a) (fun (a : ι) => _inst_2 a)) (fun (a : α) => Function.update.{succ u2, succ u1} ι (fun (i : ι) => π i) (fun (a : ι) (b : ι) => _inst_3 a b) (f a) i (g a)) a))
Case conversion may be inaccurate. Consider using '#align continuous_at.update ContinuousAt.updateₓ'. -/
theorem ContinuousAt.update [DecidableEq ι] {a : α} (hf : ContinuousAt f a) (i : ι) {g : α → π i}
    (hg : ContinuousAt g a) : ContinuousAt (fun a => update (f a) i (g a)) a :=
  hf.update i hg
#align continuous_at.update ContinuousAt.update

/- warning: continuous.update -> Continuous.update is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {π : ι -> Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : forall (i : ι), TopologicalSpace.{u3} (π i)] {f : α -> (forall (i : ι), π i)} [_inst_3 : DecidableEq.{succ u2} ι], (Continuous.{u1, max u2 u3} α (forall (i : ι), π i) _inst_1 (Pi.topologicalSpace.{u2, u3} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_2 a)) f) -> (forall (i : ι) {g : α -> (π i)}, (Continuous.{u1, u3} α (π i) _inst_1 (_inst_2 i) g) -> (Continuous.{u1, max u2 u3} α (forall (a : ι), π a) _inst_1 (Pi.topologicalSpace.{u2, u3} ι (fun (a : ι) => π a) (fun (a : ι) => _inst_2 a)) (fun (a : α) => Function.update.{succ u2, succ u3} ι (fun (i : ι) => π i) (fun (a : ι) (b : ι) => _inst_3 a b) (f a) i (g a))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Type.{u2}} {π : ι -> Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : forall (i : ι), TopologicalSpace.{u1} (π i)] {f : α -> (forall (i : ι), π i)} [_inst_3 : DecidableEq.{succ u2} ι], (Continuous.{u3, max u2 u1} α (forall (i : ι), π i) _inst_1 (Pi.topologicalSpace.{u2, u1} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_2 a)) f) -> (forall (i : ι) {g : α -> (π i)}, (Continuous.{u3, u1} α (π i) _inst_1 (_inst_2 i) g) -> (Continuous.{u3, max u2 u1} α (forall (a : ι), π a) _inst_1 (Pi.topologicalSpace.{u2, u1} ι (fun (a : ι) => π a) (fun (a : ι) => _inst_2 a)) (fun (a : α) => Function.update.{succ u2, succ u1} ι (fun (i : ι) => π i) (fun (a : ι) (b : ι) => _inst_3 a b) (f a) i (g a))))
Case conversion may be inaccurate. Consider using '#align continuous.update Continuous.updateₓ'. -/
theorem Continuous.update [DecidableEq ι] (hf : Continuous f) (i : ι) {g : α → π i}
    (hg : Continuous g) : Continuous fun a => update (f a) i (g a) :=
  continuous_iff_continuousAt.2 fun x => hf.ContinuousAt.update i hg.ContinuousAt
#align continuous.update Continuous.update

/- warning: continuous_update -> continuous_update is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {π : ι -> Type.{u2}} [_inst_2 : forall (i : ι), TopologicalSpace.{u2} (π i)] [_inst_3 : DecidableEq.{succ u1} ι] (i : ι), Continuous.{max u1 u2, max u1 u2} (Prod.{max u1 u2, u2} (forall (j : ι), π j) (π i)) (forall (a : ι), π a) (Prod.topologicalSpace.{max u1 u2, u2} (forall (j : ι), π j) (π i) (Pi.topologicalSpace.{u1, u2} ι (fun (a : ι) => π a) (fun (a : ι) => _inst_2 a)) (_inst_2 i)) (Pi.topologicalSpace.{u1, u2} ι (fun (a : ι) => π a) (fun (a : ι) => _inst_2 a)) (fun (f : Prod.{max u1 u2, u2} (forall (j : ι), π j) (π i)) => Function.update.{succ u1, succ u2} ι (fun (j : ι) => π j) (fun (a : ι) (b : ι) => _inst_3 a b) (Prod.fst.{max u1 u2, u2} (forall (j : ι), π j) (π i) f) i (Prod.snd.{max u1 u2, u2} (forall (j : ι), π j) (π i) f))
but is expected to have type
  forall {ι : Type.{u2}} {π : ι -> Type.{u1}} [_inst_2 : forall (i : ι), TopologicalSpace.{u1} (π i)] [_inst_3 : DecidableEq.{succ u2} ι] (i : ι), Continuous.{max u2 u1, max u2 u1} (Prod.{max u2 u1, u1} (forall (j : ι), π j) (π i)) (forall (a : ι), π a) (instTopologicalSpaceProd.{max u2 u1, u1} (forall (j : ι), π j) (π i) (Pi.topologicalSpace.{u2, u1} ι (fun (a : ι) => π a) (fun (a : ι) => _inst_2 a)) (_inst_2 i)) (Pi.topologicalSpace.{u2, u1} ι (fun (a : ι) => π a) (fun (a : ι) => _inst_2 a)) (fun (f : Prod.{max u2 u1, u1} (forall (j : ι), π j) (π i)) => Function.update.{succ u2, succ u1} ι (fun (j : ι) => π j) (fun (a : ι) (b : ι) => _inst_3 a b) (Prod.fst.{max u2 u1, u1} (forall (j : ι), π j) (π i) f) i (Prod.snd.{max u2 u1, u1} (forall (j : ι), π j) (π i) f))
Case conversion may be inaccurate. Consider using '#align continuous_update continuous_updateₓ'. -/
/-- `function.update f i x` is continuous in `(f, x)`. -/
@[continuity]
theorem continuous_update [DecidableEq ι] (i : ι) :
    Continuous fun f : (∀ j, π j) × π i => update f.1 i f.2 :=
  continuous_fst.update i continuous_snd
#align continuous_update continuous_update

/-- `pi.mul_single i x` is continuous in `x`. -/
@[continuity, to_additive "`pi.single i x` is continuous in `x`."]
theorem continuous_mulSingle [∀ i, One (π i)] [DecidableEq ι] (i : ι) :
    Continuous fun x => (Pi.mulSingle i x : ∀ i, π i) :=
  continuous_const.update _ continuous_id
#align continuous_mul_single continuous_mulSingle
#align continuous_single continuous_single

/- warning: filter.tendsto.fin_insert_nth -> Filter.Tendsto.fin_insertNth is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {n : Nat} {π : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u2}} [_inst_3 : forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), TopologicalSpace.{u2} (π i)] (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) {f : β -> (π i)} {l : Filter.{u1} β} {x : π i}, (Filter.Tendsto.{u1, u2} β (π i) f l (nhds.{u2} (π i) (_inst_3 i) x)) -> (forall {g : β -> (forall (j : Fin n), π (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) j))} {y : forall (j : Fin n), π (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) j)}, (Filter.Tendsto.{u1, u2} β (forall (j : Fin n), π (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) j)) g l (nhds.{u2} (forall (j : Fin n), π (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) j)) (Pi.topologicalSpace.{0, u2} (Fin n) (fun (j : Fin n) => π (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) j)) (fun (a : Fin n) => _inst_3 (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) a))) y)) -> (Filter.Tendsto.{u1, u2} β (forall (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), π j) (fun (a : β) => Fin.insertNth.{u2} n (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => π i) i (f a) (g a)) l (nhds.{u2} (forall (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), π j) (Pi.topologicalSpace.{0, u2} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => π j) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => _inst_3 a)) (Fin.insertNth.{u2} n (fun (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => π j) i x y))))
but is expected to have type
  forall {β : Type.{u2}} {n : Nat} {π : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u1}} [_inst_3 : forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), TopologicalSpace.{u1} (π i)] (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) {f : β -> (π i)} {l : Filter.{u2} β} {x : π i}, (Filter.Tendsto.{u2, u1} β (π i) f l (nhds.{u1} (π i) (_inst_3 i) x)) -> (forall {g : β -> (forall (j : Fin n), π (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Function.instEmbeddingLikeEmbedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (RelEmbedding.toEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (Fin.succAbove n i)) j))} {y : forall (j : Fin n), π (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Function.instEmbeddingLikeEmbedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (RelEmbedding.toEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (Fin.succAbove n i)) j)}, (Filter.Tendsto.{u2, u1} β (forall (j : Fin n), π (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Function.instEmbeddingLikeEmbedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (RelEmbedding.toEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (Fin.succAbove n i)) j)) g l (nhds.{u1} (forall (j : Fin n), π (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Function.instEmbeddingLikeEmbedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (RelEmbedding.toEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (Fin.succAbove n i)) j)) (Pi.topologicalSpace.{0, u1} (Fin n) (fun (j : Fin n) => π (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Function.instEmbeddingLikeEmbedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (RelEmbedding.toEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (Fin.succAbove n i)) j)) (fun (a : Fin n) => _inst_3 (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Function.instEmbeddingLikeEmbedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (RelEmbedding.toEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (Fin.succAbove n i)) a))) y)) -> (Filter.Tendsto.{u2, u1} β (forall (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), π j) (fun (a : β) => Fin.insertNth.{u1} n π i (f a) (g a)) l (nhds.{u1} (forall (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), π j) (Pi.topologicalSpace.{0, u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => π j) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => _inst_3 a)) (Fin.insertNth.{u1} n (fun (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => π j) i x y))))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.fin_insert_nth Filter.Tendsto.fin_insertNthₓ'. -/
theorem Filter.Tendsto.fin_insertNth {n} {π : Fin (n + 1) → Type _} [∀ i, TopologicalSpace (π i)]
    (i : Fin (n + 1)) {f : β → π i} {l : Filter β} {x : π i} (hf : Tendsto f l (𝓝 x))
    {g : β → ∀ j : Fin n, π (i.succAbove j)} {y : ∀ j, π (i.succAbove j)} (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun a => i.insertNth (f a) (g a)) l (𝓝 <| i.insertNth x y) :=
  tendsto_pi_nhds.2 fun j => Fin.succAboveCases i (by simpa) (by simpa using tendsto_pi_nhds.1 hg) j
#align filter.tendsto.fin_insert_nth Filter.Tendsto.fin_insertNth

/- warning: continuous_at.fin_insert_nth -> ContinuousAt.fin_insertNth is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {n : Nat} {π : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u2}} [_inst_3 : forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), TopologicalSpace.{u2} (π i)] (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) {f : α -> (π i)} {a : α}, (ContinuousAt.{u1, u2} α (π i) _inst_1 (_inst_3 i) f a) -> (forall {g : α -> (forall (j : Fin n), π (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) j))}, (ContinuousAt.{u1, u2} α (forall (j : Fin n), π (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) j)) _inst_1 (Pi.topologicalSpace.{0, u2} (Fin n) (fun (j : Fin n) => π (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) j)) (fun (a : Fin n) => _inst_3 (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) a))) g a) -> (ContinuousAt.{u1, u2} α (forall (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), π j) _inst_1 (Pi.topologicalSpace.{0, u2} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => π j) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => _inst_3 a)) (fun (a : α) => Fin.insertNth.{u2} n (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => π i) i (f a) (g a)) a))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {n : Nat} {π : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u1}} [_inst_3 : forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), TopologicalSpace.{u1} (π i)] (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) {f : α -> (π i)} {a : α}, (ContinuousAt.{u2, u1} α (π i) _inst_1 (_inst_3 i) f a) -> (forall {g : α -> (forall (j : Fin n), π (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Function.instEmbeddingLikeEmbedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (RelEmbedding.toEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (Fin.succAbove n i)) j))}, (ContinuousAt.{u2, u1} α (forall (j : Fin n), π (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Function.instEmbeddingLikeEmbedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (RelEmbedding.toEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (Fin.succAbove n i)) j)) _inst_1 (Pi.topologicalSpace.{0, u1} (Fin n) (fun (j : Fin n) => π (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Function.instEmbeddingLikeEmbedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (RelEmbedding.toEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (Fin.succAbove n i)) j)) (fun (a : Fin n) => _inst_3 (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Function.instEmbeddingLikeEmbedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (RelEmbedding.toEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (Fin.succAbove n i)) a))) g a) -> (ContinuousAt.{u2, u1} α (forall (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), π j) _inst_1 (Pi.topologicalSpace.{0, u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => π j) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => _inst_3 a)) (fun (a : α) => Fin.insertNth.{u1} n π i (f a) (g a)) a))
Case conversion may be inaccurate. Consider using '#align continuous_at.fin_insert_nth ContinuousAt.fin_insertNthₓ'. -/
theorem ContinuousAt.fin_insertNth {n} {π : Fin (n + 1) → Type _} [∀ i, TopologicalSpace (π i)]
    (i : Fin (n + 1)) {f : α → π i} {a : α} (hf : ContinuousAt f a)
    {g : α → ∀ j : Fin n, π (i.succAbove j)} (hg : ContinuousAt g a) :
    ContinuousAt (fun a => i.insertNth (f a) (g a)) a :=
  hf.fin_insertNth i hg
#align continuous_at.fin_insert_nth ContinuousAt.fin_insertNth

/- warning: continuous.fin_insert_nth -> Continuous.fin_insertNth is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {n : Nat} {π : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u2}} [_inst_3 : forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), TopologicalSpace.{u2} (π i)] (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) {f : α -> (π i)}, (Continuous.{u1, u2} α (π i) _inst_1 (_inst_3 i) f) -> (forall {g : α -> (forall (j : Fin n), π (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) j))}, (Continuous.{u1, u2} α (forall (j : Fin n), π (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) j)) _inst_1 (Pi.topologicalSpace.{0, u2} (Fin n) (fun (j : Fin n) => π (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) j)) (fun (a : Fin n) => _inst_3 (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) a))) g) -> (Continuous.{u1, u2} α (forall (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), π j) _inst_1 (Pi.topologicalSpace.{0, u2} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => π j) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => _inst_3 a)) (fun (a : α) => Fin.insertNth.{u2} n (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => π i) i (f a) (g a))))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {n : Nat} {π : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u1}} [_inst_3 : forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), TopologicalSpace.{u1} (π i)] (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) {f : α -> (π i)}, (Continuous.{u2, u1} α (π i) _inst_1 (_inst_3 i) f) -> (forall {g : α -> (forall (j : Fin n), π (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Function.instEmbeddingLikeEmbedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (RelEmbedding.toEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (Fin.succAbove n i)) j))}, (Continuous.{u2, u1} α (forall (j : Fin n), π (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Function.instEmbeddingLikeEmbedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (RelEmbedding.toEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (Fin.succAbove n i)) j)) _inst_1 (Pi.topologicalSpace.{0, u1} (Fin n) (fun (j : Fin n) => π (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Function.instEmbeddingLikeEmbedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (RelEmbedding.toEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (Fin.succAbove n i)) j)) (fun (a : Fin n) => _inst_3 (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Function.instEmbeddingLikeEmbedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (RelEmbedding.toEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (Fin.succAbove n i)) a))) g) -> (Continuous.{u2, u1} α (forall (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), π j) _inst_1 (Pi.topologicalSpace.{0, u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => π j) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => _inst_3 a)) (fun (a : α) => Fin.insertNth.{u1} n π i (f a) (g a))))
Case conversion may be inaccurate. Consider using '#align continuous.fin_insert_nth Continuous.fin_insertNthₓ'. -/
theorem Continuous.fin_insertNth {n} {π : Fin (n + 1) → Type _} [∀ i, TopologicalSpace (π i)]
    (i : Fin (n + 1)) {f : α → π i} (hf : Continuous f) {g : α → ∀ j : Fin n, π (i.succAbove j)}
    (hg : Continuous g) : Continuous fun a => i.insertNth (f a) (g a) :=
  continuous_iff_continuousAt.2 fun a => hf.ContinuousAt.fin_insertNth i hg.ContinuousAt
#align continuous.fin_insert_nth Continuous.fin_insertNth

/- warning: is_open_set_pi -> isOpen_set_pi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {π : ι -> Type.{u2}} [_inst_2 : forall (i : ι), TopologicalSpace.{u2} (π i)] {i : Set.{u1} ι} {s : forall (a : ι), Set.{u2} (π a)}, (Set.Finite.{u1} ι i) -> (forall (a : ι), (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) a i) -> (IsOpen.{u2} (π a) (_inst_2 a) (s a))) -> (IsOpen.{max u1 u2} (forall (i : ι), π i) (Pi.topologicalSpace.{u1, u2} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_2 a)) (Set.pi.{u1, u2} ι (fun (a : ι) => π a) i s))
but is expected to have type
  forall {ι : Type.{u2}} {π : ι -> Type.{u1}} [_inst_2 : forall (i : ι), TopologicalSpace.{u1} (π i)] {i : Set.{u2} ι} {s : forall (a : ι), Set.{u1} (π a)}, (Set.Finite.{u2} ι i) -> (forall (a : ι), (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) a i) -> (IsOpen.{u1} (π a) (_inst_2 a) (s a))) -> (IsOpen.{max u1 u2} (forall (i : ι), π i) (Pi.topologicalSpace.{u2, u1} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_2 a)) (Set.pi.{u2, u1} ι (fun (a : ι) => π a) i s))
Case conversion may be inaccurate. Consider using '#align is_open_set_pi isOpen_set_piₓ'. -/
theorem isOpen_set_pi {i : Set ι} {s : ∀ a, Set (π a)} (hi : i.Finite)
    (hs : ∀ a ∈ i, IsOpen (s a)) : IsOpen (pi i s) := by
  rw [pi_def] <;> exact isOpen_binterᵢ hi fun a ha => (hs _ ha).Preimage (continuous_apply _)
#align is_open_set_pi isOpen_set_pi

/- warning: is_open_pi_iff -> isOpen_pi_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {π : ι -> Type.{u2}} [_inst_2 : forall (i : ι), TopologicalSpace.{u2} (π i)] {s : Set.{max u1 u2} (forall (a : ι), π a)}, Iff (IsOpen.{max u1 u2} (forall (a : ι), π a) (Pi.topologicalSpace.{u1, u2} ι (fun (a : ι) => π a) (fun (a : ι) => _inst_2 a)) s) (forall (f : forall (a : ι), π a), (Membership.Mem.{max u1 u2, max u1 u2} (forall (a : ι), π a) (Set.{max u1 u2} (forall (a : ι), π a)) (Set.hasMem.{max u1 u2} (forall (a : ι), π a)) f s) -> (Exists.{succ u1} (Finset.{u1} ι) (fun (I : Finset.{u1} ι) => Exists.{max (succ u1) (succ u2)} (forall (a : ι), Set.{u2} (π a)) (fun (u : forall (a : ι), Set.{u2} (π a)) => And (forall (a : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) a I) -> (And (IsOpen.{u2} (π a) (_inst_2 a) (u a)) (Membership.Mem.{u2, u2} (π a) (Set.{u2} (π a)) (Set.hasMem.{u2} (π a)) (f a) (u a)))) (HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), π i)) (Set.hasSubset.{max u1 u2} (forall (i : ι), π i)) (Set.pi.{u1, u2} ι (fun (a : ι) => π a) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} ι) (Set.{u1} ι) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} ι) (Set.{u1} ι) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} ι) (Set.{u1} ι) (Finset.Set.hasCoeT.{u1} ι))) I) u) s)))))
but is expected to have type
  forall {ι : Type.{u2}} {π : ι -> Type.{u1}} [_inst_2 : forall (i : ι), TopologicalSpace.{u1} (π i)] {s : Set.{max u2 u1} (forall (a : ι), π a)}, Iff (IsOpen.{max u2 u1} (forall (a : ι), π a) (Pi.topologicalSpace.{u2, u1} ι (fun (a : ι) => π a) (fun (a : ι) => _inst_2 a)) s) (forall (f : forall (a : ι), π a), (Membership.mem.{max u2 u1, max u2 u1} (forall (a : ι), π a) (Set.{max u2 u1} (forall (a : ι), π a)) (Set.instMembershipSet.{max u2 u1} (forall (a : ι), π a)) f s) -> (Exists.{succ u2} (Finset.{u2} ι) (fun (I : Finset.{u2} ι) => Exists.{max (succ u2) (succ u1)} (forall (a : ι), Set.{u1} (π a)) (fun (u : forall (a : ι), Set.{u1} (π a)) => And (forall (a : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) a I) -> (And (IsOpen.{u1} (π a) (_inst_2 a) (u a)) (Membership.mem.{u1, u1} (π a) (Set.{u1} (π a)) (Set.instMembershipSet.{u1} (π a)) (f a) (u a)))) (HasSubset.Subset.{max u2 u1} (Set.{max u2 u1} (forall (i : ι), π i)) (Set.instHasSubsetSet.{max u2 u1} (forall (i : ι), π i)) (Set.pi.{u2, u1} ι (fun (a : ι) => π a) (Finset.toSet.{u2} ι I) u) s)))))
Case conversion may be inaccurate. Consider using '#align is_open_pi_iff isOpen_pi_iffₓ'. -/
theorem isOpen_pi_iff {s : Set (∀ a, π a)} :
    IsOpen s ↔
      ∀ f,
        f ∈ s →
          ∃ (I : Finset ι)(u : ∀ a, Set (π a)),
            (∀ a, a ∈ I → IsOpen (u a) ∧ f a ∈ u a) ∧ (I : Set ι).pi u ⊆ s :=
  by
  rw [isOpen_iff_nhds]
  simp_rw [le_principal_iff, nhds_pi, Filter.mem_pi', mem_nhds_iff, exists_prop]
  refine' ball_congr fun a h => ⟨_, _⟩
  · rintro ⟨I, t, ⟨h1, h2⟩⟩
    refine' ⟨I, fun a => eval a '' (I : Set ι).pi fun a => (h1 a).some, fun i hi => _, _⟩
    · simp_rw [Set.eval_image_pi (finset.mem_coe.mpr hi)
          (pi_nonempty_iff.mpr fun i => ⟨_, fun _ => (h1 i).choose_spec.2.2⟩)]
      exact (h1 i).choose_spec.2
    ·
      refine'
        subset.trans
          (Set.pi_mono fun i hi => (Set.eval_image_pi_subset hi).trans (h1 i).choose_spec.1) h2
  · rintro ⟨I, t, ⟨h1, h2⟩⟩
    refine' ⟨I, fun a => ite (a ∈ I) (t a) Set.univ, fun i => _, _⟩
    · by_cases hi : i ∈ I
      · use t i
        rw [if_pos hi]
        exact ⟨subset.rfl, (h1 i) hi⟩
      · use Set.univ
        rw [if_neg hi]
        exact ⟨subset.rfl, isOpen_univ, mem_univ _⟩
    · rw [← Set.univ_pi_ite]
      simp only [← ite_and, ← Finset.mem_coe, and_self_iff, Set.univ_pi_ite, h2]
#align is_open_pi_iff isOpen_pi_iff

/- warning: is_open_pi_iff' -> isOpen_pi_iff' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {π : ι -> Type.{u2}} [_inst_2 : forall (i : ι), TopologicalSpace.{u2} (π i)] [_inst_3 : Finite.{succ u1} ι] {s : Set.{max u1 u2} (forall (a : ι), π a)}, Iff (IsOpen.{max u1 u2} (forall (a : ι), π a) (Pi.topologicalSpace.{u1, u2} ι (fun (a : ι) => π a) (fun (a : ι) => _inst_2 a)) s) (forall (f : forall (a : ι), π a), (Membership.Mem.{max u1 u2, max u1 u2} (forall (a : ι), π a) (Set.{max u1 u2} (forall (a : ι), π a)) (Set.hasMem.{max u1 u2} (forall (a : ι), π a)) f s) -> (Exists.{max (succ u1) (succ u2)} (forall (a : ι), Set.{u2} (π a)) (fun (u : forall (a : ι), Set.{u2} (π a)) => And (forall (a : ι), And (IsOpen.{u2} (π a) (_inst_2 a) (u a)) (Membership.Mem.{u2, u2} (π a) (Set.{u2} (π a)) (Set.hasMem.{u2} (π a)) (f a) (u a))) (HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), π i)) (Set.hasSubset.{max u1 u2} (forall (i : ι), π i)) (Set.pi.{u1, u2} ι (fun (a : ι) => π a) (Set.univ.{u1} ι) u) s))))
but is expected to have type
  forall {ι : Type.{u2}} {π : ι -> Type.{u1}} [_inst_2 : forall (i : ι), TopologicalSpace.{u1} (π i)] [_inst_3 : Finite.{succ u2} ι] {s : Set.{max u2 u1} (forall (a : ι), π a)}, Iff (IsOpen.{max u2 u1} (forall (a : ι), π a) (Pi.topologicalSpace.{u2, u1} ι (fun (a : ι) => π a) (fun (a : ι) => _inst_2 a)) s) (forall (f : forall (a : ι), π a), (Membership.mem.{max u2 u1, max u2 u1} (forall (a : ι), π a) (Set.{max u2 u1} (forall (a : ι), π a)) (Set.instMembershipSet.{max u2 u1} (forall (a : ι), π a)) f s) -> (Exists.{max (succ u2) (succ u1)} (forall (a : ι), Set.{u1} (π a)) (fun (u : forall (a : ι), Set.{u1} (π a)) => And (forall (a : ι), And (IsOpen.{u1} (π a) (_inst_2 a) (u a)) (Membership.mem.{u1, u1} (π a) (Set.{u1} (π a)) (Set.instMembershipSet.{u1} (π a)) (f a) (u a))) (HasSubset.Subset.{max u1 u2} (Set.{max u2 u1} (forall (i : ι), π i)) (Set.instHasSubsetSet.{max u2 u1} (forall (i : ι), π i)) (Set.pi.{u2, u1} ι (fun (a : ι) => π a) (Set.univ.{u2} ι) u) s))))
Case conversion may be inaccurate. Consider using '#align is_open_pi_iff' isOpen_pi_iff'ₓ'. -/
theorem isOpen_pi_iff' [Finite ι] {s : Set (∀ a, π a)} :
    IsOpen s ↔
      ∀ f, f ∈ s → ∃ u : ∀ a, Set (π a), (∀ a, IsOpen (u a) ∧ f a ∈ u a) ∧ Set.univ.pi u ⊆ s :=
  by
  cases nonempty_fintype ι
  rw [isOpen_iff_nhds]
  simp_rw [le_principal_iff, nhds_pi, Filter.mem_pi', mem_nhds_iff, exists_prop]
  refine' ball_congr fun a h => ⟨_, _⟩
  · rintro ⟨I, t, ⟨h1, h2⟩⟩
    refine'
      ⟨fun i => (h1 i).some,
        ⟨fun i => (h1 i).choose_spec.2,
          (Set.pi_mono fun i _ => (h1 i).choose_spec.1).trans (subset.trans _ h2)⟩⟩
    rw [← Set.pi_inter_compl (I : Set ι)]
    exact inter_subset_left _ _
  ·
    exact fun ⟨u, ⟨h1, _⟩⟩ =>
      ⟨Finset.univ, u, ⟨fun i => ⟨u i, ⟨rfl.subset, h1 i⟩⟩, by rwa [Finset.coe_univ]⟩⟩
#align is_open_pi_iff' isOpen_pi_iff'

/- warning: is_closed_set_pi -> isClosed_set_pi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {π : ι -> Type.{u2}} [_inst_2 : forall (i : ι), TopologicalSpace.{u2} (π i)] {i : Set.{u1} ι} {s : forall (a : ι), Set.{u2} (π a)}, (forall (a : ι), (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) a i) -> (IsClosed.{u2} (π a) (_inst_2 a) (s a))) -> (IsClosed.{max u1 u2} (forall (i : ι), π i) (Pi.topologicalSpace.{u1, u2} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_2 a)) (Set.pi.{u1, u2} ι (fun (a : ι) => π a) i s))
but is expected to have type
  forall {ι : Type.{u2}} {π : ι -> Type.{u1}} [_inst_2 : forall (i : ι), TopologicalSpace.{u1} (π i)] {i : Set.{u2} ι} {s : forall (a : ι), Set.{u1} (π a)}, (forall (a : ι), (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) a i) -> (IsClosed.{u1} (π a) (_inst_2 a) (s a))) -> (IsClosed.{max u1 u2} (forall (i : ι), π i) (Pi.topologicalSpace.{u2, u1} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_2 a)) (Set.pi.{u2, u1} ι (fun (a : ι) => π a) i s))
Case conversion may be inaccurate. Consider using '#align is_closed_set_pi isClosed_set_piₓ'. -/
theorem isClosed_set_pi {i : Set ι} {s : ∀ a, Set (π a)} (hs : ∀ a ∈ i, IsClosed (s a)) :
    IsClosed (pi i s) := by
  rw [pi_def] <;>
    exact isClosed_interᵢ fun a => isClosed_interᵢ fun ha => (hs _ ha).Preimage (continuous_apply _)
#align is_closed_set_pi isClosed_set_pi

/- warning: mem_nhds_of_pi_mem_nhds -> mem_nhds_of_pi_mem_nhds is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {π : ι -> Type.{u2}} [_inst_2 : forall (i : ι), TopologicalSpace.{u2} (π i)] {I : Set.{u1} ι} {s : forall (i : ι), Set.{u2} (π i)} (a : forall (i : ι), π i), (Membership.Mem.{max u1 u2, max u1 u2} (Set.{max u1 u2} (forall (i : ι), π i)) (Filter.{max u1 u2} (forall (i : ι), π i)) (Filter.hasMem.{max u1 u2} (forall (i : ι), π i)) (Set.pi.{u1, u2} ι (fun (i : ι) => π i) I s) (nhds.{max u1 u2} (forall (i : ι), π i) (Pi.topologicalSpace.{u1, u2} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_2 a)) a)) -> (forall {i : ι}, (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i I) -> (Membership.Mem.{u2, u2} (Set.{u2} (π i)) (Filter.{u2} (π i)) (Filter.hasMem.{u2} (π i)) (s i) (nhds.{u2} (π i) (_inst_2 i) (a i))))
but is expected to have type
  forall {ι : Type.{u2}} {π : ι -> Type.{u1}} [_inst_2 : forall (i : ι), TopologicalSpace.{u1} (π i)] {I : Set.{u2} ι} {s : forall (i : ι), Set.{u1} (π i)} (a : forall (i : ι), π i), (Membership.mem.{max u2 u1, max u2 u1} (Set.{max u2 u1} (forall (i : ι), π i)) (Filter.{max u2 u1} (forall (i : ι), π i)) (instMembershipSetFilter.{max u2 u1} (forall (i : ι), π i)) (Set.pi.{u2, u1} ι (fun (i : ι) => π i) I s) (nhds.{max u2 u1} (forall (i : ι), π i) (Pi.topologicalSpace.{u2, u1} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_2 a)) a)) -> (forall {i : ι}, (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i I) -> (Membership.mem.{u1, u1} (Set.{u1} (π i)) (Filter.{u1} (π i)) (instMembershipSetFilter.{u1} (π i)) (s i) (nhds.{u1} (π i) (_inst_2 i) (a i))))
Case conversion may be inaccurate. Consider using '#align mem_nhds_of_pi_mem_nhds mem_nhds_of_pi_mem_nhdsₓ'. -/
theorem mem_nhds_of_pi_mem_nhds {I : Set ι} {s : ∀ i, Set (π i)} (a : ∀ i, π i) (hs : I.pi s ∈ 𝓝 a)
    {i : ι} (hi : i ∈ I) : s i ∈ 𝓝 (a i) :=
  by
  rw [nhds_pi] at hs
  exact mem_of_pi_mem_pi hs hi
#align mem_nhds_of_pi_mem_nhds mem_nhds_of_pi_mem_nhds

/- warning: set_pi_mem_nhds -> set_pi_mem_nhds is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {π : ι -> Type.{u2}} [_inst_2 : forall (i : ι), TopologicalSpace.{u2} (π i)] {i : Set.{u1} ι} {s : forall (a : ι), Set.{u2} (π a)} {x : forall (a : ι), π a}, (Set.Finite.{u1} ι i) -> (forall (a : ι), (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) a i) -> (Membership.Mem.{u2, u2} (Set.{u2} (π a)) (Filter.{u2} (π a)) (Filter.hasMem.{u2} (π a)) (s a) (nhds.{u2} (π a) (_inst_2 a) (x a)))) -> (Membership.Mem.{max u1 u2, max u1 u2} (Set.{max u1 u2} (forall (i : ι), π i)) (Filter.{max u1 u2} (forall (a : ι), π a)) (Filter.hasMem.{max u1 u2} (forall (a : ι), π a)) (Set.pi.{u1, u2} ι (fun (a : ι) => π a) i s) (nhds.{max u1 u2} (forall (a : ι), π a) (Pi.topologicalSpace.{u1, u2} ι (fun (a : ι) => π a) (fun (a : ι) => _inst_2 a)) x))
but is expected to have type
  forall {ι : Type.{u2}} {π : ι -> Type.{u1}} [_inst_2 : forall (i : ι), TopologicalSpace.{u1} (π i)] {i : Set.{u2} ι} {s : forall (a : ι), Set.{u1} (π a)} {x : forall (a : ι), π a}, (Set.Finite.{u2} ι i) -> (forall (a : ι), (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) a i) -> (Membership.mem.{u1, u1} (Set.{u1} (π a)) (Filter.{u1} (π a)) (instMembershipSetFilter.{u1} (π a)) (s a) (nhds.{u1} (π a) (_inst_2 a) (x a)))) -> (Membership.mem.{max u1 u2, max u2 u1} (Set.{max u2 u1} (forall (i : ι), π i)) (Filter.{max u2 u1} (forall (a : ι), π a)) (instMembershipSetFilter.{max u2 u1} (forall (a : ι), π a)) (Set.pi.{u2, u1} ι (fun (a : ι) => π a) i s) (nhds.{max u2 u1} (forall (a : ι), π a) (Pi.topologicalSpace.{u2, u1} ι (fun (a : ι) => π a) (fun (a : ι) => _inst_2 a)) x))
Case conversion may be inaccurate. Consider using '#align set_pi_mem_nhds set_pi_mem_nhdsₓ'. -/
theorem set_pi_mem_nhds {i : Set ι} {s : ∀ a, Set (π a)} {x : ∀ a, π a} (hi : i.Finite)
    (hs : ∀ a ∈ i, s a ∈ 𝓝 (x a)) : pi i s ∈ 𝓝 x :=
  by
  rw [pi_def, bInter_mem hi]
  exact fun a ha => (continuous_apply a).ContinuousAt (hs a ha)
#align set_pi_mem_nhds set_pi_mem_nhds

/- warning: set_pi_mem_nhds_iff -> set_pi_mem_nhds_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {π : ι -> Type.{u2}} [_inst_2 : forall (i : ι), TopologicalSpace.{u2} (π i)] {I : Set.{u1} ι}, (Set.Finite.{u1} ι I) -> (forall {s : forall (i : ι), Set.{u2} (π i)} (a : forall (i : ι), π i), Iff (Membership.Mem.{max u1 u2, max u1 u2} (Set.{max u1 u2} (forall (i : ι), π i)) (Filter.{max u1 u2} (forall (i : ι), π i)) (Filter.hasMem.{max u1 u2} (forall (i : ι), π i)) (Set.pi.{u1, u2} ι (fun (i : ι) => π i) I s) (nhds.{max u1 u2} (forall (i : ι), π i) (Pi.topologicalSpace.{u1, u2} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_2 a)) a)) (forall (i : ι), (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i I) -> (Membership.Mem.{u2, u2} (Set.{u2} (π i)) (Filter.{u2} (π i)) (Filter.hasMem.{u2} (π i)) (s i) (nhds.{u2} (π i) (_inst_2 i) (a i)))))
but is expected to have type
  forall {ι : Type.{u2}} {π : ι -> Type.{u1}} [_inst_2 : forall (i : ι), TopologicalSpace.{u1} (π i)] {I : Set.{u2} ι}, (Set.Finite.{u2} ι I) -> (forall {s : forall (i : ι), Set.{u1} (π i)} (a : forall (i : ι), π i), Iff (Membership.mem.{max u2 u1, max u2 u1} (Set.{max u2 u1} (forall (i : ι), π i)) (Filter.{max u2 u1} (forall (i : ι), π i)) (instMembershipSetFilter.{max u2 u1} (forall (i : ι), π i)) (Set.pi.{u2, u1} ι (fun (i : ι) => π i) I s) (nhds.{max u2 u1} (forall (i : ι), π i) (Pi.topologicalSpace.{u2, u1} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_2 a)) a)) (forall (i : ι), (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i I) -> (Membership.mem.{u1, u1} (Set.{u1} (π i)) (Filter.{u1} (π i)) (instMembershipSetFilter.{u1} (π i)) (s i) (nhds.{u1} (π i) (_inst_2 i) (a i)))))
Case conversion may be inaccurate. Consider using '#align set_pi_mem_nhds_iff set_pi_mem_nhds_iffₓ'. -/
theorem set_pi_mem_nhds_iff {I : Set ι} (hI : I.Finite) {s : ∀ i, Set (π i)} (a : ∀ i, π i) :
    I.pi s ∈ 𝓝 a ↔ ∀ i : ι, i ∈ I → s i ∈ 𝓝 (a i) :=
  by
  rw [nhds_pi, pi_mem_pi_iff hI]
  infer_instance
#align set_pi_mem_nhds_iff set_pi_mem_nhds_iff

/- warning: interior_pi_set -> interior_pi_set is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {π : ι -> Type.{u2}} [_inst_2 : forall (i : ι), TopologicalSpace.{u2} (π i)] {I : Set.{u1} ι}, (Set.Finite.{u1} ι I) -> (forall {s : forall (i : ι), Set.{u2} (π i)}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (forall (i : ι), π i)) (interior.{max u1 u2} (forall (i : ι), π i) (Pi.topologicalSpace.{u1, u2} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_2 a)) (Set.pi.{u1, u2} ι (fun (i : ι) => π i) I s)) (Set.pi.{u1, u2} ι (fun (i : ι) => π i) I (fun (i : ι) => interior.{u2} (π i) (_inst_2 i) (s i))))
but is expected to have type
  forall {ι : Type.{u2}} {π : ι -> Type.{u1}} [_inst_2 : forall (i : ι), TopologicalSpace.{u1} (π i)] {I : Set.{u2} ι}, (Set.Finite.{u2} ι I) -> (forall {s : forall (i : ι), Set.{u1} (π i)}, Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (forall (i : ι), π i)) (interior.{max u1 u2} (forall (i : ι), π i) (Pi.topologicalSpace.{u2, u1} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_2 a)) (Set.pi.{u2, u1} ι (fun (i : ι) => π i) I s)) (Set.pi.{u2, u1} ι (fun (i : ι) => π i) I (fun (i : ι) => interior.{u1} (π i) (_inst_2 i) (s i))))
Case conversion may be inaccurate. Consider using '#align interior_pi_set interior_pi_setₓ'. -/
theorem interior_pi_set {I : Set ι} (hI : I.Finite) {s : ∀ i, Set (π i)} :
    interior (pi I s) = I.pi fun i => interior (s i) :=
  by
  ext a
  simp only [Set.mem_pi, mem_interior_iff_mem_nhds, set_pi_mem_nhds_iff hI]
#align interior_pi_set interior_pi_set

/- warning: exists_finset_piecewise_mem_of_mem_nhds -> exists_finset_piecewise_mem_of_mem_nhds is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {π : ι -> Type.{u2}} [_inst_2 : forall (i : ι), TopologicalSpace.{u2} (π i)] [_inst_3 : DecidableEq.{succ u1} ι] {s : Set.{max u1 u2} (forall (a : ι), π a)} {x : forall (a : ι), π a}, (Membership.Mem.{max u1 u2, max u1 u2} (Set.{max u1 u2} (forall (a : ι), π a)) (Filter.{max u1 u2} (forall (a : ι), π a)) (Filter.hasMem.{max u1 u2} (forall (a : ι), π a)) s (nhds.{max u1 u2} (forall (a : ι), π a) (Pi.topologicalSpace.{u1, u2} ι (fun (a : ι) => π a) (fun (a : ι) => _inst_2 a)) x)) -> (forall (y : forall (a : ι), π a), Exists.{succ u1} (Finset.{u1} ι) (fun (I : Finset.{u1} ι) => Membership.Mem.{max u1 u2, max u1 u2} (forall (i : ι), π i) (Set.{max u1 u2} (forall (a : ι), π a)) (Set.hasMem.{max u1 u2} (forall (a : ι), π a)) (Finset.piecewise.{u1, succ u2} ι (fun (a : ι) => π a) I x y (fun (j : ι) => Finset.decidableMem.{u1} ι (fun (a : ι) (b : ι) => _inst_3 a b) j I)) s))
but is expected to have type
  forall {ι : Type.{u2}} {π : ι -> Type.{u1}} [_inst_2 : forall (i : ι), TopologicalSpace.{u1} (π i)] [_inst_3 : DecidableEq.{succ u2} ι] {s : Set.{max u2 u1} (forall (a : ι), π a)} {x : forall (a : ι), π a}, (Membership.mem.{max u2 u1, max u2 u1} (Set.{max u2 u1} (forall (a : ι), π a)) (Filter.{max u2 u1} (forall (a : ι), π a)) (instMembershipSetFilter.{max u2 u1} (forall (a : ι), π a)) s (nhds.{max u2 u1} (forall (a : ι), π a) (Pi.topologicalSpace.{u2, u1} ι (fun (a : ι) => π a) (fun (a : ι) => _inst_2 a)) x)) -> (forall (y : forall (a : ι), π a), Exists.{succ u2} (Finset.{u2} ι) (fun (I : Finset.{u2} ι) => Membership.mem.{max u2 u1, max u2 u1} (forall (i : ι), π i) (Set.{max u2 u1} (forall (a : ι), π a)) (Set.instMembershipSet.{max u2 u1} (forall (a : ι), π a)) (Finset.piecewise.{u2, succ u1} ι (fun (a : ι) => π a) I x y (fun (j : ι) => Finset.decidableMem.{u2} ι (fun (a : ι) (b : ι) => _inst_3 a b) j I)) s))
Case conversion may be inaccurate. Consider using '#align exists_finset_piecewise_mem_of_mem_nhds exists_finset_piecewise_mem_of_mem_nhdsₓ'. -/
theorem exists_finset_piecewise_mem_of_mem_nhds [DecidableEq ι] {s : Set (∀ a, π a)} {x : ∀ a, π a}
    (hs : s ∈ 𝓝 x) (y : ∀ a, π a) : ∃ I : Finset ι, I.piecewise x y ∈ s :=
  by
  simp only [nhds_pi, Filter.mem_pi'] at hs
  rcases hs with ⟨I, t, htx, hts⟩
  refine' ⟨I, hts fun i hi => _⟩
  simpa [Finset.mem_coe.1 hi] using mem_of_mem_nhds (htx i)
#align exists_finset_piecewise_mem_of_mem_nhds exists_finset_piecewise_mem_of_mem_nhds

#print pi_eq_generateFrom /-
theorem pi_eq_generateFrom :
    Pi.topologicalSpace =
      generateFrom
        { g | ∃ (s : ∀ a, Set (π a))(i : Finset ι), (∀ a ∈ i, IsOpen (s a)) ∧ g = pi (↑i) s } :=
  le_antisymm
    (le_generateFrom fun g ⟨s, i, hi, Eq⟩ => Eq.symm ▸ isOpen_set_pi (Finset.finite_toSet _) hi)
    (le_infᵢ fun a s ⟨t, ht, s_eq⟩ =>
      GenerateOpen.basic _ <|
        ⟨update (fun a => univ) a t, {a}, by simpa using ht, s_eq ▸ by ext f <;> simp [Set.pi]⟩)
#align pi_eq_generate_from pi_eq_generateFrom
-/

#print pi_generateFrom_eq /-
theorem pi_generateFrom_eq {π : ι → Type _} {g : ∀ a, Set (Set (π a))} :
    (@Pi.topologicalSpace ι π fun a => generateFrom (g a)) =
      generateFrom
        { t | ∃ (s : ∀ a, Set (π a))(i : Finset ι), (∀ a ∈ i, s a ∈ g a) ∧ t = pi (↑i) s } :=
  by
  let G := { t | ∃ (s : ∀ a, Set (π a))(i : Finset ι), (∀ a ∈ i, s a ∈ g a) ∧ t = pi (↑i) s }
  rw [pi_eq_generateFrom]
  refine' le_antisymm (generate_from_anti _) (le_generateFrom _)
  exact fun s ⟨t, i, ht, Eq⟩ => ⟨t, i, fun a ha => generate_open.basic _ (ht a ha), Eq⟩
  · rintro s ⟨t, i, hi, rfl⟩
    rw [pi_def]
    apply isOpen_binterᵢ (Finset.finite_toSet _)
    intro a ha
    show ((generate_from G).coinduced fun f : ∀ a, π a => f a).IsOpen (t a)
    refine' le_generateFrom _ _ (hi a ha)
    exact fun s hs => generate_open.basic _ ⟨update (fun a => univ) a s, {a}, by simp [hs]⟩
#align pi_generate_from_eq pi_generateFrom_eq
-/

#print pi_generateFrom_eq_finite /-
theorem pi_generateFrom_eq_finite {π : ι → Type _} {g : ∀ a, Set (Set (π a))} [Finite ι]
    (hg : ∀ a, ⋃₀ g a = univ) :
    (@Pi.topologicalSpace ι π fun a => generateFrom (g a)) =
      generateFrom { t | ∃ s : ∀ a, Set (π a), (∀ a, s a ∈ g a) ∧ t = pi univ s } :=
  by
  cases nonempty_fintype ι
  rw [pi_generateFrom_eq]
  refine' le_antisymm (generate_from_anti _) (le_generateFrom _)
  · rintro s ⟨t, ht, rfl⟩
    exact ⟨t, Finset.univ, by simp [ht]⟩
  · rintro s ⟨t, i, ht, rfl⟩
    apply isOpen_iff_forall_mem_open.2 _
    intro f hf
    choose c hc using
      show ∀ a, ∃ s, s ∈ g a ∧ f a ∈ s by
        intro a
        have : f a ∈ ⋃₀ g a := by
          rw [hg]
          apply mem_univ
        simpa
    refine' ⟨pi univ fun a => if a ∈ i then t a else (c : ∀ a, Set (π a)) a, _, _, _⟩
    · simp [pi_if]
    · refine' generate_open.basic _ ⟨_, fun a => _, rfl⟩
      by_cases a ∈ i <;> simp_all [Set.pi]
    · have : f ∈ pi { a | a ∉ i } c := by simp_all [Set.pi]
      simpa [pi_if, hf]
#align pi_generate_from_eq_finite pi_generateFrom_eq_finite
-/

/- warning: inducing_infi_to_pi -> inducing_infᵢ_to_pi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {π : ι -> Type.{u2}} [_inst_2 : forall (i : ι), TopologicalSpace.{u2} (π i)] {X : Type.{u3}} (f : forall (i : ι), X -> (π i)), Inducing.{u3, max u1 u2} X (forall (i : ι), π i) (infᵢ.{u3, succ u1} (TopologicalSpace.{u3} X) (ConditionallyCompleteLattice.toHasInf.{u3} (TopologicalSpace.{u3} X) (CompleteLattice.toConditionallyCompleteLattice.{u3} (TopologicalSpace.{u3} X) (TopologicalSpace.completeLattice.{u3} X))) ι (fun (i : ι) => TopologicalSpace.induced.{u3, u2} X (π i) (f i) (inferInstance.{succ u2} (TopologicalSpace.{u2} (π i)) (_inst_2 i)))) (Pi.topologicalSpace.{u1, u2} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_2 a)) (fun (x : X) (i : ι) => f i x)
but is expected to have type
  forall {ι : Type.{u2}} {π : ι -> Type.{u1}} [_inst_2 : forall (i : ι), TopologicalSpace.{u1} (π i)] {X : Type.{u3}} (f : forall (i : ι), X -> (π i)), Inducing.{u3, max u2 u1} X (forall (i : ι), π i) (infᵢ.{u3, succ u2} (TopologicalSpace.{u3} X) (ConditionallyCompleteLattice.toInfSet.{u3} (TopologicalSpace.{u3} X) (CompleteLattice.toConditionallyCompleteLattice.{u3} (TopologicalSpace.{u3} X) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u3} X))) ι (fun (i : ι) => TopologicalSpace.induced.{u3, u1} X (π i) (f i) (inferInstance.{succ u1} (TopologicalSpace.{u1} (π i)) (_inst_2 i)))) (Pi.topologicalSpace.{u2, u1} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_2 a)) (fun (x : X) (i : ι) => f i x)
Case conversion may be inaccurate. Consider using '#align inducing_infi_to_pi inducing_infᵢ_to_piₓ'. -/
/-- Suppose `π i` is a family of topological spaces indexed by `i : ι`, and `X` is a type
endowed with a family of maps `f i : X → π i` for every `i : ι`, hence inducing a
map `g : X → Π i, π i`. This lemma shows that infimum of the topologies on `X` induced by
the `f i` as `i : ι` varies is simply the topology on `X` induced by `g : X → Π i, π i`
where `Π i, π i` is endowed with the usual product topology. -/
theorem inducing_infᵢ_to_pi {X : Type _} (f : ∀ i, X → π i) :
    @Inducing X (∀ i, π i) (⨅ i, induced (f i) inferInstance) _ fun x i => f i x :=
  by
  constructor
  erw [induced_infᵢ]
  congr 1
  funext
  erw [induced_compose]
#align inducing_infi_to_pi inducing_infᵢ_to_pi

variable [Finite ι] [∀ i, DiscreteTopology (π i)]

#print Pi.discreteTopology /-
/-- A finite product of discrete spaces is discrete. -/
instance Pi.discreteTopology : DiscreteTopology (∀ i, π i) :=
  singletons_open_iff_discrete.mp fun x =>
    by
    rw [show {x} = ⋂ i, { y : ∀ i, π i | y i = x i } by ext;
        simp only [funext_iff, Set.mem_singleton_iff, Set.mem_interᵢ, Set.mem_setOf_eq]]
    exact isOpen_interᵢ fun i => (continuous_apply i).isOpen_preimage {x i} (isOpen_discrete {x i})
#align Pi.discrete_topology Pi.discreteTopology
-/

end Pi

section Sigma

variable {ι κ : Type _} {σ : ι → Type _} {τ : κ → Type _} [∀ i, TopologicalSpace (σ i)]
  [∀ k, TopologicalSpace (τ k)] [TopologicalSpace α]

/- warning: continuous_sigma_mk -> continuous_sigmaMk is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : ι -> Type.{u2}} [_inst_1 : forall (i : ι), TopologicalSpace.{u2} (σ i)] {i : ι}, Continuous.{u2, max u1 u2} (σ i) (Sigma.{u1, u2} ι σ) (_inst_1 i) (Sigma.topologicalSpace.{u1, u2} ι σ (fun (a : ι) => _inst_1 a)) (Sigma.mk.{u1, u2} ι σ i)
but is expected to have type
  forall {ι : Type.{u1}} {σ : ι -> Type.{u2}} [_inst_1 : forall (i : ι), TopologicalSpace.{u2} (σ i)] {i : ι}, Continuous.{u2, max u1 u2} (σ i) (Sigma.{u1, u2} ι σ) (_inst_1 i) (instTopologicalSpaceSigma.{u1, u2} ι σ (fun (a : ι) => _inst_1 a)) (Sigma.mk.{u1, u2} ι σ i)
Case conversion may be inaccurate. Consider using '#align continuous_sigma_mk continuous_sigmaMkₓ'. -/
@[continuity]
theorem continuous_sigmaMk {i : ι} : Continuous (@Sigma.mk ι σ i) :=
  continuous_supᵢ_rng continuous_coinduced_rng
#align continuous_sigma_mk continuous_sigmaMk

/- warning: is_open_sigma_iff -> isOpen_sigma_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : ι -> Type.{u2}} [_inst_1 : forall (i : ι), TopologicalSpace.{u2} (σ i)] {s : Set.{max u1 u2} (Sigma.{u1, u2} ι σ)}, Iff (IsOpen.{max u1 u2} (Sigma.{u1, u2} ι σ) (Sigma.topologicalSpace.{u1, u2} ι σ (fun (a : ι) => _inst_1 a)) s) (forall (i : ι), IsOpen.{u2} (σ i) (_inst_1 i) (Set.preimage.{u2, max u1 u2} (σ i) (Sigma.{u1, u2} ι σ) (Sigma.mk.{u1, u2} ι σ i) s))
but is expected to have type
  forall {ι : Type.{u1}} {σ : ι -> Type.{u2}} [_inst_1 : forall (i : ι), TopologicalSpace.{u2} (σ i)] {s : Set.{max u2 u1} (Sigma.{u1, u2} ι σ)}, Iff (IsOpen.{max u1 u2} (Sigma.{u1, u2} ι σ) (instTopologicalSpaceSigma.{u1, u2} ι σ (fun (a : ι) => _inst_1 a)) s) (forall (i : ι), IsOpen.{u2} (σ i) (_inst_1 i) (Set.preimage.{u2, max u2 u1} (σ i) (Sigma.{u1, u2} ι σ) (Sigma.mk.{u1, u2} ι σ i) s))
Case conversion may be inaccurate. Consider using '#align is_open_sigma_iff isOpen_sigma_iffₓ'. -/
theorem isOpen_sigma_iff {s : Set (Sigma σ)} : IsOpen s ↔ ∀ i, IsOpen (Sigma.mk i ⁻¹' s) := by
  simp only [isOpen_supᵢ_iff, isOpen_coinduced]
#align is_open_sigma_iff isOpen_sigma_iff

/- warning: is_closed_sigma_iff -> isClosed_sigma_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : ι -> Type.{u2}} [_inst_1 : forall (i : ι), TopologicalSpace.{u2} (σ i)] {s : Set.{max u1 u2} (Sigma.{u1, u2} ι σ)}, Iff (IsClosed.{max u1 u2} (Sigma.{u1, u2} ι σ) (Sigma.topologicalSpace.{u1, u2} ι σ (fun (a : ι) => _inst_1 a)) s) (forall (i : ι), IsClosed.{u2} (σ i) (_inst_1 i) (Set.preimage.{u2, max u1 u2} (σ i) (Sigma.{u1, u2} ι σ) (Sigma.mk.{u1, u2} ι σ i) s))
but is expected to have type
  forall {ι : Type.{u1}} {σ : ι -> Type.{u2}} [_inst_1 : forall (i : ι), TopologicalSpace.{u2} (σ i)] {s : Set.{max u2 u1} (Sigma.{u1, u2} ι σ)}, Iff (IsClosed.{max u1 u2} (Sigma.{u1, u2} ι σ) (instTopologicalSpaceSigma.{u1, u2} ι σ (fun (a : ι) => _inst_1 a)) s) (forall (i : ι), IsClosed.{u2} (σ i) (_inst_1 i) (Set.preimage.{u2, max u2 u1} (σ i) (Sigma.{u1, u2} ι σ) (Sigma.mk.{u1, u2} ι σ i) s))
Case conversion may be inaccurate. Consider using '#align is_closed_sigma_iff isClosed_sigma_iffₓ'. -/
theorem isClosed_sigma_iff {s : Set (Sigma σ)} : IsClosed s ↔ ∀ i, IsClosed (Sigma.mk i ⁻¹' s) := by
  simp only [← isOpen_compl_iff, isOpen_sigma_iff, preimage_compl]
#align is_closed_sigma_iff isClosed_sigma_iff

/- warning: is_open_map_sigma_mk -> isOpenMap_sigmaMk is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : ι -> Type.{u2}} [_inst_1 : forall (i : ι), TopologicalSpace.{u2} (σ i)] {i : ι}, IsOpenMap.{u2, max u1 u2} (σ i) (Sigma.{u1, u2} ι σ) (_inst_1 i) (Sigma.topologicalSpace.{u1, u2} ι σ (fun (a : ι) => _inst_1 a)) (Sigma.mk.{u1, u2} ι σ i)
but is expected to have type
  forall {ι : Type.{u1}} {σ : ι -> Type.{u2}} [_inst_1 : forall (i : ι), TopologicalSpace.{u2} (σ i)] {i : ι}, IsOpenMap.{u2, max u1 u2} (σ i) (Sigma.{u1, u2} ι σ) (_inst_1 i) (instTopologicalSpaceSigma.{u1, u2} ι σ (fun (a : ι) => _inst_1 a)) (Sigma.mk.{u1, u2} ι σ i)
Case conversion may be inaccurate. Consider using '#align is_open_map_sigma_mk isOpenMap_sigmaMkₓ'. -/
theorem isOpenMap_sigmaMk {i : ι} : IsOpenMap (@Sigma.mk ι σ i) :=
  by
  intro s hs
  rw [isOpen_sigma_iff]
  intro j
  rcases eq_or_ne j i with (rfl | hne)
  · rwa [Set.preimage_image_eq _ sigma_mk_injective]
  · rw [preimage_image_sigma_mk_of_ne hne]
    exact isOpen_empty
#align is_open_map_sigma_mk isOpenMap_sigmaMk

/- warning: is_open_range_sigma_mk -> isOpen_range_sigmaMk is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : ι -> Type.{u2}} [_inst_1 : forall (i : ι), TopologicalSpace.{u2} (σ i)] {i : ι}, IsOpen.{max u1 u2} (Sigma.{u1, u2} ι σ) (Sigma.topologicalSpace.{u1, u2} ι σ (fun (a : ι) => _inst_1 a)) (Set.range.{max u1 u2, succ u2} (Sigma.{u1, u2} ι σ) (σ i) (Sigma.mk.{u1, u2} ι σ i))
but is expected to have type
  forall {ι : Type.{u2}} {σ : ι -> Type.{u1}} [_inst_1 : forall (i : ι), TopologicalSpace.{u1} (σ i)] {i : ι}, IsOpen.{max u2 u1} (Sigma.{u2, u1} ι σ) (instTopologicalSpaceSigma.{u2, u1} ι σ (fun (a : ι) => _inst_1 a)) (Set.range.{max u2 u1, succ u1} (Sigma.{u2, u1} ι σ) (σ i) (Sigma.mk.{u2, u1} ι σ i))
Case conversion may be inaccurate. Consider using '#align is_open_range_sigma_mk isOpen_range_sigmaMkₓ'. -/
theorem isOpen_range_sigmaMk {i : ι} : IsOpen (Set.range (@Sigma.mk ι σ i)) :=
  isOpenMap_sigmaMk.isOpen_range
#align is_open_range_sigma_mk isOpen_range_sigmaMk

/- warning: is_closed_map_sigma_mk -> isClosedMap_sigmaMk is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : ι -> Type.{u2}} [_inst_1 : forall (i : ι), TopologicalSpace.{u2} (σ i)] {i : ι}, IsClosedMap.{u2, max u1 u2} (σ i) (Sigma.{u1, u2} ι σ) (_inst_1 i) (Sigma.topologicalSpace.{u1, u2} ι σ (fun (a : ι) => _inst_1 a)) (Sigma.mk.{u1, u2} ι σ i)
but is expected to have type
  forall {ι : Type.{u1}} {σ : ι -> Type.{u2}} [_inst_1 : forall (i : ι), TopologicalSpace.{u2} (σ i)] {i : ι}, IsClosedMap.{u2, max u1 u2} (σ i) (Sigma.{u1, u2} ι σ) (_inst_1 i) (instTopologicalSpaceSigma.{u1, u2} ι σ (fun (a : ι) => _inst_1 a)) (Sigma.mk.{u1, u2} ι σ i)
Case conversion may be inaccurate. Consider using '#align is_closed_map_sigma_mk isClosedMap_sigmaMkₓ'. -/
theorem isClosedMap_sigmaMk {i : ι} : IsClosedMap (@Sigma.mk ι σ i) :=
  by
  intro s hs
  rw [isClosed_sigma_iff]
  intro j
  rcases eq_or_ne j i with (rfl | hne)
  · rwa [Set.preimage_image_eq _ sigma_mk_injective]
  · rw [preimage_image_sigma_mk_of_ne hne]
    exact isClosed_empty
#align is_closed_map_sigma_mk isClosedMap_sigmaMk

/- warning: is_closed_range_sigma_mk -> isClosed_range_sigmaMk is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : ι -> Type.{u2}} [_inst_1 : forall (i : ι), TopologicalSpace.{u2} (σ i)] {i : ι}, IsClosed.{max u1 u2} (Sigma.{u1, u2} ι σ) (Sigma.topologicalSpace.{u1, u2} ι σ (fun (a : ι) => _inst_1 a)) (Set.range.{max u1 u2, succ u2} (Sigma.{u1, u2} ι σ) (σ i) (Sigma.mk.{u1, u2} ι σ i))
but is expected to have type
  forall {ι : Type.{u2}} {σ : ι -> Type.{u1}} [_inst_1 : forall (i : ι), TopologicalSpace.{u1} (σ i)] {i : ι}, IsClosed.{max u2 u1} (Sigma.{u2, u1} ι σ) (instTopologicalSpaceSigma.{u2, u1} ι σ (fun (a : ι) => _inst_1 a)) (Set.range.{max u2 u1, succ u1} (Sigma.{u2, u1} ι σ) (σ i) (Sigma.mk.{u2, u1} ι σ i))
Case conversion may be inaccurate. Consider using '#align is_closed_range_sigma_mk isClosed_range_sigmaMkₓ'. -/
theorem isClosed_range_sigmaMk {i : ι} : IsClosed (Set.range (@Sigma.mk ι σ i)) :=
  isClosedMap_sigmaMk.closed_range
#align is_closed_range_sigma_mk isClosed_range_sigmaMk

/- warning: open_embedding_sigma_mk -> openEmbedding_sigmaMk is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : ι -> Type.{u2}} [_inst_1 : forall (i : ι), TopologicalSpace.{u2} (σ i)] {i : ι}, OpenEmbedding.{u2, max u1 u2} (σ i) (Sigma.{u1, u2} ι σ) (_inst_1 i) (Sigma.topologicalSpace.{u1, u2} ι σ (fun (a : ι) => _inst_1 a)) (Sigma.mk.{u1, u2} ι σ i)
but is expected to have type
  forall {ι : Type.{u1}} {σ : ι -> Type.{u2}} [_inst_1 : forall (i : ι), TopologicalSpace.{u2} (σ i)] {i : ι}, OpenEmbedding.{u2, max u1 u2} (σ i) (Sigma.{u1, u2} ι σ) (_inst_1 i) (instTopologicalSpaceSigma.{u1, u2} ι σ (fun (a : ι) => _inst_1 a)) (Sigma.mk.{u1, u2} ι σ i)
Case conversion may be inaccurate. Consider using '#align open_embedding_sigma_mk openEmbedding_sigmaMkₓ'. -/
theorem openEmbedding_sigmaMk {i : ι} : OpenEmbedding (@Sigma.mk ι σ i) :=
  openEmbedding_of_continuous_injective_open continuous_sigmaMk sigma_mk_injective isOpenMap_sigmaMk
#align open_embedding_sigma_mk openEmbedding_sigmaMk

/- warning: closed_embedding_sigma_mk -> closedEmbedding_sigmaMk is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : ι -> Type.{u2}} [_inst_1 : forall (i : ι), TopologicalSpace.{u2} (σ i)] {i : ι}, ClosedEmbedding.{u2, max u1 u2} (σ i) (Sigma.{u1, u2} ι σ) (_inst_1 i) (Sigma.topologicalSpace.{u1, u2} ι σ (fun (a : ι) => _inst_1 a)) (Sigma.mk.{u1, u2} ι σ i)
but is expected to have type
  forall {ι : Type.{u1}} {σ : ι -> Type.{u2}} [_inst_1 : forall (i : ι), TopologicalSpace.{u2} (σ i)] {i : ι}, ClosedEmbedding.{u2, max u1 u2} (σ i) (Sigma.{u1, u2} ι σ) (_inst_1 i) (instTopologicalSpaceSigma.{u1, u2} ι σ (fun (a : ι) => _inst_1 a)) (Sigma.mk.{u1, u2} ι σ i)
Case conversion may be inaccurate. Consider using '#align closed_embedding_sigma_mk closedEmbedding_sigmaMkₓ'. -/
theorem closedEmbedding_sigmaMk {i : ι} : ClosedEmbedding (@Sigma.mk ι σ i) :=
  closedEmbedding_of_continuous_injective_closed continuous_sigmaMk sigma_mk_injective
    isClosedMap_sigmaMk
#align closed_embedding_sigma_mk closedEmbedding_sigmaMk

/- warning: embedding_sigma_mk -> embedding_sigmaMk is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : ι -> Type.{u2}} [_inst_1 : forall (i : ι), TopologicalSpace.{u2} (σ i)] {i : ι}, Embedding.{u2, max u1 u2} (σ i) (Sigma.{u1, u2} ι σ) (_inst_1 i) (Sigma.topologicalSpace.{u1, u2} ι σ (fun (a : ι) => _inst_1 a)) (Sigma.mk.{u1, u2} ι σ i)
but is expected to have type
  forall {ι : Type.{u1}} {σ : ι -> Type.{u2}} [_inst_1 : forall (i : ι), TopologicalSpace.{u2} (σ i)] {i : ι}, Embedding.{u2, max u1 u2} (σ i) (Sigma.{u1, u2} ι σ) (_inst_1 i) (instTopologicalSpaceSigma.{u1, u2} ι σ (fun (a : ι) => _inst_1 a)) (Sigma.mk.{u1, u2} ι σ i)
Case conversion may be inaccurate. Consider using '#align embedding_sigma_mk embedding_sigmaMkₓ'. -/
theorem embedding_sigmaMk {i : ι} : Embedding (@Sigma.mk ι σ i) :=
  closedEmbedding_sigmaMk.1
#align embedding_sigma_mk embedding_sigmaMk

/- warning: sigma.nhds_mk -> Sigma.nhds_mk is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : ι -> Type.{u2}} [_inst_1 : forall (i : ι), TopologicalSpace.{u2} (σ i)] (i : ι) (x : σ i), Eq.{succ (max u1 u2)} (Filter.{max u1 u2} (Sigma.{u1, u2} ι σ)) (nhds.{max u1 u2} (Sigma.{u1, u2} ι σ) (Sigma.topologicalSpace.{u1, u2} ι σ (fun (a : ι) => _inst_1 a)) (Sigma.mk.{u1, u2} ι σ i x)) (Filter.map.{u2, max u1 u2} (σ i) (Sigma.{u1, u2} ι σ) (Sigma.mk.{u1, u2} ι σ i) (nhds.{u2} (σ i) (_inst_1 i) x))
but is expected to have type
  forall {ι : Type.{u2}} {σ : ι -> Type.{u1}} [_inst_1 : forall (i : ι), TopologicalSpace.{u1} (σ i)] (i : ι) (x : σ i), Eq.{max (succ u2) (succ u1)} (Filter.{max u2 u1} (Sigma.{u2, u1} ι σ)) (nhds.{max u2 u1} (Sigma.{u2, u1} ι σ) (instTopologicalSpaceSigma.{u2, u1} ι σ (fun (a : ι) => _inst_1 a)) (Sigma.mk.{u2, u1} ι σ i x)) (Filter.map.{u1, max u2 u1} (σ i) (Sigma.{u2, u1} ι σ) (Sigma.mk.{u2, u1} ι σ i) (nhds.{u1} (σ i) (_inst_1 i) x))
Case conversion may be inaccurate. Consider using '#align sigma.nhds_mk Sigma.nhds_mkₓ'. -/
theorem Sigma.nhds_mk (i : ι) (x : σ i) : 𝓝 (⟨i, x⟩ : Sigma σ) = map (Sigma.mk i) (𝓝 x) :=
  (openEmbedding_sigmaMk.map_nhds_eq x).symm
#align sigma.nhds_mk Sigma.nhds_mk

/- warning: sigma.nhds_eq -> Sigma.nhds_eq is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : ι -> Type.{u2}} [_inst_1 : forall (i : ι), TopologicalSpace.{u2} (σ i)] (x : Sigma.{u1, u2} ι σ), Eq.{succ (max u1 u2)} (Filter.{max u1 u2} (Sigma.{u1, u2} ι σ)) (nhds.{max u1 u2} (Sigma.{u1, u2} ι σ) (Sigma.topologicalSpace.{u1, u2} ι σ (fun (a : ι) => _inst_1 a)) x) (Filter.map.{u2, max u1 u2} (σ (Sigma.fst.{u1, u2} ι σ x)) (Sigma.{u1, u2} ι σ) (Sigma.mk.{u1, u2} ι σ (Sigma.fst.{u1, u2} ι σ x)) (nhds.{u2} (σ (Sigma.fst.{u1, u2} ι σ x)) (_inst_1 (Sigma.fst.{u1, u2} ι σ x)) (Sigma.snd.{u1, u2} ι σ x)))
but is expected to have type
  forall {ι : Type.{u2}} {σ : ι -> Type.{u1}} [_inst_1 : forall (i : ι), TopologicalSpace.{u1} (σ i)] (x : Sigma.{u2, u1} ι σ), Eq.{max (succ u2) (succ u1)} (Filter.{max u2 u1} (Sigma.{u2, u1} ι σ)) (nhds.{max u2 u1} (Sigma.{u2, u1} ι σ) (instTopologicalSpaceSigma.{u2, u1} ι σ (fun (a : ι) => _inst_1 a)) x) (Filter.map.{u1, max u2 u1} (σ (Sigma.fst.{u2, u1} ι σ x)) (Sigma.{u2, u1} ι σ) (Sigma.mk.{u2, u1} ι σ (Sigma.fst.{u2, u1} ι σ x)) (nhds.{u1} (σ (Sigma.fst.{u2, u1} ι σ x)) (_inst_1 (Sigma.fst.{u2, u1} ι σ x)) (Sigma.snd.{u2, u1} ι σ x)))
Case conversion may be inaccurate. Consider using '#align sigma.nhds_eq Sigma.nhds_eqₓ'. -/
theorem Sigma.nhds_eq (x : Sigma σ) : 𝓝 x = map (Sigma.mk x.1) (𝓝 x.2) :=
  by
  cases x
  apply Sigma.nhds_mk
#align sigma.nhds_eq Sigma.nhds_eq

/- warning: comap_sigma_mk_nhds -> comap_sigmaMk_nhds is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : ι -> Type.{u2}} [_inst_1 : forall (i : ι), TopologicalSpace.{u2} (σ i)] (i : ι) (x : σ i), Eq.{succ u2} (Filter.{u2} (σ i)) (Filter.comap.{u2, max u1 u2} (σ i) (Sigma.{u1, u2} ι (fun (i : ι) => σ i)) (Sigma.mk.{u1, u2} ι (fun (i : ι) => σ i) i) (nhds.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => σ i)) (Sigma.topologicalSpace.{u1, u2} ι (fun (i : ι) => σ i) (fun (a : ι) => _inst_1 a)) (Sigma.mk.{u1, u2} ι (fun (i : ι) => σ i) i x))) (nhds.{u2} (σ i) (_inst_1 i) x)
but is expected to have type
  forall {ι : Type.{u1}} {σ : ι -> Type.{u2}} [_inst_1 : forall (i : ι), TopologicalSpace.{u2} (σ i)] (i : ι) (x : σ i), Eq.{succ u2} (Filter.{u2} (σ i)) (Filter.comap.{u2, max u1 u2} (σ i) (Sigma.{u1, u2} ι σ) (Sigma.mk.{u1, u2} ι σ i) (nhds.{max u1 u2} (Sigma.{u1, u2} ι σ) (instTopologicalSpaceSigma.{u1, u2} ι σ (fun (a : ι) => _inst_1 a)) (Sigma.mk.{u1, u2} ι σ i x))) (nhds.{u2} (σ i) (_inst_1 i) x)
Case conversion may be inaccurate. Consider using '#align comap_sigma_mk_nhds comap_sigmaMk_nhdsₓ'. -/
theorem comap_sigmaMk_nhds (i : ι) (x : σ i) : comap (Sigma.mk i) (𝓝 ⟨i, x⟩) = 𝓝 x :=
  (embedding_sigmaMk.to_inducing.nhds_eq_comap _).symm
#align comap_sigma_mk_nhds comap_sigmaMk_nhds

/- warning: is_open_sigma_fst_preimage -> isOpen_sigma_fst_preimage is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : ι -> Type.{u2}} [_inst_1 : forall (i : ι), TopologicalSpace.{u2} (σ i)] (s : Set.{u1} ι), IsOpen.{max u1 u2} (Sigma.{u1, u2} ι (fun (a : ι) => σ a)) (Sigma.topologicalSpace.{u1, u2} ι (fun (a : ι) => σ a) (fun (a : ι) => _inst_1 a)) (Set.preimage.{max u1 u2, u1} (Sigma.{u1, u2} ι (fun (a : ι) => σ a)) ι (Sigma.fst.{u1, u2} ι (fun (a : ι) => σ a)) s)
but is expected to have type
  forall {ι : Type.{u2}} {σ : ι -> Type.{u1}} [_inst_1 : forall (i : ι), TopologicalSpace.{u1} (σ i)] (s : Set.{u2} ι), IsOpen.{max u2 u1} (Sigma.{u2, u1} ι (fun (a : ι) => σ a)) (instTopologicalSpaceSigma.{u2, u1} ι (fun (a : ι) => σ a) (fun (a : ι) => _inst_1 a)) (Set.preimage.{max u2 u1, u2} (Sigma.{u2, u1} ι (fun (a : ι) => σ a)) ι (Sigma.fst.{u2, u1} ι (fun (a : ι) => σ a)) s)
Case conversion may be inaccurate. Consider using '#align is_open_sigma_fst_preimage isOpen_sigma_fst_preimageₓ'. -/
theorem isOpen_sigma_fst_preimage (s : Set ι) : IsOpen (Sigma.fst ⁻¹' s : Set (Σa, σ a)) :=
  by
  rw [← bUnion_of_singleton s, preimage_Union₂]
  simp only [← range_sigma_mk]
  exact isOpen_bunionᵢ fun _ _ => isOpen_range_sigmaMk
#align is_open_sigma_fst_preimage isOpen_sigma_fst_preimage

/- warning: continuous_sigma_iff -> continuous_sigma_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {σ : ι -> Type.{u3}} [_inst_1 : forall (i : ι), TopologicalSpace.{u3} (σ i)] [_inst_3 : TopologicalSpace.{u1} α] {f : (Sigma.{u2, u3} ι σ) -> α}, Iff (Continuous.{max u2 u3, u1} (Sigma.{u2, u3} ι σ) α (Sigma.topologicalSpace.{u2, u3} ι σ (fun (a : ι) => _inst_1 a)) _inst_3 f) (forall (i : ι), Continuous.{u3, u1} (σ i) α (_inst_1 i) _inst_3 (fun (a : σ i) => f (Sigma.mk.{u2, u3} ι σ i a)))
but is expected to have type
  forall {α : Type.{u3}} {ι : Type.{u2}} {σ : ι -> Type.{u1}} [_inst_1 : forall (i : ι), TopologicalSpace.{u1} (σ i)] [_inst_3 : TopologicalSpace.{u3} α] {f : (Sigma.{u2, u1} ι σ) -> α}, Iff (Continuous.{max u2 u1, u3} (Sigma.{u2, u1} ι σ) α (instTopologicalSpaceSigma.{u2, u1} ι σ (fun (a : ι) => _inst_1 a)) _inst_3 f) (forall (i : ι), Continuous.{u1, u3} (σ i) α (_inst_1 i) _inst_3 (fun (a : σ i) => f (Sigma.mk.{u2, u1} ι σ i a)))
Case conversion may be inaccurate. Consider using '#align continuous_sigma_iff continuous_sigma_iffₓ'. -/
/-- A map out of a sum type is continuous iff its restriction to each summand is. -/
@[simp]
theorem continuous_sigma_iff {f : Sigma σ → α} : Continuous f ↔ ∀ i, Continuous fun a => f ⟨i, a⟩ :=
  by simp only [continuous_supᵢ_dom, continuous_coinduced_dom]
#align continuous_sigma_iff continuous_sigma_iff

/- warning: continuous_sigma -> continuous_sigma is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {σ : ι -> Type.{u3}} [_inst_1 : forall (i : ι), TopologicalSpace.{u3} (σ i)] [_inst_3 : TopologicalSpace.{u1} α] {f : (Sigma.{u2, u3} ι σ) -> α}, (forall (i : ι), Continuous.{u3, u1} (σ i) α (_inst_1 i) _inst_3 (fun (a : σ i) => f (Sigma.mk.{u2, u3} ι σ i a))) -> (Continuous.{max u2 u3, u1} (Sigma.{u2, u3} ι σ) α (Sigma.topologicalSpace.{u2, u3} ι σ (fun (a : ι) => _inst_1 a)) _inst_3 f)
but is expected to have type
  forall {α : Type.{u3}} {ι : Type.{u2}} {σ : ι -> Type.{u1}} [_inst_1 : forall (i : ι), TopologicalSpace.{u1} (σ i)] [_inst_3 : TopologicalSpace.{u3} α] {f : (Sigma.{u2, u1} ι σ) -> α}, (forall (i : ι), Continuous.{u1, u3} (σ i) α (_inst_1 i) _inst_3 (fun (a : σ i) => f (Sigma.mk.{u2, u1} ι σ i a))) -> (Continuous.{max u2 u1, u3} (Sigma.{u2, u1} ι σ) α (instTopologicalSpaceSigma.{u2, u1} ι σ (fun (a : ι) => _inst_1 a)) _inst_3 f)
Case conversion may be inaccurate. Consider using '#align continuous_sigma continuous_sigmaₓ'. -/
/-- A map out of a sum type is continuous if its restriction to each summand is. -/
@[continuity]
theorem continuous_sigma {f : Sigma σ → α} (hf : ∀ i, Continuous fun a => f ⟨i, a⟩) :
    Continuous f :=
  continuous_sigma_iff.2 hf
#align continuous_sigma continuous_sigma

/- warning: continuous_sigma_map -> continuous_sigma_map is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {κ : Type.{u2}} {σ : ι -> Type.{u3}} {τ : κ -> Type.{u4}} [_inst_1 : forall (i : ι), TopologicalSpace.{u3} (σ i)] [_inst_2 : forall (k : κ), TopologicalSpace.{u4} (τ k)] {f₁ : ι -> κ} {f₂ : forall (i : ι), (σ i) -> (τ (f₁ i))}, Iff (Continuous.{max u1 u3, max u2 u4} (Sigma.{u1, u3} ι (fun (i : ι) => σ i)) (Sigma.{u2, u4} κ τ) (Sigma.topologicalSpace.{u1, u3} ι (fun (i : ι) => σ i) (fun (a : ι) => _inst_1 a)) (Sigma.topologicalSpace.{u2, u4} κ τ (fun (a : κ) => _inst_2 a)) (Sigma.map.{u1, u2, u3, u4} ι κ (fun (i : ι) => σ i) τ f₁ f₂)) (forall (i : ι), Continuous.{u3, u4} (σ i) (τ (f₁ i)) (_inst_1 i) (_inst_2 (f₁ i)) (f₂ i))
but is expected to have type
  forall {ι : Type.{u3}} {κ : Type.{u1}} {σ : ι -> Type.{u4}} {τ : κ -> Type.{u2}} [_inst_1 : forall (i : ι), TopologicalSpace.{u4} (σ i)] [_inst_2 : forall (k : κ), TopologicalSpace.{u2} (τ k)] {f₁ : ι -> κ} {f₂ : forall (i : ι), (σ i) -> (τ (f₁ i))}, Iff (Continuous.{max u4 u3, max u2 u1} (Sigma.{u3, u4} ι (fun (i : ι) => σ i)) (Sigma.{u1, u2} κ τ) (instTopologicalSpaceSigma.{u3, u4} ι (fun (i : ι) => σ i) (fun (a : ι) => _inst_1 a)) (instTopologicalSpaceSigma.{u1, u2} κ τ (fun (a : κ) => _inst_2 a)) (Sigma.map.{u3, u1, u4, u2} ι κ (fun (i : ι) => σ i) τ f₁ f₂)) (forall (i : ι), Continuous.{u4, u2} (σ i) (τ (f₁ i)) (_inst_1 i) (_inst_2 (f₁ i)) (f₂ i))
Case conversion may be inaccurate. Consider using '#align continuous_sigma_map continuous_sigma_mapₓ'. -/
@[simp]
theorem continuous_sigma_map {f₁ : ι → κ} {f₂ : ∀ i, σ i → τ (f₁ i)} :
    Continuous (Sigma.map f₁ f₂) ↔ ∀ i, Continuous (f₂ i) :=
  continuous_sigma_iff.trans <| by simp only [Sigma.map, embedding_sigma_mk.continuous_iff]
#align continuous_sigma_map continuous_sigma_map

/- warning: continuous.sigma_map -> Continuous.sigma_map is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {κ : Type.{u2}} {σ : ι -> Type.{u3}} {τ : κ -> Type.{u4}} [_inst_1 : forall (i : ι), TopologicalSpace.{u3} (σ i)] [_inst_2 : forall (k : κ), TopologicalSpace.{u4} (τ k)] {f₁ : ι -> κ} {f₂ : forall (i : ι), (σ i) -> (τ (f₁ i))}, (forall (i : ι), Continuous.{u3, u4} (σ i) (τ (f₁ i)) (_inst_1 i) (_inst_2 (f₁ i)) (f₂ i)) -> (Continuous.{max u1 u3, max u2 u4} (Sigma.{u1, u3} ι (fun (i : ι) => σ i)) (Sigma.{u2, u4} κ τ) (Sigma.topologicalSpace.{u1, u3} ι (fun (i : ι) => σ i) (fun (a : ι) => _inst_1 a)) (Sigma.topologicalSpace.{u2, u4} κ τ (fun (a : κ) => _inst_2 a)) (Sigma.map.{u1, u2, u3, u4} ι κ (fun (i : ι) => σ i) τ f₁ f₂))
but is expected to have type
  forall {ι : Type.{u2}} {κ : Type.{u1}} {σ : ι -> Type.{u4}} {τ : κ -> Type.{u3}} [_inst_1 : forall (i : ι), TopologicalSpace.{u4} (σ i)] [_inst_2 : forall (k : κ), TopologicalSpace.{u3} (τ k)] {f₁ : ι -> κ} {f₂ : forall (i : ι), (σ i) -> (τ (f₁ i))}, (forall (i : ι), Continuous.{u4, u3} (σ i) (τ (f₁ i)) (_inst_1 i) (_inst_2 (f₁ i)) (f₂ i)) -> (Continuous.{max u4 u2, max u3 u1} (Sigma.{u2, u4} ι (fun (i : ι) => σ i)) (Sigma.{u1, u3} κ τ) (instTopologicalSpaceSigma.{u2, u4} ι (fun (i : ι) => σ i) (fun (a : ι) => _inst_1 a)) (instTopologicalSpaceSigma.{u1, u3} κ τ (fun (a : κ) => _inst_2 a)) (Sigma.map.{u2, u1, u4, u3} ι κ (fun (i : ι) => σ i) τ f₁ f₂))
Case conversion may be inaccurate. Consider using '#align continuous.sigma_map Continuous.sigma_mapₓ'. -/
@[continuity]
theorem Continuous.sigma_map {f₁ : ι → κ} {f₂ : ∀ i, σ i → τ (f₁ i)} (hf : ∀ i, Continuous (f₂ i)) :
    Continuous (Sigma.map f₁ f₂) :=
  continuous_sigma_map.2 hf
#align continuous.sigma_map Continuous.sigma_map

/- warning: is_open_map_sigma -> isOpenMap_sigma is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {σ : ι -> Type.{u3}} [_inst_1 : forall (i : ι), TopologicalSpace.{u3} (σ i)] [_inst_3 : TopologicalSpace.{u1} α] {f : (Sigma.{u2, u3} ι σ) -> α}, Iff (IsOpenMap.{max u2 u3, u1} (Sigma.{u2, u3} ι σ) α (Sigma.topologicalSpace.{u2, u3} ι σ (fun (a : ι) => _inst_1 a)) _inst_3 f) (forall (i : ι), IsOpenMap.{u3, u1} (σ i) α (_inst_1 i) _inst_3 (fun (a : σ i) => f (Sigma.mk.{u2, u3} ι σ i a)))
but is expected to have type
  forall {α : Type.{u3}} {ι : Type.{u2}} {σ : ι -> Type.{u1}} [_inst_1 : forall (i : ι), TopologicalSpace.{u1} (σ i)] [_inst_3 : TopologicalSpace.{u3} α] {f : (Sigma.{u2, u1} ι σ) -> α}, Iff (IsOpenMap.{max u2 u1, u3} (Sigma.{u2, u1} ι σ) α (instTopologicalSpaceSigma.{u2, u1} ι σ (fun (a : ι) => _inst_1 a)) _inst_3 f) (forall (i : ι), IsOpenMap.{u1, u3} (σ i) α (_inst_1 i) _inst_3 (fun (a : σ i) => f (Sigma.mk.{u2, u1} ι σ i a)))
Case conversion may be inaccurate. Consider using '#align is_open_map_sigma isOpenMap_sigmaₓ'. -/
theorem isOpenMap_sigma {f : Sigma σ → α} : IsOpenMap f ↔ ∀ i, IsOpenMap fun a => f ⟨i, a⟩ := by
  simp only [isOpenMap_iff_nhds_le, Sigma.forall, Sigma.nhds_eq, map_map]
#align is_open_map_sigma isOpenMap_sigma

/- warning: is_open_map_sigma_map -> isOpenMap_sigma_map is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {κ : Type.{u2}} {σ : ι -> Type.{u3}} {τ : κ -> Type.{u4}} [_inst_1 : forall (i : ι), TopologicalSpace.{u3} (σ i)] [_inst_2 : forall (k : κ), TopologicalSpace.{u4} (τ k)] {f₁ : ι -> κ} {f₂ : forall (i : ι), (σ i) -> (τ (f₁ i))}, Iff (IsOpenMap.{max u1 u3, max u2 u4} (Sigma.{u1, u3} ι (fun (i : ι) => σ i)) (Sigma.{u2, u4} κ τ) (Sigma.topologicalSpace.{u1, u3} ι (fun (i : ι) => σ i) (fun (a : ι) => _inst_1 a)) (Sigma.topologicalSpace.{u2, u4} κ τ (fun (a : κ) => _inst_2 a)) (Sigma.map.{u1, u2, u3, u4} ι κ (fun (i : ι) => σ i) τ f₁ f₂)) (forall (i : ι), IsOpenMap.{u3, u4} (σ i) (τ (f₁ i)) (_inst_1 i) (_inst_2 (f₁ i)) (f₂ i))
but is expected to have type
  forall {ι : Type.{u3}} {κ : Type.{u1}} {σ : ι -> Type.{u4}} {τ : κ -> Type.{u2}} [_inst_1 : forall (i : ι), TopologicalSpace.{u4} (σ i)] [_inst_2 : forall (k : κ), TopologicalSpace.{u2} (τ k)] {f₁ : ι -> κ} {f₂ : forall (i : ι), (σ i) -> (τ (f₁ i))}, Iff (IsOpenMap.{max u4 u3, max u2 u1} (Sigma.{u3, u4} ι (fun (i : ι) => σ i)) (Sigma.{u1, u2} κ τ) (instTopologicalSpaceSigma.{u3, u4} ι (fun (i : ι) => σ i) (fun (a : ι) => _inst_1 a)) (instTopologicalSpaceSigma.{u1, u2} κ τ (fun (a : κ) => _inst_2 a)) (Sigma.map.{u3, u1, u4, u2} ι κ (fun (i : ι) => σ i) τ f₁ f₂)) (forall (i : ι), IsOpenMap.{u4, u2} (σ i) (τ (f₁ i)) (_inst_1 i) (_inst_2 (f₁ i)) (f₂ i))
Case conversion may be inaccurate. Consider using '#align is_open_map_sigma_map isOpenMap_sigma_mapₓ'. -/
theorem isOpenMap_sigma_map {f₁ : ι → κ} {f₂ : ∀ i, σ i → τ (f₁ i)} :
    IsOpenMap (Sigma.map f₁ f₂) ↔ ∀ i, IsOpenMap (f₂ i) :=
  isOpenMap_sigma.trans <|
    forall_congr' fun i => (@openEmbedding_sigmaMk _ _ _ (f₁ i)).isOpenMap_iff.symm
#align is_open_map_sigma_map isOpenMap_sigma_map

/- warning: inducing_sigma_map -> inducing_sigma_map is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {κ : Type.{u2}} {σ : ι -> Type.{u3}} {τ : κ -> Type.{u4}} [_inst_1 : forall (i : ι), TopologicalSpace.{u3} (σ i)] [_inst_2 : forall (k : κ), TopologicalSpace.{u4} (τ k)] {f₁ : ι -> κ} {f₂ : forall (i : ι), (σ i) -> (τ (f₁ i))}, (Function.Injective.{succ u1, succ u2} ι κ f₁) -> (Iff (Inducing.{max u1 u3, max u2 u4} (Sigma.{u1, u3} ι (fun (i : ι) => σ i)) (Sigma.{u2, u4} κ τ) (Sigma.topologicalSpace.{u1, u3} ι (fun (i : ι) => σ i) (fun (a : ι) => _inst_1 a)) (Sigma.topologicalSpace.{u2, u4} κ τ (fun (a : κ) => _inst_2 a)) (Sigma.map.{u1, u2, u3, u4} ι κ (fun (i : ι) => σ i) τ f₁ f₂)) (forall (i : ι), Inducing.{u3, u4} (σ i) (τ (f₁ i)) (_inst_1 i) (_inst_2 (f₁ i)) (f₂ i)))
but is expected to have type
  forall {ι : Type.{u4}} {κ : Type.{u3}} {σ : ι -> Type.{u2}} {τ : κ -> Type.{u1}} [_inst_1 : forall (i : ι), TopologicalSpace.{u2} (σ i)] [_inst_2 : forall (k : κ), TopologicalSpace.{u1} (τ k)] {f₁ : ι -> κ} {f₂ : forall (i : ι), (σ i) -> (τ (f₁ i))}, (Function.Injective.{succ u4, succ u3} ι κ f₁) -> (Iff (Inducing.{max u2 u4, max u1 u3} (Sigma.{u4, u2} ι (fun (i : ι) => σ i)) (Sigma.{u3, u1} κ τ) (instTopologicalSpaceSigma.{u4, u2} ι (fun (i : ι) => σ i) (fun (a : ι) => _inst_1 a)) (instTopologicalSpaceSigma.{u3, u1} κ τ (fun (a : κ) => _inst_2 a)) (Sigma.map.{u4, u3, u2, u1} ι κ (fun (i : ι) => σ i) τ f₁ f₂)) (forall (i : ι), Inducing.{u2, u1} (σ i) (τ (f₁ i)) (_inst_1 i) (_inst_2 (f₁ i)) (f₂ i)))
Case conversion may be inaccurate. Consider using '#align inducing_sigma_map inducing_sigma_mapₓ'. -/
theorem inducing_sigma_map {f₁ : ι → κ} {f₂ : ∀ i, σ i → τ (f₁ i)} (h₁ : Injective f₁) :
    Inducing (Sigma.map f₁ f₂) ↔ ∀ i, Inducing (f₂ i) := by
  simp only [inducing_iff_nhds, Sigma.forall, Sigma.nhds_mk, Sigma.map, ← map_sigma_mk_comap h₁,
    map_inj sigma_mk_injective]
#align inducing_sigma_map inducing_sigma_map

/- warning: embedding_sigma_map -> embedding_sigma_map is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {κ : Type.{u2}} {σ : ι -> Type.{u3}} {τ : κ -> Type.{u4}} [_inst_1 : forall (i : ι), TopologicalSpace.{u3} (σ i)] [_inst_2 : forall (k : κ), TopologicalSpace.{u4} (τ k)] {f₁ : ι -> κ} {f₂ : forall (i : ι), (σ i) -> (τ (f₁ i))}, (Function.Injective.{succ u1, succ u2} ι κ f₁) -> (Iff (Embedding.{max u1 u3, max u2 u4} (Sigma.{u1, u3} ι (fun (i : ι) => σ i)) (Sigma.{u2, u4} κ τ) (Sigma.topologicalSpace.{u1, u3} ι (fun (i : ι) => σ i) (fun (a : ι) => _inst_1 a)) (Sigma.topologicalSpace.{u2, u4} κ τ (fun (a : κ) => _inst_2 a)) (Sigma.map.{u1, u2, u3, u4} ι κ (fun (i : ι) => σ i) τ f₁ f₂)) (forall (i : ι), Embedding.{u3, u4} (σ i) (τ (f₁ i)) (_inst_1 i) (_inst_2 (f₁ i)) (f₂ i)))
but is expected to have type
  forall {ι : Type.{u4}} {κ : Type.{u3}} {σ : ι -> Type.{u2}} {τ : κ -> Type.{u1}} [_inst_1 : forall (i : ι), TopologicalSpace.{u2} (σ i)] [_inst_2 : forall (k : κ), TopologicalSpace.{u1} (τ k)] {f₁ : ι -> κ} {f₂ : forall (i : ι), (σ i) -> (τ (f₁ i))}, (Function.Injective.{succ u4, succ u3} ι κ f₁) -> (Iff (Embedding.{max u2 u4, max u1 u3} (Sigma.{u4, u2} ι (fun (i : ι) => σ i)) (Sigma.{u3, u1} κ τ) (instTopologicalSpaceSigma.{u4, u2} ι (fun (i : ι) => σ i) (fun (a : ι) => _inst_1 a)) (instTopologicalSpaceSigma.{u3, u1} κ τ (fun (a : κ) => _inst_2 a)) (Sigma.map.{u4, u3, u2, u1} ι κ (fun (i : ι) => σ i) τ f₁ f₂)) (forall (i : ι), Embedding.{u2, u1} (σ i) (τ (f₁ i)) (_inst_1 i) (_inst_2 (f₁ i)) (f₂ i)))
Case conversion may be inaccurate. Consider using '#align embedding_sigma_map embedding_sigma_mapₓ'. -/
theorem embedding_sigma_map {f₁ : ι → κ} {f₂ : ∀ i, σ i → τ (f₁ i)} (h : Injective f₁) :
    Embedding (Sigma.map f₁ f₂) ↔ ∀ i, Embedding (f₂ i) := by
  simp only [embedding_iff, injective.sigma_map, inducing_sigma_map h, forall_and, h.sigma_map_iff]
#align embedding_sigma_map embedding_sigma_map

/- warning: open_embedding_sigma_map -> openEmbedding_sigma_map is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {κ : Type.{u2}} {σ : ι -> Type.{u3}} {τ : κ -> Type.{u4}} [_inst_1 : forall (i : ι), TopologicalSpace.{u3} (σ i)] [_inst_2 : forall (k : κ), TopologicalSpace.{u4} (τ k)] {f₁ : ι -> κ} {f₂ : forall (i : ι), (σ i) -> (τ (f₁ i))}, (Function.Injective.{succ u1, succ u2} ι κ f₁) -> (Iff (OpenEmbedding.{max u1 u3, max u2 u4} (Sigma.{u1, u3} ι (fun (i : ι) => σ i)) (Sigma.{u2, u4} κ τ) (Sigma.topologicalSpace.{u1, u3} ι (fun (i : ι) => σ i) (fun (a : ι) => _inst_1 a)) (Sigma.topologicalSpace.{u2, u4} κ τ (fun (a : κ) => _inst_2 a)) (Sigma.map.{u1, u2, u3, u4} ι κ (fun (i : ι) => σ i) τ f₁ f₂)) (forall (i : ι), OpenEmbedding.{u3, u4} (σ i) (τ (f₁ i)) (_inst_1 i) (_inst_2 (f₁ i)) (f₂ i)))
but is expected to have type
  forall {ι : Type.{u4}} {κ : Type.{u3}} {σ : ι -> Type.{u2}} {τ : κ -> Type.{u1}} [_inst_1 : forall (i : ι), TopologicalSpace.{u2} (σ i)] [_inst_2 : forall (k : κ), TopologicalSpace.{u1} (τ k)] {f₁ : ι -> κ} {f₂ : forall (i : ι), (σ i) -> (τ (f₁ i))}, (Function.Injective.{succ u4, succ u3} ι κ f₁) -> (Iff (OpenEmbedding.{max u2 u4, max u1 u3} (Sigma.{u4, u2} ι (fun (i : ι) => σ i)) (Sigma.{u3, u1} κ τ) (instTopologicalSpaceSigma.{u4, u2} ι (fun (i : ι) => σ i) (fun (a : ι) => _inst_1 a)) (instTopologicalSpaceSigma.{u3, u1} κ τ (fun (a : κ) => _inst_2 a)) (Sigma.map.{u4, u3, u2, u1} ι κ (fun (i : ι) => σ i) τ f₁ f₂)) (forall (i : ι), OpenEmbedding.{u2, u1} (σ i) (τ (f₁ i)) (_inst_1 i) (_inst_2 (f₁ i)) (f₂ i)))
Case conversion may be inaccurate. Consider using '#align open_embedding_sigma_map openEmbedding_sigma_mapₓ'. -/
theorem openEmbedding_sigma_map {f₁ : ι → κ} {f₂ : ∀ i, σ i → τ (f₁ i)} (h : Injective f₁) :
    OpenEmbedding (Sigma.map f₁ f₂) ↔ ∀ i, OpenEmbedding (f₂ i) := by
  simp only [openEmbedding_iff_embedding_open, isOpenMap_sigma_map, embedding_sigma_map h,
    forall_and]
#align open_embedding_sigma_map openEmbedding_sigma_map

end Sigma

section ULift

#print continuous_uLift_down /-
@[continuity]
theorem continuous_uLift_down [TopologicalSpace α] : Continuous (ULift.down : ULift.{v, u} α → α) :=
  continuous_induced_dom
#align continuous_ulift_down continuous_uLift_down
-/

#print continuous_uLift_up /-
@[continuity]
theorem continuous_uLift_up [TopologicalSpace α] : Continuous (ULift.up : α → ULift.{v, u} α) :=
  continuous_induced_rng.2 continuous_id
#align continuous_ulift_up continuous_uLift_up
-/

#print embedding_uLift_down /-
theorem embedding_uLift_down [TopologicalSpace α] : Embedding (ULift.down : ULift.{v, u} α → α) :=
  ⟨⟨rfl⟩, ULift.down_injective⟩
#align embedding_ulift_down embedding_uLift_down
-/

instance [TopologicalSpace α] [DiscreteTopology α] : DiscreteTopology (ULift α) :=
  embedding_uLift_down.DiscreteTopology

end ULift

