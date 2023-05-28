/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module topology.order
! leanprover-community/mathlib commit e46da4e335b8671848ac711ccb34b42538c0d800
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Tactic

/-!
# Ordering on topologies and (co)induced topologies

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Topologies on a fixed type `α` are ordered, by reverse inclusion.
That is, for topologies `t₁` and `t₂` on `α`, we write `t₁ ≤ t₂`
if every set open in `t₂` is also open in `t₁`.
(One also calls `t₁` finer than `t₂`, and `t₂` coarser than `t₁`.)

Any function `f : α → β` induces
       `induced f : topological_space β → topological_space α`
and  `coinduced f : topological_space α → topological_space β`.
Continuity, the ordering on topologies and (co)induced topologies are
related as follows:
* The identity map (α, t₁) → (α, t₂) is continuous iff t₁ ≤ t₂.
* A map f : (α, t) → (β, u) is continuous
    iff             t ≤ induced f u   (`continuous_iff_le_induced`)
    iff coinduced f t ≤ u             (`continuous_iff_coinduced_le`).

Topologies on α form a complete lattice, with ⊥ the discrete topology
and ⊤ the indiscrete topology.

For a function f : α → β, (coinduced f, induced f) is a Galois connection
between topologies on α and topologies on β.

## Implementation notes

There is a Galois insertion between topologies on α (with the inclusion ordering)
and all collections of sets in α. The complete lattice structure on topologies
on α is defined as the reverse of the one obtained via this Galois insertion.

## Tags

finer, coarser, induced topology, coinduced topology

-/


open Function Set Filter

open Topology Filter

universe u v w

namespace TopologicalSpace

variable {α : Type u}

#print TopologicalSpace.GenerateOpen /-
/-- The open sets of the least topology containing a collection of basic sets. -/
inductive GenerateOpen (g : Set (Set α)) : Set α → Prop
  | basic : ∀ s ∈ g, generate_open s
  | univ : generate_open univ
  | inter : ∀ s t, generate_open s → generate_open t → generate_open (s ∩ t)
  | sUnion : ∀ k, (∀ s ∈ k, generate_open s) → generate_open (⋃₀ k)
#align topological_space.generate_open TopologicalSpace.GenerateOpen
-/

#print TopologicalSpace.generateFrom /-
/-- The smallest topological space containing the collection `g` of basic sets -/
def generateFrom (g : Set (Set α)) : TopologicalSpace α
    where
  IsOpen := GenerateOpen g
  isOpen_univ := GenerateOpen.univ
  isOpen_inter := GenerateOpen.inter
  isOpen_sUnion := GenerateOpen.sUnion
#align topological_space.generate_from TopologicalSpace.generateFrom
-/

#print TopologicalSpace.isOpen_generateFrom_of_mem /-
theorem isOpen_generateFrom_of_mem {g : Set (Set α)} {s : Set α} (hs : s ∈ g) :
    is_open[generateFrom g] s :=
  GenerateOpen.basic s hs
#align topological_space.is_open_generate_from_of_mem TopologicalSpace.isOpen_generateFrom_of_mem
-/

/- warning: topological_space.nhds_generate_from -> TopologicalSpace.nhds_generateFrom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {g : Set.{u1} (Set.{u1} α)} {a : α}, Eq.{succ u1} (Filter.{u1} α) (nhds.{u1} α (TopologicalSpace.generateFrom.{u1} α g) a) (iInf.{u1, succ u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (Set.{u1} α) (fun (s : Set.{u1} α) => iInf.{u1, 0} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s g)))) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s g)))) => Filter.principal.{u1} α s)))
but is expected to have type
  forall {α : Type.{u1}} {g : Set.{u1} (Set.{u1} α)} {a : α}, Eq.{succ u1} (Filter.{u1} α) (nhds.{u1} α (TopologicalSpace.generateFrom.{u1} α g) a) (iInf.{u1, succ u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toInfSet.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))) (Set.{u1} α) (fun (s : Set.{u1} α) => iInf.{u1, 0} (Filter.{u1} α) (ConditionallyCompleteLattice.toInfSet.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))) (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s g)))) (fun (H : Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s g)))) => Filter.principal.{u1} α s)))
Case conversion may be inaccurate. Consider using '#align topological_space.nhds_generate_from TopologicalSpace.nhds_generateFromₓ'. -/
theorem nhds_generateFrom {g : Set (Set α)} {a : α} :
    @nhds α (generateFrom g) a = ⨅ s ∈ { s | a ∈ s ∧ s ∈ g }, 𝓟 s :=
  by
  rw [nhds_def]
  refine' le_antisymm (biInf_mono fun s ⟨as, sg⟩ => ⟨as, generate_open.basic _ sg⟩) _
  refine' le_iInf₂ fun s hs => _; cases' hs with ha hs
  induction hs
  case basic s hs => exact iInf₂_le _ ⟨ha, hs⟩
  case univ => exact le_top.trans_eq principal_univ.symm
  case inter s t hs' ht' hs ht => exact (le_inf (hs ha.1) (ht ha.2)).trans_eq inf_principal
  case sUnion S hS' hS =>
    rcases ha with ⟨t, htS, hat⟩
    exact (hS t htS hat).trans (principal_mono.2 <| subset_sUnion_of_mem htS)
#align topological_space.nhds_generate_from TopologicalSpace.nhds_generateFrom

/- warning: topological_space.tendsto_nhds_generate_from -> TopologicalSpace.tendsto_nhds_generateFrom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : α -> β} {f : Filter.{u1} α} {g : Set.{u2} (Set.{u2} β)} {b : β}, (forall (s : Set.{u2} β), (Membership.Mem.{u2, u2} (Set.{u2} β) (Set.{u2} (Set.{u2} β)) (Set.hasMem.{u2} (Set.{u2} β)) s g) -> (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b s) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (Set.preimage.{u1, u2} α β m s) f)) -> (Filter.Tendsto.{u1, u2} α β m f (nhds.{u2} β (TopologicalSpace.generateFrom.{u2} β g) b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : α -> β} {f : Filter.{u2} α} {g : Set.{u1} (Set.{u1} β)} {b : β}, (forall (s : Set.{u1} β), (Membership.mem.{u1, u1} (Set.{u1} β) (Set.{u1} (Set.{u1} β)) (Set.instMembershipSet.{u1} (Set.{u1} β)) s g) -> (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) b s) -> (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) (Set.preimage.{u2, u1} α β m s) f)) -> (Filter.Tendsto.{u2, u1} α β m f (nhds.{u1} β (TopologicalSpace.generateFrom.{u1} β g) b))
Case conversion may be inaccurate. Consider using '#align topological_space.tendsto_nhds_generate_from TopologicalSpace.tendsto_nhds_generateFromₓ'. -/
theorem tendsto_nhds_generateFrom {β : Type _} {m : α → β} {f : Filter α} {g : Set (Set β)} {b : β}
    (h : ∀ s ∈ g, b ∈ s → m ⁻¹' s ∈ f) : Tendsto m f (@nhds β (generateFrom g) b) := by
  rw [nhds_generate_from] <;>
    exact
      tendsto_infi.2 fun s => tendsto_infi.2 fun ⟨hbs, hsg⟩ => tendsto_principal.2 <| h s hsg hbs
#align topological_space.tendsto_nhds_generate_from TopologicalSpace.tendsto_nhds_generateFrom

#print TopologicalSpace.mkOfNhds /-
/-- Construct a topology on α given the filter of neighborhoods of each point of α. -/
protected def mkOfNhds (n : α → Filter α) : TopologicalSpace α
    where
  IsOpen s := ∀ a ∈ s, s ∈ n a
  isOpen_univ x h := univ_mem
  isOpen_inter := fun s t hs ht x ⟨hxs, hxt⟩ => inter_mem (hs x hxs) (ht x hxt)
  isOpen_sUnion := fun s hs a ⟨x, hx, hxa⟩ =>
    mem_of_superset (hs x hx _ hxa) (Set.subset_sUnion_of_mem hx)
#align topological_space.mk_of_nhds TopologicalSpace.mkOfNhds
-/

/- warning: topological_space.nhds_mk_of_nhds -> TopologicalSpace.nhds_mkOfNhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (n : α -> (Filter.{u1} α)) (a : α), (LE.le.{u1} (α -> (Filter.{u1} α)) (Pi.hasLe.{u1, u1} α (fun (ᾰ : α) => Filter.{u1} α) (fun (i : α) => Preorder.toHasLe.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α)))) (Pure.pure.{u1, u1} (fun {α : Type.{u1}} => Filter.{u1} α) Filter.hasPure.{u1} α) n) -> (forall (a : α) (s : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (n a)) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t (n a)) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t (n a)) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s) (forall (a' : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a' t) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (n a'))))))) -> (Eq.{succ u1} (Filter.{u1} α) (nhds.{u1} α (TopologicalSpace.mkOfNhds.{u1} α n) a) (n a))
but is expected to have type
  forall {α : Type.{u1}} (n : α -> (Filter.{u1} α)) (a : α), (LE.le.{u1} (α -> (Filter.{u1} α)) (Pi.hasLe.{u1, u1} α (fun (ᾰ : α) => Filter.{u1} α) (fun (i : α) => Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α)))) (Pure.pure.{u1, u1} Filter.{u1} Filter.instPureFilter.{u1} α) n) -> (forall (a : α) (s : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (n a)) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t (n a)) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t s) (forall (a' : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a' t) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (n a'))))))) -> (Eq.{succ u1} (Filter.{u1} α) (nhds.{u1} α (TopologicalSpace.mkOfNhds.{u1} α n) a) (n a))
Case conversion may be inaccurate. Consider using '#align topological_space.nhds_mk_of_nhds TopologicalSpace.nhds_mkOfNhdsₓ'. -/
theorem nhds_mkOfNhds (n : α → Filter α) (a : α) (h₀ : pure ≤ n)
    (h₁ : ∀ a s, s ∈ n a → ∃ t ∈ n a, t ⊆ s ∧ ∀ a' ∈ t, s ∈ n a') :
    @nhds α (TopologicalSpace.mkOfNhds n) a = n a :=
  by
  letI := TopologicalSpace.mkOfNhds n
  refine' le_antisymm (fun s hs => _) fun s hs => _
  · have h₀ : { b | s ∈ n b } ⊆ s := fun b hb => mem_pure.1 <| h₀ b hb
    have h₁ : { b | s ∈ n b } ∈ 𝓝 a :=
      by
      refine' IsOpen.mem_nhds (fun b (hb : s ∈ n b) => _) hs
      rcases h₁ _ _ hb with ⟨t, ht, hts, h⟩
      exact mem_of_superset ht h
    exact mem_of_superset h₁ h₀
  · rcases(@mem_nhds_iff α (TopologicalSpace.mkOfNhds n) _ _).1 hs with ⟨t, hts, ht, hat⟩
    exact (n a).sets_of_superset (ht _ hat) hts
#align topological_space.nhds_mk_of_nhds TopologicalSpace.nhds_mkOfNhds

/- warning: topological_space.nhds_mk_of_nhds_single -> TopologicalSpace.nhds_mkOfNhds_single is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {a₀ : α} {l : Filter.{u1} α}, (LE.le.{u1} (Filter.{u1} α) (Preorder.toHasLe.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (Pure.pure.{u1, u1} (fun {α : Type.{u1}} => Filter.{u1} α) Filter.hasPure.{u1} α a₀) l) -> (forall (b : α), Eq.{succ u1} (Filter.{u1} α) (nhds.{u1} α (TopologicalSpace.mkOfNhds.{u1} α (Function.update.{succ u1, succ u1} α (fun (ᾰ : α) => Filter.{u1} α) (fun (a : α) (b : α) => _inst_1 a b) (Pure.pure.{u1, u1} (fun {α : Type.{u1}} => Filter.{u1} α) Filter.hasPure.{u1} α) a₀ l)) b) (Function.update.{succ u1, succ u1} α (fun (ᾰ : α) => Filter.{u1} α) (fun (a : α) (b : α) => _inst_1 a b) (Pure.pure.{u1, u1} (fun {α : Type.{u1}} => Filter.{u1} α) Filter.hasPure.{u1} α) a₀ l b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {a₀ : α} {l : Filter.{u1} α}, (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (Pure.pure.{u1, u1} Filter.{u1} Filter.instPureFilter.{u1} α a₀) l) -> (forall (b : α), Eq.{succ u1} (Filter.{u1} α) (nhds.{u1} α (TopologicalSpace.mkOfNhds.{u1} α (Function.update.{succ u1, succ u1} α (fun (ᾰ : α) => Filter.{u1} α) (fun (a : α) (b : α) => _inst_1 a b) (Pure.pure.{u1, u1} Filter.{u1} Filter.instPureFilter.{u1} α) a₀ l)) b) (Function.update.{succ u1, succ u1} α (fun (ᾰ : α) => Filter.{u1} α) (fun (a : α) (b : α) => _inst_1 a b) (Pure.pure.{u1, u1} Filter.{u1} Filter.instPureFilter.{u1} α) a₀ l b))
Case conversion may be inaccurate. Consider using '#align topological_space.nhds_mk_of_nhds_single TopologicalSpace.nhds_mkOfNhds_singleₓ'. -/
theorem nhds_mkOfNhds_single [DecidableEq α] {a₀ : α} {l : Filter α} (h : pure a₀ ≤ l) (b : α) :
    @nhds α (TopologicalSpace.mkOfNhds <| update pure a₀ l) b =
      (update pure a₀ l : α → Filter α) b :=
  by
  refine' nhds_mk_of_nhds _ _ (le_update_iff.mpr ⟨h, fun _ _ => le_rfl⟩) fun a s hs => _
  rcases eq_or_ne a a₀ with (rfl | ha)
  · refine' ⟨s, hs, subset.rfl, fun b hb => _⟩
    rcases eq_or_ne b a with (rfl | hb)
    · exact hs
    · rwa [update_noteq hb]
  · have hs' := hs
    rw [update_noteq ha] at hs⊢
    exact ⟨{a}, rfl, singleton_subset_iff.mpr hs, forall_eq.2 hs'⟩
#align topological_space.nhds_mk_of_nhds_single TopologicalSpace.nhds_mkOfNhds_single

/- warning: topological_space.nhds_mk_of_nhds_filter_basis -> TopologicalSpace.nhds_mkOfNhds_filterBasis is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (B : α -> (FilterBasis.{u1} α)) (a : α), (forall (x : α) (n : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (FilterBasis.{u1} α) (FilterBasis.hasMem.{u1} α) n (B x)) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x n)) -> (forall (x : α) (n : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (FilterBasis.{u1} α) (FilterBasis.hasMem.{u1} α) n (B x)) -> (Exists.{succ u1} (Set.{u1} α) (fun (n₁ : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (FilterBasis.{u1} α) (FilterBasis.hasMem.{u1} α) n₁ (B x)) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (FilterBasis.{u1} α) (FilterBasis.hasMem.{u1} α) n₁ (B x)) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) n₁ n) (forall (x' : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x' n₁) -> (Exists.{succ u1} (Set.{u1} α) (fun (n₂ : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (FilterBasis.{u1} α) (FilterBasis.hasMem.{u1} α) n₂ (B x')) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (FilterBasis.{u1} α) (FilterBasis.hasMem.{u1} α) n₂ (B x')) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) n₂ n)))))))) -> (Eq.{succ u1} (Filter.{u1} α) (nhds.{u1} α (TopologicalSpace.mkOfNhds.{u1} α (fun (x : α) => FilterBasis.filter.{u1} α (B x))) a) (FilterBasis.filter.{u1} α (B a)))
but is expected to have type
  forall {α : Type.{u1}} (B : α -> (FilterBasis.{u1} α)) (a : α), (forall (x : α) (n : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (FilterBasis.{u1} α) (instMembershipSetFilterBasis.{u1} α) n (B x)) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x n)) -> (forall (x : α) (n : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (FilterBasis.{u1} α) (instMembershipSetFilterBasis.{u1} α) n (B x)) -> (Exists.{succ u1} (Set.{u1} α) (fun (n₁ : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (FilterBasis.{u1} α) (instMembershipSetFilterBasis.{u1} α) n₁ (B x)) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) n₁ n) (forall (x' : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x' n₁) -> (Exists.{succ u1} (Set.{u1} α) (fun (n₂ : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (FilterBasis.{u1} α) (instMembershipSetFilterBasis.{u1} α) n₂ (B x')) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) n₂ n)))))))) -> (Eq.{succ u1} (Filter.{u1} α) (nhds.{u1} α (TopologicalSpace.mkOfNhds.{u1} α (fun (x : α) => FilterBasis.filter.{u1} α (B x))) a) (FilterBasis.filter.{u1} α (B a)))
Case conversion may be inaccurate. Consider using '#align topological_space.nhds_mk_of_nhds_filter_basis TopologicalSpace.nhds_mkOfNhds_filterBasisₓ'. -/
theorem nhds_mkOfNhds_filterBasis (B : α → FilterBasis α) (a : α) (h₀ : ∀ (x), ∀ n ∈ B x, x ∈ n)
    (h₁ : ∀ (x), ∀ n ∈ B x, ∃ n₁ ∈ B x, n₁ ⊆ n ∧ ∀ x' ∈ n₁, ∃ n₂ ∈ B x', n₂ ⊆ n) :
    @nhds α (TopologicalSpace.mkOfNhds fun x => (B x).filterₓ) a = (B a).filterₓ :=
  by
  rw [TopologicalSpace.nhds_mkOfNhds] <;> intro x n hn <;>
    obtain ⟨m, hm₁, hm₂⟩ := (B x).mem_filter_iff.mp hn
  · exact hm₂ (h₀ _ _ hm₁)
  · obtain ⟨n₁, hn₁, hn₂, hn₃⟩ := h₁ x m hm₁
    refine'
      ⟨n₁, (B x).mem_filter_of_mem hn₁, hn₂.trans hm₂, fun x' hx' => (B x').mem_filter_iff.mp _⟩
    obtain ⟨n₂, hn₄, hn₅⟩ := hn₃ x' hx'
    exact ⟨n₂, hn₄, hn₅.trans hm₂⟩
#align topological_space.nhds_mk_of_nhds_filter_basis TopologicalSpace.nhds_mkOfNhds_filterBasis

section Lattice

/-- The ordering on topologies on the type `α`. `t ≤ s` if every set open in `s` is also open in `t`
(`t` is finer than `s`). -/
instance : PartialOrder (TopologicalSpace α) :=
  { PartialOrder.lift (fun s => OrderDual.toDual is_open[s]) fun _ _ => topologicalSpace_eq with
    le := fun s t => ∀ U, is_open[t] U → is_open[s] U }

/- warning: topological_space.le_def -> TopologicalSpace.le_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {t : TopologicalSpace.{u1} α} {s : TopologicalSpace.{u1} α}, Iff (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toHasLe.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.partialOrder.{u1} α))) t s) (LE.le.{u1} ((Set.{u1} α) -> Prop) (Pi.hasLe.{u1, 0} (Set.{u1} α) (fun (s : Set.{u1} α) => Prop) (fun (i : Set.{u1} α) => Prop.le)) (IsOpen.{u1} α s) (IsOpen.{u1} α t))
but is expected to have type
  forall {α : Type.{u1}} {t : TopologicalSpace.{u1} α} {s : TopologicalSpace.{u1} α}, Iff (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toLE.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instPartialOrderTopologicalSpace.{u1} α))) t s) (LE.le.{u1} ((Set.{u1} α) -> Prop) (Pi.hasLe.{u1, 0} (Set.{u1} α) (fun (s : Set.{u1} α) => Prop) (fun (i : Set.{u1} α) => Prop.le)) (IsOpen.{u1} α s) (IsOpen.{u1} α t))
Case conversion may be inaccurate. Consider using '#align topological_space.le_def TopologicalSpace.le_defₓ'. -/
protected theorem le_def {α} {t s : TopologicalSpace α} : t ≤ s ↔ is_open[s] ≤ is_open[t] :=
  Iff.rfl
#align topological_space.le_def TopologicalSpace.le_def

/- warning: topological_space.le_generate_from_iff_subset_is_open -> TopologicalSpace.le_generateFrom_iff_subset_isOpen is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {g : Set.{u1} (Set.{u1} α)} {t : TopologicalSpace.{u1} α}, Iff (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toHasLe.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.partialOrder.{u1} α))) t (TopologicalSpace.generateFrom.{u1} α g)) (HasSubset.Subset.{u1} (Set.{u1} (Set.{u1} α)) (Set.hasSubset.{u1} (Set.{u1} α)) g (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => IsOpen.{u1} α t s)))
but is expected to have type
  forall {α : Type.{u1}} {g : Set.{u1} (Set.{u1} α)} {t : TopologicalSpace.{u1} α}, Iff (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toLE.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instPartialOrderTopologicalSpace.{u1} α))) t (TopologicalSpace.generateFrom.{u1} α g)) (HasSubset.Subset.{u1} (Set.{u1} (Set.{u1} α)) (Set.instHasSubsetSet.{u1} (Set.{u1} α)) g (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => IsOpen.{u1} α t s)))
Case conversion may be inaccurate. Consider using '#align topological_space.le_generate_from_iff_subset_is_open TopologicalSpace.le_generateFrom_iff_subset_isOpenₓ'. -/
theorem le_generateFrom_iff_subset_isOpen {g : Set (Set α)} {t : TopologicalSpace α} :
    t ≤ TopologicalSpace.generateFrom g ↔ g ⊆ { s | is_open[t] s } :=
  ⟨fun ht s hs => ht _ <| GenerateOpen.basic s hs, fun hg s hs =>
    hs.recOn (fun v hv => hg hv) t.isOpen_univ (fun u v _ _ => t.isOpen_inter u v) fun k _ =>
      t.isOpen_sUnion k⟩
#align topological_space.le_generate_from_iff_subset_is_open TopologicalSpace.le_generateFrom_iff_subset_isOpen

#print TopologicalSpace.mkOfClosure /-
/-- If `s` equals the collection of open sets in the topology it generates, then `s` defines a
topology. -/
protected def mkOfClosure (s : Set (Set α)) (hs : { u | GenerateOpen s u } = s) : TopologicalSpace α
    where
  IsOpen u := u ∈ s
  isOpen_univ := hs ▸ TopologicalSpace.GenerateOpen.univ
  isOpen_inter := hs ▸ TopologicalSpace.GenerateOpen.inter
  isOpen_sUnion := hs ▸ TopologicalSpace.GenerateOpen.sUnion
#align topological_space.mk_of_closure TopologicalSpace.mkOfClosure
-/

#print TopologicalSpace.mkOfClosure_sets /-
theorem mkOfClosure_sets {s : Set (Set α)} {hs : { u | GenerateOpen s u } = s} :
    TopologicalSpace.mkOfClosure s hs = TopologicalSpace.generateFrom s :=
  topologicalSpace_eq hs.symm
#align topological_space.mk_of_closure_sets TopologicalSpace.mkOfClosure_sets
-/

#print TopologicalSpace.gc_generateFrom /-
theorem gc_generateFrom (α) :
    GaloisConnection (fun t : TopologicalSpace α => OrderDual.toDual { s | is_open[t] s })
      (generateFrom ∘ OrderDual.ofDual) :=
  fun _ _ => le_generateFrom_iff_subset_isOpen.symm
#align topological_space.gc_generate_from TopologicalSpace.gc_generateFrom
-/

/- warning: topological_space.gci_generate_from clashes with gi_generate_from -> TopologicalSpace.gciGenerateFrom
warning: topological_space.gci_generate_from -> TopologicalSpace.gciGenerateFrom is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}), GaloisCoinsertion.{u1, u1} (TopologicalSpace.{u1} α) (OrderDual.{u1} (Set.{u1} (Set.{u1} α))) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.partialOrder.{u1} α)) (OrderDual.preorder.{u1} (Set.{u1} (Set.{u1} α)) (PartialOrder.toPreorder.{u1} (Set.{u1} (Set.{u1} α)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (Set.{u1} α)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (Set.{u1} α)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (Set.{u1} α)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (Set.{u1} α)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (Set.{u1} α)) (Set.completeBooleanAlgebra.{u1} (Set.{u1} α))))))))) (fun (t : TopologicalSpace.{u1} α) => coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Set.{u1} (Set.{u1} α)) (OrderDual.{u1} (Set.{u1} (Set.{u1} α)))) (fun (_x : Equiv.{succ u1, succ u1} (Set.{u1} (Set.{u1} α)) (OrderDual.{u1} (Set.{u1} (Set.{u1} α)))) => (Set.{u1} (Set.{u1} α)) -> (OrderDual.{u1} (Set.{u1} (Set.{u1} α)))) (Equiv.hasCoeToFun.{succ u1, succ u1} (Set.{u1} (Set.{u1} α)) (OrderDual.{u1} (Set.{u1} (Set.{u1} α)))) (OrderDual.toDual.{u1} (Set.{u1} (Set.{u1} α))) (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => IsOpen.{u1} α t s))) (Function.comp.{succ u1, succ u1, succ u1} (OrderDual.{u1} (Set.{u1} (Set.{u1} α))) (Set.{u1} (Set.{u1} α)) (TopologicalSpace.{u1} α) (TopologicalSpace.generateFrom.{u1} α) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} (Set.{u1} (Set.{u1} α))) (Set.{u1} (Set.{u1} α))) (fun (_x : Equiv.{succ u1, succ u1} (OrderDual.{u1} (Set.{u1} (Set.{u1} α))) (Set.{u1} (Set.{u1} α))) => (OrderDual.{u1} (Set.{u1} (Set.{u1} α))) -> (Set.{u1} (Set.{u1} α))) (Equiv.hasCoeToFun.{succ u1, succ u1} (OrderDual.{u1} (Set.{u1} (Set.{u1} α))) (Set.{u1} (Set.{u1} α))) (OrderDual.ofDual.{u1} (Set.{u1} (Set.{u1} α)))))
but is expected to have type
  forall (α : Type.{u1}), GaloisCoinsertion.{u1, u1} (TopologicalSpace.{u1} α) (OrderDual.{u1} (Set.{u1} (Set.{u1} α))) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instPartialOrderTopologicalSpace.{u1} α)) (OrderDual.preorder.{u1} (Set.{u1} (Set.{u1} α)) (PartialOrder.toPreorder.{u1} (Set.{u1} (Set.{u1} α)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (Set.{u1} α)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (Set.{u1} α)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (Set.{u1} α)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (Set.{u1} α)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (Set.{u1} α)) (Set.instCompleteBooleanAlgebraSet.{u1} (Set.{u1} α))))))))) (fun (t : TopologicalSpace.{u1} α) => FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Set.{u1} (Set.{u1} α)) (OrderDual.{u1} (Set.{u1} (Set.{u1} α)))) (Set.{u1} (Set.{u1} α)) (fun (_x : Set.{u1} (Set.{u1} α)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Set.{u1} (Set.{u1} α)) => OrderDual.{u1} (Set.{u1} (Set.{u1} α))) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (Set.{u1} (Set.{u1} α)) (OrderDual.{u1} (Set.{u1} (Set.{u1} α)))) (OrderDual.toDual.{u1} (Set.{u1} (Set.{u1} α))) (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => IsOpen.{u1} α t s))) (Function.comp.{succ u1, succ u1, succ u1} (OrderDual.{u1} (Set.{u1} (Set.{u1} α))) (Set.{u1} (Set.{u1} α)) (TopologicalSpace.{u1} α) (TopologicalSpace.generateFrom.{u1} α) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} (Set.{u1} (Set.{u1} α))) (Set.{u1} (Set.{u1} α))) (OrderDual.{u1} (Set.{u1} (Set.{u1} α))) (fun (_x : OrderDual.{u1} (Set.{u1} (Set.{u1} α))) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : OrderDual.{u1} (Set.{u1} (Set.{u1} α))) => Set.{u1} (Set.{u1} α)) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (OrderDual.{u1} (Set.{u1} (Set.{u1} α))) (Set.{u1} (Set.{u1} α))) (OrderDual.ofDual.{u1} (Set.{u1} (Set.{u1} α)))))
Case conversion may be inaccurate. Consider using '#align topological_space.gci_generate_from TopologicalSpace.gciGenerateFromₓ'. -/
/-- The Galois coinsertion between `topological_space α` and `(set (set α))ᵒᵈ` whose lower part
  sends a topology to its collection of open subsets, and whose upper part sends a collection of
  subsets of α to the topology they generate. -/
def gciGenerateFrom (α : Type _) :
    GaloisCoinsertion (fun t : TopologicalSpace α => OrderDual.toDual { s | is_open[t] s })
      (generateFrom ∘ OrderDual.ofDual)
    where
  gc := gc_generateFrom α
  u_l_le ts s hs := GenerateOpen.basic s hs
  choice g hg :=
    TopologicalSpace.mkOfClosure g
      (Subset.antisymm hg <| le_generateFrom_iff_subset_isOpen.1 <| le_rfl)
  choice_eq s hs := mkOfClosure_sets
#align topological_space.gci_generate_from TopologicalSpace.gciGenerateFrom

/-- Topologies on `α` form a complete lattice, with `⊥` the discrete topology
  and `⊤` the indiscrete topology. The infimum of a collection of topologies
  is the topology generated by all their open sets, while the supremum is the
  topology whose open sets are those sets open in every member of the collection. -/
instance : CompleteLattice (TopologicalSpace α) :=
  (gciGenerateFrom α).liftCompleteLattice

/- warning: topological_space.generate_from_anti -> TopologicalSpace.generateFrom_anti is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {g₁ : Set.{u1} (Set.{u1} α)} {g₂ : Set.{u1} (Set.{u1} α)}, (HasSubset.Subset.{u1} (Set.{u1} (Set.{u1} α)) (Set.hasSubset.{u1} (Set.{u1} α)) g₁ g₂) -> (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toHasLe.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.partialOrder.{u1} α))) (TopologicalSpace.generateFrom.{u1} α g₂) (TopologicalSpace.generateFrom.{u1} α g₁))
but is expected to have type
  forall {α : Type.{u1}} {g₁ : Set.{u1} (Set.{u1} α)} {g₂ : Set.{u1} (Set.{u1} α)}, (HasSubset.Subset.{u1} (Set.{u1} (Set.{u1} α)) (Set.instHasSubsetSet.{u1} (Set.{u1} α)) g₁ g₂) -> (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toLE.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instPartialOrderTopologicalSpace.{u1} α))) (TopologicalSpace.generateFrom.{u1} α g₂) (TopologicalSpace.generateFrom.{u1} α g₁))
Case conversion may be inaccurate. Consider using '#align topological_space.generate_from_anti TopologicalSpace.generateFrom_antiₓ'. -/
@[mono]
theorem generateFrom_anti {α} {g₁ g₂ : Set (Set α)} (h : g₁ ⊆ g₂) :
    generateFrom g₂ ≤ generateFrom g₁ :=
  (gc_generateFrom _).monotone_u h
#align topological_space.generate_from_anti TopologicalSpace.generateFrom_anti

#print TopologicalSpace.generateFrom_setOf_isOpen /-
theorem generateFrom_setOf_isOpen (t : TopologicalSpace α) :
    generateFrom { s | is_open[t] s } = t :=
  (gciGenerateFrom α).u_l_eq t
#align topological_space.generate_from_set_of_is_open TopologicalSpace.generateFrom_setOf_isOpen
-/

#print TopologicalSpace.leftInverse_generateFrom /-
theorem leftInverse_generateFrom :
    LeftInverse generateFrom fun t : TopologicalSpace α => { s | is_open[t] s } :=
  (gciGenerateFrom α).u_l_leftInverse
#align topological_space.left_inverse_generate_from TopologicalSpace.leftInverse_generateFrom
-/

#print TopologicalSpace.generateFrom_surjective /-
theorem generateFrom_surjective : Surjective (generateFrom : Set (Set α) → TopologicalSpace α) :=
  (gciGenerateFrom α).u_surjective
#align topological_space.generate_from_surjective TopologicalSpace.generateFrom_surjective
-/

#print TopologicalSpace.setOf_isOpen_injective /-
theorem setOf_isOpen_injective : Injective fun t : TopologicalSpace α => { s | is_open[t] s } :=
  (gciGenerateFrom α).l_injective
#align topological_space.set_of_is_open_injective TopologicalSpace.setOf_isOpen_injective
-/

end Lattice

end TopologicalSpace

section Lattice

variable {α : Type u} {β : Type v}

/- warning: is_open.mono -> IsOpen.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {t₁ : TopologicalSpace.{u1} α} {t₂ : TopologicalSpace.{u1} α} {s : Set.{u1} α}, (IsOpen.{u1} α t₂ s) -> (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toHasLe.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.partialOrder.{u1} α))) t₁ t₂) -> (IsOpen.{u1} α t₁ s)
but is expected to have type
  forall {α : Type.{u1}} {t₁ : TopologicalSpace.{u1} α} {t₂ : TopologicalSpace.{u1} α} {s : Set.{u1} α}, (IsOpen.{u1} α t₂ s) -> (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toLE.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instPartialOrderTopologicalSpace.{u1} α))) t₁ t₂) -> (IsOpen.{u1} α t₁ s)
Case conversion may be inaccurate. Consider using '#align is_open.mono IsOpen.monoₓ'. -/
theorem IsOpen.mono {α} {t₁ t₂ : TopologicalSpace α} {s : Set α} (hs : is_open[t₂] s)
    (h : t₁ ≤ t₂) : is_open[t₁] s :=
  h s hs
#align is_open.mono IsOpen.mono

/- warning: is_closed.mono -> IsClosed.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {t₁ : TopologicalSpace.{u1} α} {t₂ : TopologicalSpace.{u1} α} {s : Set.{u1} α}, (IsClosed.{u1} α t₂ s) -> (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toHasLe.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.partialOrder.{u1} α))) t₁ t₂) -> (IsClosed.{u1} α t₁ s)
but is expected to have type
  forall {α : Type.{u1}} {t₁ : TopologicalSpace.{u1} α} {t₂ : TopologicalSpace.{u1} α} {s : Set.{u1} α}, (IsClosed.{u1} α t₂ s) -> (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toLE.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instPartialOrderTopologicalSpace.{u1} α))) t₁ t₂) -> (IsClosed.{u1} α t₁ s)
Case conversion may be inaccurate. Consider using '#align is_closed.mono IsClosed.monoₓ'. -/
theorem IsClosed.mono {α} {t₁ t₂ : TopologicalSpace α} {s : Set α} (hs : is_closed[t₂] s)
    (h : t₁ ≤ t₂) : is_closed[t₁] s :=
  (@isOpen_compl_iff α t₁ s).mp <| hs.isOpen_compl.mono h
#align is_closed.mono IsClosed.mono

/- warning: is_open_implies_is_open_iff -> isOpen_implies_isOpen_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : TopologicalSpace.{u1} α} {b : TopologicalSpace.{u1} α}, Iff (forall (s : Set.{u1} α), (IsOpen.{u1} α a s) -> (IsOpen.{u1} α b s)) (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toHasLe.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.partialOrder.{u1} α))) b a)
but is expected to have type
  forall {α : Type.{u1}} {a : TopologicalSpace.{u1} α} {b : TopologicalSpace.{u1} α}, Iff (forall (s : Set.{u1} α), (IsOpen.{u1} α a s) -> (IsOpen.{u1} α b s)) (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toLE.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instPartialOrderTopologicalSpace.{u1} α))) b a)
Case conversion may be inaccurate. Consider using '#align is_open_implies_is_open_iff isOpen_implies_isOpen_iffₓ'. -/
theorem isOpen_implies_isOpen_iff {a b : TopologicalSpace α} :
    (∀ s, is_open[a] s → is_open[b] s) ↔ b ≤ a :=
  Iff.rfl
#align is_open_implies_is_open_iff isOpen_implies_isOpen_iff

/- warning: topological_space.is_open_top_iff -> TopologicalSpace.isOpen_top_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (U : Set.{u1} α), Iff (IsOpen.{u1} α (Top.top.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toHasTop.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))) U) (Or (Eq.{succ u1} (Set.{u1} α) U (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Eq.{succ u1} (Set.{u1} α) U (Set.univ.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} (U : Set.{u1} α), Iff (IsOpen.{u1} α (Top.top.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toTop.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α))) U) (Or (Eq.{succ u1} (Set.{u1} α) U (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (Eq.{succ u1} (Set.{u1} α) U (Set.univ.{u1} α)))
Case conversion may be inaccurate. Consider using '#align topological_space.is_open_top_iff TopologicalSpace.isOpen_top_iffₓ'. -/
/-- The only open sets in the indiscrete topology are the empty set and the whole space. -/
theorem TopologicalSpace.isOpen_top_iff {α} (U : Set α) : is_open[⊤] U ↔ U = ∅ ∨ U = univ :=
  ⟨fun h => by
    induction' h with V h _ _ _ _ ih₁ ih₂ _ _ ih
    · cases h; · exact Or.inr rfl
    · obtain ⟨rfl | rfl, rfl | rfl⟩ := ih₁, ih₂ <;> simp
    · rw [sUnion_eq_empty, or_iff_not_imp_left]
      intro h; push_neg  at h; obtain ⟨U, hU, hne⟩ := h
      have := (ih U hU).resolve_left hne; subst this
      refine' sUnion_eq_univ_iff.2 fun a => ⟨_, hU, trivial⟩, by rintro (rfl | rfl);
    exacts[@isOpen_empty _ ⊤, @isOpen_univ _ ⊤]⟩
#align topological_space.is_open_top_iff TopologicalSpace.isOpen_top_iff

#print DiscreteTopology /-
/- ./././Mathport/Syntax/Translate/Command.lean:393:30: infer kinds are unsupported in Lean 4: #[`eq_bot] [] -/
/-- A topological space is discrete if every set is open, that is,
  its topology equals the discrete topology `⊥`. -/
class DiscreteTopology (α : Type _) [t : TopologicalSpace α] : Prop where
  eq_bot : t = ⊥
#align discrete_topology DiscreteTopology
-/

/- warning: discrete_topology_bot -> discreteTopology_bot is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}), DiscreteTopology.{u1} α (Bot.bot.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toHasBot.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α)))
but is expected to have type
  forall (α : Type.{u1}), DiscreteTopology.{u1} α (Bot.bot.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toBot.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α)))
Case conversion may be inaccurate. Consider using '#align discrete_topology_bot discreteTopology_botₓ'. -/
theorem discreteTopology_bot (α : Type _) : @DiscreteTopology α ⊥ :=
  @DiscreteTopology.mk α ⊥ rfl
#align discrete_topology_bot discreteTopology_bot

#print isOpen_discrete /-
@[simp]
theorem isOpen_discrete [TopologicalSpace α] [DiscreteTopology α] (s : Set α) : IsOpen s :=
  (DiscreteTopology.eq_bot α).symm ▸ trivial
#align is_open_discrete isOpen_discrete
-/

#print isClosed_discrete /-
@[simp]
theorem isClosed_discrete [TopologicalSpace α] [DiscreteTopology α] (s : Set α) : IsClosed s :=
  isOpen_compl_iff.1 <| isOpen_discrete _
#align is_closed_discrete isClosed_discrete
-/

#print continuous_of_discreteTopology /-
@[nontriviality]
theorem continuous_of_discreteTopology [TopologicalSpace α] [DiscreteTopology α]
    [TopologicalSpace β] {f : α → β} : Continuous f :=
  continuous_def.2 fun s hs => isOpen_discrete _
#align continuous_of_discrete_topology continuous_of_discreteTopology
-/

#print nhds_discrete /-
@[simp]
theorem nhds_discrete (α : Type _) [TopologicalSpace α] [DiscreteTopology α] : @nhds α _ = pure :=
  le_antisymm (fun _ s hs => (isOpen_discrete s).mem_nhds hs) pure_le_nhds
#align nhds_discrete nhds_discrete
-/

#print mem_nhds_discrete /-
theorem mem_nhds_discrete [TopologicalSpace α] [DiscreteTopology α] {x : α} {s : Set α} :
    s ∈ 𝓝 x ↔ x ∈ s := by rw [nhds_discrete, mem_pure]
#align mem_nhds_discrete mem_nhds_discrete
-/

/- warning: le_of_nhds_le_nhds -> le_of_nhds_le_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {t₁ : TopologicalSpace.{u1} α} {t₂ : TopologicalSpace.{u1} α}, (forall (x : α), LE.le.{u1} (Filter.{u1} α) (Preorder.toHasLe.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (nhds.{u1} α t₁ x) (nhds.{u1} α t₂ x)) -> (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toHasLe.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.partialOrder.{u1} α))) t₁ t₂)
but is expected to have type
  forall {α : Type.{u1}} {t₁ : TopologicalSpace.{u1} α} {t₂ : TopologicalSpace.{u1} α}, (forall (x : α), LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (nhds.{u1} α t₁ x) (nhds.{u1} α t₂ x)) -> (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toLE.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instPartialOrderTopologicalSpace.{u1} α))) t₁ t₂)
Case conversion may be inaccurate. Consider using '#align le_of_nhds_le_nhds le_of_nhds_le_nhdsₓ'. -/
theorem le_of_nhds_le_nhds {t₁ t₂ : TopologicalSpace α} (h : ∀ x, @nhds α t₁ x ≤ @nhds α t₂ x) :
    t₁ ≤ t₂ := by
  intro s
  rw [@isOpen_iff_mem_nhds _ t₁, @isOpen_iff_mem_nhds α t₂]
  exact fun hs a ha => h _ (hs _ ha)
#align le_of_nhds_le_nhds le_of_nhds_le_nhds

#print eq_of_nhds_eq_nhds /-
theorem eq_of_nhds_eq_nhds {t₁ t₂ : TopologicalSpace α} (h : ∀ x, @nhds α t₁ x = @nhds α t₂ x) :
    t₁ = t₂ :=
  le_antisymm (le_of_nhds_le_nhds fun x => le_of_eq <| h x)
    (le_of_nhds_le_nhds fun x => le_of_eq <| (h x).symm)
#align eq_of_nhds_eq_nhds eq_of_nhds_eq_nhds
-/

/- warning: eq_bot_of_singletons_open -> eq_bot_of_singletons_open is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {t : TopologicalSpace.{u1} α}, (forall (x : α), IsOpen.{u1} α t (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x)) -> (Eq.{succ u1} (TopologicalSpace.{u1} α) t (Bot.bot.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toHasBot.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))))
but is expected to have type
  forall {α : Type.{u1}} {t : TopologicalSpace.{u1} α}, (forall (x : α), IsOpen.{u1} α t (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x)) -> (Eq.{succ u1} (TopologicalSpace.{u1} α) t (Bot.bot.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toBot.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α))))
Case conversion may be inaccurate. Consider using '#align eq_bot_of_singletons_open eq_bot_of_singletons_openₓ'. -/
theorem eq_bot_of_singletons_open {t : TopologicalSpace α} (h : ∀ x, is_open[t] {x}) : t = ⊥ :=
  bot_unique fun s hs => biUnion_of_singleton s ▸ isOpen_biUnion fun x _ => h x
#align eq_bot_of_singletons_open eq_bot_of_singletons_open

#print forall_open_iff_discrete /-
theorem forall_open_iff_discrete {X : Type _} [TopologicalSpace X] :
    (∀ s : Set X, IsOpen s) ↔ DiscreteTopology X :=
  ⟨fun h => ⟨eq_bot_of_singletons_open fun _ => h _⟩, @isOpen_discrete _ _⟩
#align forall_open_iff_discrete forall_open_iff_discrete
-/

#print singletons_open_iff_discrete /-
theorem singletons_open_iff_discrete {X : Type _} [TopologicalSpace X] :
    (∀ a : X, IsOpen ({a} : Set X)) ↔ DiscreteTopology X :=
  ⟨fun h => ⟨eq_bot_of_singletons_open h⟩, fun a _ => @isOpen_discrete _ _ a _⟩
#align singletons_open_iff_discrete singletons_open_iff_discrete
-/

#print discreteTopology_iff_singleton_mem_nhds /-
theorem discreteTopology_iff_singleton_mem_nhds [TopologicalSpace α] :
    DiscreteTopology α ↔ ∀ x : α, {x} ∈ 𝓝 x := by
  simp only [← singletons_open_iff_discrete, isOpen_iff_mem_nhds, mem_singleton_iff, forall_eq]
#align discrete_topology_iff_singleton_mem_nhds discreteTopology_iff_singleton_mem_nhds
-/

#print discreteTopology_iff_nhds /-
/-- This lemma characterizes discrete topological spaces as those whose singletons are
neighbourhoods. -/
theorem discreteTopology_iff_nhds [TopologicalSpace α] :
    DiscreteTopology α ↔ ∀ x : α, 𝓝 x = pure x := by
  simp only [discreteTopology_iff_singleton_mem_nhds, ← nhds_ne_bot.le_pure_iff, le_pure_iff]
#align discrete_topology_iff_nhds discreteTopology_iff_nhds
-/

/- warning: discrete_topology_iff_nhds_ne -> discreteTopology_iff_nhds_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α], Iff (DiscreteTopology.{u1} α _inst_1) (forall (x : α), Eq.{succ u1} (Filter.{u1} α) (nhdsWithin.{u1} α _inst_1 x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x))) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α], Iff (DiscreteTopology.{u1} α _inst_1) (forall (x : α), Eq.{succ u1} (Filter.{u1} α) (nhdsWithin.{u1} α _inst_1 x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x))) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))))
Case conversion may be inaccurate. Consider using '#align discrete_topology_iff_nhds_ne discreteTopology_iff_nhds_neₓ'. -/
theorem discreteTopology_iff_nhds_ne [TopologicalSpace α] :
    DiscreteTopology α ↔ ∀ x : α, 𝓝[≠] x = ⊥ := by
  simp only [discreteTopology_iff_singleton_mem_nhds, nhdsWithin, inf_principal_eq_bot, compl_compl]
#align discrete_topology_iff_nhds_ne discreteTopology_iff_nhds_ne

end Lattice

section GaloisConnection

variable {α : Type _} {β : Type _} {γ : Type _}

#print TopologicalSpace.induced /-
/-- Given `f : α → β` and a topology on `β`, the induced topology on `α` is the collection of
  sets that are preimages of some open set in `β`. This is the coarsest topology that
  makes `f` continuous. -/
def TopologicalSpace.induced {α : Type u} {β : Type v} (f : α → β) (t : TopologicalSpace β) :
    TopologicalSpace α where
  IsOpen s := ∃ s', IsOpen s' ∧ f ⁻¹' s' = s
  isOpen_univ := ⟨univ, isOpen_univ, preimage_univ⟩
  isOpen_inter := by
    rintro s₁ s₂ ⟨s'₁, hs₁, rfl⟩ ⟨s'₂, hs₂, rfl⟩ <;>
      exact ⟨s'₁ ∩ s'₂, hs₁.inter hs₂, preimage_inter⟩
  isOpen_sUnion s h := by
    simp only [Classical.skolem] at h
    cases' h with f hf
    apply Exists.intro (⋃ (x : Set α) (h : x ∈ s), f x h)
    simp only [sUnion_eq_bUnion, preimage_Union, fun x h => (hf x h).right]; refine' ⟨_, rfl⟩
    exact
      @isOpen_iUnion β _ t _ fun i =>
        show IsOpen (⋃ h, f i h) from @isOpen_iUnion β _ t _ fun h => (hf i h).left
#align topological_space.induced TopologicalSpace.induced
-/

#print isOpen_induced_iff /-
theorem isOpen_induced_iff [t : TopologicalSpace β] {s : Set α} {f : α → β} :
    is_open[t.induced f] s ↔ ∃ t, IsOpen t ∧ f ⁻¹' t = s :=
  Iff.rfl
#align is_open_induced_iff isOpen_induced_iff
-/

#print isClosed_induced_iff /-
theorem isClosed_induced_iff [t : TopologicalSpace β] {s : Set α} {f : α → β} :
    is_closed[t.induced f] s ↔ ∃ t, IsClosed t ∧ f ⁻¹' t = s :=
  by
  simp only [← isOpen_compl_iff, isOpen_induced_iff]
  exact compl_surjective.exists.trans (by simp only [preimage_compl, compl_inj_iff])
#align is_closed_induced_iff isClosed_induced_iff
-/

#print TopologicalSpace.coinduced /-
/-- Given `f : α → β` and a topology on `α`, the coinduced topology on `β` is defined
  such that `s:set β` is open if the preimage of `s` is open. This is the finest topology that
  makes `f` continuous. -/
def TopologicalSpace.coinduced {α : Type u} {β : Type v} (f : α → β) (t : TopologicalSpace α) :
    TopologicalSpace β where
  IsOpen s := is_open[t] (f ⁻¹' s)
  isOpen_univ := t.isOpen_univ
  isOpen_inter _ _ h₁ h₂ := h₁.inter h₂
  isOpen_sUnion s h := by simpa only [preimage_sUnion] using isOpen_biUnion h
#align topological_space.coinduced TopologicalSpace.coinduced
-/

/- warning: is_open_coinduced -> isOpen_coinduced is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {t : TopologicalSpace.{u1} α} {s : Set.{u2} β} {f : α -> β}, Iff (IsOpen.{u2} β (TopologicalSpace.coinduced.{u1, u2} α β f t) s) (IsOpen.{u1} α t (Set.preimage.{u1, u2} α β f s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {t : TopologicalSpace.{u2} α} {s : Set.{u1} β} {f : α -> β}, Iff (IsOpen.{u1} β (TopologicalSpace.coinduced.{u2, u1} α β f t) s) (IsOpen.{u2} α t (Set.preimage.{u2, u1} α β f s))
Case conversion may be inaccurate. Consider using '#align is_open_coinduced isOpen_coinducedₓ'. -/
theorem isOpen_coinduced {t : TopologicalSpace α} {s : Set β} {f : α → β} :
    is_open[t.coinduced f] s ↔ IsOpen (f ⁻¹' s) :=
  Iff.rfl
#align is_open_coinduced isOpen_coinduced

/- warning: preimage_nhds_coinduced -> preimage_nhds_coinduced is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] {π : α -> β} {s : Set.{u2} β} {a : α}, (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) s (nhds.{u2} β (TopologicalSpace.coinduced.{u1, u2} α β π _inst_1) (π a))) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (Set.preimage.{u1, u2} α β π s) (nhds.{u1} α _inst_1 a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] {π : α -> β} {s : Set.{u1} β} {a : α}, (Membership.mem.{u1, u1} (Set.{u1} β) (Filter.{u1} β) (instMembershipSetFilter.{u1} β) s (nhds.{u1} β (TopologicalSpace.coinduced.{u2, u1} α β π _inst_1) (π a))) -> (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) (Set.preimage.{u2, u1} α β π s) (nhds.{u2} α _inst_1 a))
Case conversion may be inaccurate. Consider using '#align preimage_nhds_coinduced preimage_nhds_coinducedₓ'. -/
theorem preimage_nhds_coinduced [TopologicalSpace α] {π : α → β} {s : Set β} {a : α}
    (hs : s ∈ @nhds β (TopologicalSpace.coinduced π ‹_›) (π a)) : π ⁻¹' s ∈ 𝓝 a :=
  by
  letI := TopologicalSpace.coinduced π ‹_›
  rcases mem_nhds_iff.mp hs with ⟨V, hVs, V_op, mem_V⟩
  exact mem_nhds_iff.mpr ⟨π ⁻¹' V, Set.preimage_mono hVs, V_op, mem_V⟩
#align preimage_nhds_coinduced preimage_nhds_coinduced

variable {t t₁ t₂ : TopologicalSpace α} {t' : TopologicalSpace β} {f : α → β} {g : β → α}

/- warning: continuous.coinduced_le -> Continuous.coinduced_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {t : TopologicalSpace.{u1} α} {t' : TopologicalSpace.{u2} β} {f : α -> β}, (Continuous.{u1, u2} α β t t' f) -> (LE.le.{u2} (TopologicalSpace.{u2} β) (Preorder.toHasLe.{u2} (TopologicalSpace.{u2} β) (PartialOrder.toPreorder.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.partialOrder.{u2} β))) (TopologicalSpace.coinduced.{u1, u2} α β f t) t')
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {t : TopologicalSpace.{u2} α} {t' : TopologicalSpace.{u1} β} {f : α -> β}, (Continuous.{u2, u1} α β t t' f) -> (LE.le.{u1} (TopologicalSpace.{u1} β) (Preorder.toLE.{u1} (TopologicalSpace.{u1} β) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} β) (TopologicalSpace.instPartialOrderTopologicalSpace.{u1} β))) (TopologicalSpace.coinduced.{u2, u1} α β f t) t')
Case conversion may be inaccurate. Consider using '#align continuous.coinduced_le Continuous.coinduced_leₓ'. -/
theorem Continuous.coinduced_le (h : @Continuous α β t t' f) : t.coinduced f ≤ t' := fun s hs =>
  (continuous_def.1 h s hs : _)
#align continuous.coinduced_le Continuous.coinduced_le

/- warning: coinduced_le_iff_le_induced -> coinduced_le_iff_le_induced is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {tα : TopologicalSpace.{u1} α} {tβ : TopologicalSpace.{u2} β}, Iff (LE.le.{u2} (TopologicalSpace.{u2} β) (Preorder.toHasLe.{u2} (TopologicalSpace.{u2} β) (PartialOrder.toPreorder.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.partialOrder.{u2} β))) (TopologicalSpace.coinduced.{u1, u2} α β f tα) tβ) (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toHasLe.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.partialOrder.{u1} α))) tα (TopologicalSpace.induced.{u1, u2} α β f tβ))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {tα : TopologicalSpace.{u2} α} {tβ : TopologicalSpace.{u1} β}, Iff (LE.le.{u1} (TopologicalSpace.{u1} β) (Preorder.toLE.{u1} (TopologicalSpace.{u1} β) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} β) (TopologicalSpace.instPartialOrderTopologicalSpace.{u1} β))) (TopologicalSpace.coinduced.{u2, u1} α β f tα) tβ) (LE.le.{u2} (TopologicalSpace.{u2} α) (Preorder.toLE.{u2} (TopologicalSpace.{u2} α) (PartialOrder.toPreorder.{u2} (TopologicalSpace.{u2} α) (TopologicalSpace.instPartialOrderTopologicalSpace.{u2} α))) tα (TopologicalSpace.induced.{u2, u1} α β f tβ))
Case conversion may be inaccurate. Consider using '#align coinduced_le_iff_le_induced coinduced_le_iff_le_inducedₓ'. -/
theorem coinduced_le_iff_le_induced {f : α → β} {tα : TopologicalSpace α}
    {tβ : TopologicalSpace β} : tα.coinduced f ≤ tβ ↔ tα ≤ tβ.induced f :=
  ⟨fun h s ⟨t, ht, hst⟩ => hst ▸ h _ ht, fun h s hs => h _ ⟨s, hs, rfl⟩⟩
#align coinduced_le_iff_le_induced coinduced_le_iff_le_induced

/- warning: continuous.le_induced -> Continuous.le_induced is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {t : TopologicalSpace.{u1} α} {t' : TopologicalSpace.{u2} β} {f : α -> β}, (Continuous.{u1, u2} α β t t' f) -> (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toHasLe.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.partialOrder.{u1} α))) t (TopologicalSpace.induced.{u1, u2} α β f t'))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {t : TopologicalSpace.{u2} α} {t' : TopologicalSpace.{u1} β} {f : α -> β}, (Continuous.{u2, u1} α β t t' f) -> (LE.le.{u2} (TopologicalSpace.{u2} α) (Preorder.toLE.{u2} (TopologicalSpace.{u2} α) (PartialOrder.toPreorder.{u2} (TopologicalSpace.{u2} α) (TopologicalSpace.instPartialOrderTopologicalSpace.{u2} α))) t (TopologicalSpace.induced.{u2, u1} α β f t'))
Case conversion may be inaccurate. Consider using '#align continuous.le_induced Continuous.le_inducedₓ'. -/
theorem Continuous.le_induced (h : @Continuous α β t t' f) : t ≤ t'.induced f :=
  coinduced_le_iff_le_induced.1 h.coinduced_le
#align continuous.le_induced Continuous.le_induced

/- warning: gc_coinduced_induced -> gc_coinduced_induced is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β), GaloisConnection.{u1, u2} (TopologicalSpace.{u1} α) (TopologicalSpace.{u2} β) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.partialOrder.{u1} α)) (PartialOrder.toPreorder.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.partialOrder.{u2} β)) (TopologicalSpace.coinduced.{u1, u2} α β f) (TopologicalSpace.induced.{u1, u2} α β f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β), GaloisConnection.{u2, u1} (TopologicalSpace.{u2} α) (TopologicalSpace.{u1} β) (PartialOrder.toPreorder.{u2} (TopologicalSpace.{u2} α) (TopologicalSpace.instPartialOrderTopologicalSpace.{u2} α)) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} β) (TopologicalSpace.instPartialOrderTopologicalSpace.{u1} β)) (TopologicalSpace.coinduced.{u2, u1} α β f) (TopologicalSpace.induced.{u2, u1} α β f)
Case conversion may be inaccurate. Consider using '#align gc_coinduced_induced gc_coinduced_inducedₓ'. -/
theorem gc_coinduced_induced (f : α → β) :
    GaloisConnection (TopologicalSpace.coinduced f) (TopologicalSpace.induced f) := fun f g =>
  coinduced_le_iff_le_induced
#align gc_coinduced_induced gc_coinduced_induced

/- warning: induced_mono -> induced_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {t₁ : TopologicalSpace.{u1} α} {t₂ : TopologicalSpace.{u1} α} {g : β -> α}, (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toHasLe.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.partialOrder.{u1} α))) t₁ t₂) -> (LE.le.{u2} (TopologicalSpace.{u2} β) (Preorder.toHasLe.{u2} (TopologicalSpace.{u2} β) (PartialOrder.toPreorder.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.partialOrder.{u2} β))) (TopologicalSpace.induced.{u2, u1} β α g t₁) (TopologicalSpace.induced.{u2, u1} β α g t₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {t₁ : TopologicalSpace.{u2} α} {t₂ : TopologicalSpace.{u2} α} {g : β -> α}, (LE.le.{u2} (TopologicalSpace.{u2} α) (Preorder.toLE.{u2} (TopologicalSpace.{u2} α) (PartialOrder.toPreorder.{u2} (TopologicalSpace.{u2} α) (TopologicalSpace.instPartialOrderTopologicalSpace.{u2} α))) t₁ t₂) -> (LE.le.{u1} (TopologicalSpace.{u1} β) (Preorder.toLE.{u1} (TopologicalSpace.{u1} β) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} β) (TopologicalSpace.instPartialOrderTopologicalSpace.{u1} β))) (TopologicalSpace.induced.{u1, u2} β α g t₁) (TopologicalSpace.induced.{u1, u2} β α g t₂))
Case conversion may be inaccurate. Consider using '#align induced_mono induced_monoₓ'. -/
theorem induced_mono (h : t₁ ≤ t₂) : t₁.induced g ≤ t₂.induced g :=
  (gc_coinduced_induced g).monotone_u h
#align induced_mono induced_mono

/- warning: coinduced_mono -> coinduced_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {t₁ : TopologicalSpace.{u1} α} {t₂ : TopologicalSpace.{u1} α} {f : α -> β}, (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toHasLe.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.partialOrder.{u1} α))) t₁ t₂) -> (LE.le.{u2} (TopologicalSpace.{u2} β) (Preorder.toHasLe.{u2} (TopologicalSpace.{u2} β) (PartialOrder.toPreorder.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.partialOrder.{u2} β))) (TopologicalSpace.coinduced.{u1, u2} α β f t₁) (TopologicalSpace.coinduced.{u1, u2} α β f t₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {t₁ : TopologicalSpace.{u2} α} {t₂ : TopologicalSpace.{u2} α} {f : α -> β}, (LE.le.{u2} (TopologicalSpace.{u2} α) (Preorder.toLE.{u2} (TopologicalSpace.{u2} α) (PartialOrder.toPreorder.{u2} (TopologicalSpace.{u2} α) (TopologicalSpace.instPartialOrderTopologicalSpace.{u2} α))) t₁ t₂) -> (LE.le.{u1} (TopologicalSpace.{u1} β) (Preorder.toLE.{u1} (TopologicalSpace.{u1} β) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} β) (TopologicalSpace.instPartialOrderTopologicalSpace.{u1} β))) (TopologicalSpace.coinduced.{u2, u1} α β f t₁) (TopologicalSpace.coinduced.{u2, u1} α β f t₂))
Case conversion may be inaccurate. Consider using '#align coinduced_mono coinduced_monoₓ'. -/
theorem coinduced_mono (h : t₁ ≤ t₂) : t₁.coinduced f ≤ t₂.coinduced f :=
  (gc_coinduced_induced f).monotone_l h
#align coinduced_mono coinduced_mono

/- warning: induced_top -> induced_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {g : β -> α}, Eq.{succ u2} (TopologicalSpace.{u2} β) (TopologicalSpace.induced.{u2, u1} β α g (Top.top.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toHasTop.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α)))) (Top.top.{u2} (TopologicalSpace.{u2} β) (CompleteLattice.toHasTop.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.completeLattice.{u2} β)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {g : β -> α}, Eq.{succ u2} (TopologicalSpace.{u2} β) (TopologicalSpace.induced.{u2, u1} β α g (Top.top.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toTop.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α)))) (Top.top.{u2} (TopologicalSpace.{u2} β) (CompleteLattice.toTop.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u2} β)))
Case conversion may be inaccurate. Consider using '#align induced_top induced_topₓ'. -/
@[simp]
theorem induced_top : (⊤ : TopologicalSpace α).induced g = ⊤ :=
  (gc_coinduced_induced g).u_top
#align induced_top induced_top

/- warning: induced_inf -> induced_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {t₁ : TopologicalSpace.{u1} α} {t₂ : TopologicalSpace.{u1} α} {g : β -> α}, Eq.{succ u2} (TopologicalSpace.{u2} β) (TopologicalSpace.induced.{u2, u1} β α g (Inf.inf.{u1} (TopologicalSpace.{u1} α) (SemilatticeInf.toHasInf.{u1} (TopologicalSpace.{u1} α) (Lattice.toSemilatticeInf.{u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))))) t₁ t₂)) (Inf.inf.{u2} (TopologicalSpace.{u2} β) (SemilatticeInf.toHasInf.{u2} (TopologicalSpace.{u2} β) (Lattice.toSemilatticeInf.{u2} (TopologicalSpace.{u2} β) (ConditionallyCompleteLattice.toLattice.{u2} (TopologicalSpace.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.completeLattice.{u2} β))))) (TopologicalSpace.induced.{u2, u1} β α g t₁) (TopologicalSpace.induced.{u2, u1} β α g t₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {t₁ : TopologicalSpace.{u1} α} {t₂ : TopologicalSpace.{u1} α} {g : β -> α}, Eq.{succ u2} (TopologicalSpace.{u2} β) (TopologicalSpace.induced.{u2, u1} β α g (Inf.inf.{u1} (TopologicalSpace.{u1} α) (Lattice.toInf.{u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α)))) t₁ t₂)) (Inf.inf.{u2} (TopologicalSpace.{u2} β) (Lattice.toInf.{u2} (TopologicalSpace.{u2} β) (ConditionallyCompleteLattice.toLattice.{u2} (TopologicalSpace.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u2} β)))) (TopologicalSpace.induced.{u2, u1} β α g t₁) (TopologicalSpace.induced.{u2, u1} β α g t₂))
Case conversion may be inaccurate. Consider using '#align induced_inf induced_infₓ'. -/
@[simp]
theorem induced_inf : (t₁ ⊓ t₂).induced g = t₁.induced g ⊓ t₂.induced g :=
  (gc_coinduced_induced g).u_inf
#align induced_inf induced_inf

/- warning: induced_infi -> induced_iInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u2}} {β : Type.{u3}} {g : β -> α} {ι : Sort.{u1}} {t : ι -> (TopologicalSpace.{u2} α)}, Eq.{succ u3} (TopologicalSpace.{u3} β) (TopologicalSpace.induced.{u3, u2} β α g (iInf.{u2, u1} (TopologicalSpace.{u2} α) (ConditionallyCompleteLattice.toHasInf.{u2} (TopologicalSpace.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} α) (TopologicalSpace.completeLattice.{u2} α))) ι (fun (i : ι) => t i))) (iInf.{u3, u1} (TopologicalSpace.{u3} β) (ConditionallyCompleteLattice.toHasInf.{u3} (TopologicalSpace.{u3} β) (CompleteLattice.toConditionallyCompleteLattice.{u3} (TopologicalSpace.{u3} β) (TopologicalSpace.completeLattice.{u3} β))) ι (fun (i : ι) => TopologicalSpace.induced.{u3, u2} β α g (t i)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {g : β -> α} {ι : Sort.{u3}} {t : ι -> (TopologicalSpace.{u2} α)}, Eq.{succ u1} (TopologicalSpace.{u1} β) (TopologicalSpace.induced.{u1, u2} β α g (iInf.{u2, u3} (TopologicalSpace.{u2} α) (ConditionallyCompleteLattice.toInfSet.{u2} (TopologicalSpace.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u2} α))) ι (fun (i : ι) => t i))) (iInf.{u1, u3} (TopologicalSpace.{u1} β) (ConditionallyCompleteLattice.toInfSet.{u1} (TopologicalSpace.{u1} β) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} β) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} β))) ι (fun (i : ι) => TopologicalSpace.induced.{u1, u2} β α g (t i)))
Case conversion may be inaccurate. Consider using '#align induced_infi induced_iInfₓ'. -/
@[simp]
theorem induced_iInf {ι : Sort w} {t : ι → TopologicalSpace α} :
    (⨅ i, t i).induced g = ⨅ i, (t i).induced g :=
  (gc_coinduced_induced g).u_iInf
#align induced_infi induced_iInf

/- warning: coinduced_bot -> coinduced_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, Eq.{succ u2} (TopologicalSpace.{u2} β) (TopologicalSpace.coinduced.{u1, u2} α β f (Bot.bot.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toHasBot.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α)))) (Bot.bot.{u2} (TopologicalSpace.{u2} β) (CompleteLattice.toHasBot.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.completeLattice.{u2} β)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, Eq.{succ u2} (TopologicalSpace.{u2} β) (TopologicalSpace.coinduced.{u1, u2} α β f (Bot.bot.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toBot.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α)))) (Bot.bot.{u2} (TopologicalSpace.{u2} β) (CompleteLattice.toBot.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u2} β)))
Case conversion may be inaccurate. Consider using '#align coinduced_bot coinduced_botₓ'. -/
@[simp]
theorem coinduced_bot : (⊥ : TopologicalSpace α).coinduced f = ⊥ :=
  (gc_coinduced_induced f).l_bot
#align coinduced_bot coinduced_bot

/- warning: coinduced_sup -> coinduced_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {t₁ : TopologicalSpace.{u1} α} {t₂ : TopologicalSpace.{u1} α} {f : α -> β}, Eq.{succ u2} (TopologicalSpace.{u2} β) (TopologicalSpace.coinduced.{u1, u2} α β f (Sup.sup.{u1} (TopologicalSpace.{u1} α) (SemilatticeSup.toHasSup.{u1} (TopologicalSpace.{u1} α) (Lattice.toSemilatticeSup.{u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))))) t₁ t₂)) (Sup.sup.{u2} (TopologicalSpace.{u2} β) (SemilatticeSup.toHasSup.{u2} (TopologicalSpace.{u2} β) (Lattice.toSemilatticeSup.{u2} (TopologicalSpace.{u2} β) (ConditionallyCompleteLattice.toLattice.{u2} (TopologicalSpace.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.completeLattice.{u2} β))))) (TopologicalSpace.coinduced.{u1, u2} α β f t₁) (TopologicalSpace.coinduced.{u1, u2} α β f t₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {t₁ : TopologicalSpace.{u1} α} {t₂ : TopologicalSpace.{u1} α} {f : α -> β}, Eq.{succ u2} (TopologicalSpace.{u2} β) (TopologicalSpace.coinduced.{u1, u2} α β f (Sup.sup.{u1} (TopologicalSpace.{u1} α) (SemilatticeSup.toSup.{u1} (TopologicalSpace.{u1} α) (Lattice.toSemilatticeSup.{u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α))))) t₁ t₂)) (Sup.sup.{u2} (TopologicalSpace.{u2} β) (SemilatticeSup.toSup.{u2} (TopologicalSpace.{u2} β) (Lattice.toSemilatticeSup.{u2} (TopologicalSpace.{u2} β) (ConditionallyCompleteLattice.toLattice.{u2} (TopologicalSpace.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u2} β))))) (TopologicalSpace.coinduced.{u1, u2} α β f t₁) (TopologicalSpace.coinduced.{u1, u2} α β f t₂))
Case conversion may be inaccurate. Consider using '#align coinduced_sup coinduced_supₓ'. -/
@[simp]
theorem coinduced_sup : (t₁ ⊔ t₂).coinduced f = t₁.coinduced f ⊔ t₂.coinduced f :=
  (gc_coinduced_induced f).l_sup
#align coinduced_sup coinduced_sup

/- warning: coinduced_supr -> coinduced_iSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u2}} {β : Type.{u3}} {f : α -> β} {ι : Sort.{u1}} {t : ι -> (TopologicalSpace.{u2} α)}, Eq.{succ u3} (TopologicalSpace.{u3} β) (TopologicalSpace.coinduced.{u2, u3} α β f (iSup.{u2, u1} (TopologicalSpace.{u2} α) (ConditionallyCompleteLattice.toHasSup.{u2} (TopologicalSpace.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} α) (TopologicalSpace.completeLattice.{u2} α))) ι (fun (i : ι) => t i))) (iSup.{u3, u1} (TopologicalSpace.{u3} β) (ConditionallyCompleteLattice.toHasSup.{u3} (TopologicalSpace.{u3} β) (CompleteLattice.toConditionallyCompleteLattice.{u3} (TopologicalSpace.{u3} β) (TopologicalSpace.completeLattice.{u3} β))) ι (fun (i : ι) => TopologicalSpace.coinduced.{u2, u3} α β f (t i)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {ι : Sort.{u3}} {t : ι -> (TopologicalSpace.{u2} α)}, Eq.{succ u1} (TopologicalSpace.{u1} β) (TopologicalSpace.coinduced.{u2, u1} α β f (iSup.{u2, u3} (TopologicalSpace.{u2} α) (ConditionallyCompleteLattice.toSupSet.{u2} (TopologicalSpace.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u2} α))) ι (fun (i : ι) => t i))) (iSup.{u1, u3} (TopologicalSpace.{u1} β) (ConditionallyCompleteLattice.toSupSet.{u1} (TopologicalSpace.{u1} β) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} β) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} β))) ι (fun (i : ι) => TopologicalSpace.coinduced.{u2, u1} α β f (t i)))
Case conversion may be inaccurate. Consider using '#align coinduced_supr coinduced_iSupₓ'. -/
@[simp]
theorem coinduced_iSup {ι : Sort w} {t : ι → TopologicalSpace α} :
    (⨆ i, t i).coinduced f = ⨆ i, (t i).coinduced f :=
  (gc_coinduced_induced f).l_iSup
#align coinduced_supr coinduced_iSup

#print induced_id /-
theorem induced_id [t : TopologicalSpace α] : t.induced id = t :=
  topologicalSpace_eq <|
    funext fun s => propext <| ⟨fun ⟨s', hs, h⟩ => h ▸ hs, fun hs => ⟨s, hs, rfl⟩⟩
#align induced_id induced_id
-/

/- warning: induced_compose -> induced_compose is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [tγ : TopologicalSpace.{u3} γ] {f : α -> β} {g : β -> γ}, Eq.{succ u1} (TopologicalSpace.{u1} α) (TopologicalSpace.induced.{u1, u2} α β f (TopologicalSpace.induced.{u2, u3} β γ g tγ)) (TopologicalSpace.induced.{u1, u3} α γ (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) tγ)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [tγ : TopologicalSpace.{u3} γ] {f : α -> β} {g : β -> γ}, Eq.{succ u2} (TopologicalSpace.{u2} α) (TopologicalSpace.induced.{u2, u1} α β f (TopologicalSpace.induced.{u1, u3} β γ g tγ)) (TopologicalSpace.induced.{u2, u3} α γ (Function.comp.{succ u2, succ u1, succ u3} α β γ g f) tγ)
Case conversion may be inaccurate. Consider using '#align induced_compose induced_composeₓ'. -/
theorem induced_compose [tγ : TopologicalSpace γ] {f : α → β} {g : β → γ} :
    (tγ.induced g).induced f = tγ.induced (g ∘ f) :=
  topologicalSpace_eq <|
    funext fun s =>
      propext <|
        ⟨fun ⟨s', ⟨s, hs, h₂⟩, h₁⟩ => h₁ ▸ h₂ ▸ ⟨s, hs, rfl⟩, fun ⟨s, hs, h⟩ =>
          ⟨preimage g s, ⟨s, hs, rfl⟩, h ▸ rfl⟩⟩
#align induced_compose induced_compose

/- warning: induced_const -> induced_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [t : TopologicalSpace.{u1} α] {x : α}, Eq.{succ u2} (TopologicalSpace.{u2} β) (TopologicalSpace.induced.{u2, u1} β α (fun (y : β) => x) t) (Top.top.{u2} (TopologicalSpace.{u2} β) (CompleteLattice.toHasTop.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.completeLattice.{u2} β)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [t : TopologicalSpace.{u2} α] {x : α}, Eq.{succ u1} (TopologicalSpace.{u1} β) (TopologicalSpace.induced.{u1, u2} β α (fun (y : β) => x) t) (Top.top.{u1} (TopologicalSpace.{u1} β) (CompleteLattice.toTop.{u1} (TopologicalSpace.{u1} β) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} β)))
Case conversion may be inaccurate. Consider using '#align induced_const induced_constₓ'. -/
theorem induced_const [t : TopologicalSpace α] {x : α} : (t.induced fun y : β => x) = ⊤ :=
  le_antisymm le_top (@continuous_const β α ⊤ t x).le_induced
#align induced_const induced_const

#print coinduced_id /-
theorem coinduced_id [t : TopologicalSpace α] : t.coinduced id = t :=
  topologicalSpace_eq rfl
#align coinduced_id coinduced_id
-/

/- warning: coinduced_compose -> coinduced_compose is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [tα : TopologicalSpace.{u1} α] {f : α -> β} {g : β -> γ}, Eq.{succ u3} (TopologicalSpace.{u3} γ) (TopologicalSpace.coinduced.{u2, u3} β γ g (TopologicalSpace.coinduced.{u1, u2} α β f tα)) (TopologicalSpace.coinduced.{u1, u3} α γ (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) tα)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} [tα : TopologicalSpace.{u3} α] {f : α -> β} {g : β -> γ}, Eq.{succ u2} (TopologicalSpace.{u2} γ) (TopologicalSpace.coinduced.{u1, u2} β γ g (TopologicalSpace.coinduced.{u3, u1} α β f tα)) (TopologicalSpace.coinduced.{u3, u2} α γ (Function.comp.{succ u3, succ u1, succ u2} α β γ g f) tα)
Case conversion may be inaccurate. Consider using '#align coinduced_compose coinduced_composeₓ'. -/
theorem coinduced_compose [tα : TopologicalSpace α] {f : α → β} {g : β → γ} :
    (tα.coinduced f).coinduced g = tα.coinduced (g ∘ f) :=
  topologicalSpace_eq rfl
#align coinduced_compose coinduced_compose

/- warning: equiv.induced_symm -> Equiv.induced_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : Equiv.{succ u1, succ u2} α β), Eq.{max (succ u1) (succ u2)} ((TopologicalSpace.{u1} α) -> (TopologicalSpace.{u2} β)) (TopologicalSpace.induced.{u2, u1} β α (coeFn.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2), max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} β α) (fun (_x : Equiv.{succ u2, succ u1} β α) => β -> α) (Equiv.hasCoeToFun.{succ u2, succ u1} β α) (Equiv.symm.{succ u1, succ u2} α β e))) (TopologicalSpace.coinduced.{u1, u2} α β (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) e))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : Equiv.{succ u2, succ u1} α β), Eq.{max (succ u2) (succ u1)} ((TopologicalSpace.{u2} α) -> (TopologicalSpace.{u1} β)) (TopologicalSpace.induced.{u1, u2} β α (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (Equiv.{succ u1, succ u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : β) => α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u2} β α) (Equiv.symm.{succ u2, succ u1} α β e))) (TopologicalSpace.coinduced.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => β) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u1} α β) e))
Case conversion may be inaccurate. Consider using '#align equiv.induced_symm Equiv.induced_symmₓ'. -/
theorem Equiv.induced_symm {α β : Type _} (e : α ≃ β) :
    TopologicalSpace.induced e.symm = TopologicalSpace.coinduced e :=
  by
  ext (t U)
  constructor
  · rintro ⟨V, hV, rfl⟩
    rwa [isOpen_coinduced, e.preimage_symm_preimage]
  · exact fun hU => ⟨e ⁻¹' U, hU, e.symm_preimage_preimage _⟩
#align equiv.induced_symm Equiv.induced_symm

/- warning: equiv.coinduced_symm -> Equiv.coinduced_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : Equiv.{succ u1, succ u2} α β), Eq.{max (succ u2) (succ u1)} ((TopologicalSpace.{u2} β) -> (TopologicalSpace.{u1} α)) (TopologicalSpace.coinduced.{u2, u1} β α (coeFn.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2), max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} β α) (fun (_x : Equiv.{succ u2, succ u1} β α) => β -> α) (Equiv.hasCoeToFun.{succ u2, succ u1} β α) (Equiv.symm.{succ u1, succ u2} α β e))) (TopologicalSpace.induced.{u1, u2} α β (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) e))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : Equiv.{succ u2, succ u1} α β), Eq.{max (succ u2) (succ u1)} ((TopologicalSpace.{u1} β) -> (TopologicalSpace.{u2} α)) (TopologicalSpace.coinduced.{u1, u2} β α (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (Equiv.{succ u1, succ u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : β) => α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u2} β α) (Equiv.symm.{succ u2, succ u1} α β e))) (TopologicalSpace.induced.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => β) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u1} α β) e))
Case conversion may be inaccurate. Consider using '#align equiv.coinduced_symm Equiv.coinduced_symmₓ'. -/
theorem Equiv.coinduced_symm {α β : Type _} (e : α ≃ β) :
    TopologicalSpace.coinduced e.symm = TopologicalSpace.induced e := by
  rw [← e.symm.induced_symm, e.symm_symm]
#align equiv.coinduced_symm Equiv.coinduced_symm

end GaloisConnection

-- constructions using the complete lattice structure
section Constructions

open TopologicalSpace

variable {α : Type u} {β : Type v}

#print inhabitedTopologicalSpace /-
instance inhabitedTopologicalSpace {α : Type u} : Inhabited (TopologicalSpace α) :=
  ⟨⊥⟩
#align inhabited_topological_space inhabitedTopologicalSpace
-/

#print Subsingleton.uniqueTopologicalSpace /-
instance (priority := 100) Subsingleton.uniqueTopologicalSpace [Subsingleton α] :
    Unique (TopologicalSpace α) where
  default := ⊥
  uniq t :=
    eq_bot_of_singletons_open fun x =>
      Subsingleton.set_cases (@isOpen_empty _ t) (@isOpen_univ _ t) ({x} : Set α)
#align subsingleton.unique_topological_space Subsingleton.uniqueTopologicalSpace
-/

#print Subsingleton.discreteTopology /-
instance (priority := 100) Subsingleton.discreteTopology [t : TopologicalSpace α] [Subsingleton α] :
    DiscreteTopology α :=
  ⟨Unique.eq_default t⟩
#align subsingleton.discrete_topology Subsingleton.discreteTopology
-/

instance : TopologicalSpace Empty :=
  ⊥

instance : DiscreteTopology Empty :=
  ⟨rfl⟩

instance : TopologicalSpace PEmpty :=
  ⊥

instance : DiscreteTopology PEmpty :=
  ⟨rfl⟩

instance : TopologicalSpace PUnit :=
  ⊥

instance : DiscreteTopology PUnit :=
  ⟨rfl⟩

instance : TopologicalSpace Bool :=
  ⊥

instance : DiscreteTopology Bool :=
  ⟨rfl⟩

instance : TopologicalSpace ℕ :=
  ⊥

instance : DiscreteTopology ℕ :=
  ⟨rfl⟩

instance : TopologicalSpace ℤ :=
  ⊥

instance : DiscreteTopology ℤ :=
  ⟨rfl⟩

instance {n} : TopologicalSpace (Fin n) :=
  ⊥

instance {n} : DiscreteTopology (Fin n) :=
  ⟨rfl⟩

#print sierpinskiSpace /-
instance sierpinskiSpace : TopologicalSpace Prop :=
  generateFrom {{True}}
#align sierpinski_space sierpinskiSpace
-/

#print continuous_empty_function /-
theorem continuous_empty_function [TopologicalSpace α] [TopologicalSpace β] [IsEmpty β]
    (f : α → β) : Continuous f :=
  letI := Function.isEmpty f
  continuous_of_discreteTopology
#align continuous_empty_function continuous_empty_function
-/

/- warning: le_generate_from -> le_generateFrom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {t : TopologicalSpace.{u1} α} {g : Set.{u1} (Set.{u1} α)}, (forall (s : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s g) -> (IsOpen.{u1} α t s)) -> (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toHasLe.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.partialOrder.{u1} α))) t (TopologicalSpace.generateFrom.{u1} α g))
but is expected to have type
  forall {α : Type.{u1}} {t : TopologicalSpace.{u1} α} {g : Set.{u1} (Set.{u1} α)}, (forall (s : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s g) -> (IsOpen.{u1} α t s)) -> (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toLE.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instPartialOrderTopologicalSpace.{u1} α))) t (TopologicalSpace.generateFrom.{u1} α g))
Case conversion may be inaccurate. Consider using '#align le_generate_from le_generateFromₓ'. -/
theorem le_generateFrom {t : TopologicalSpace α} {g : Set (Set α)} (h : ∀ s ∈ g, IsOpen s) :
    t ≤ generateFrom g :=
  le_generateFrom_iff_subset_isOpen.2 h
#align le_generate_from le_generateFrom

/- warning: induced_generate_from_eq -> induced_generateFrom_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {b : Set.{u2} (Set.{u2} β)} {f : α -> β}, Eq.{succ u1} (TopologicalSpace.{u1} α) (TopologicalSpace.induced.{u1, u2} α β f (TopologicalSpace.generateFrom.{u2} β b)) (TopologicalSpace.generateFrom.{u1} α (Set.image.{u2, u1} (Set.{u2} β) (Set.{u1} α) (Set.preimage.{u1, u2} α β f) b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {b : Set.{u1} (Set.{u1} β)} {f : α -> β}, Eq.{succ u2} (TopologicalSpace.{u2} α) (TopologicalSpace.induced.{u2, u1} α β f (TopologicalSpace.generateFrom.{u1} β b)) (TopologicalSpace.generateFrom.{u2} α (Set.image.{u1, u2} (Set.{u1} β) (Set.{u2} α) (Set.preimage.{u2, u1} α β f) b))
Case conversion may be inaccurate. Consider using '#align induced_generate_from_eq induced_generateFrom_eqₓ'. -/
theorem induced_generateFrom_eq {α β} {b : Set (Set β)} {f : α → β} :
    (generateFrom b).induced f = TopologicalSpace.generateFrom (preimage f '' b) :=
  le_antisymm (le_generateFrom <| ball_image_iff.2 fun s hs => ⟨s, GenerateOpen.basic _ hs, rfl⟩)
    (coinduced_le_iff_le_induced.1 <|
      le_generateFrom fun s hs => GenerateOpen.basic _ <| mem_image_of_mem _ hs)
#align induced_generate_from_eq induced_generateFrom_eq

/- warning: le_induced_generate_from -> le_induced_generateFrom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [t : TopologicalSpace.{u1} α] {b : Set.{u2} (Set.{u2} β)} {f : α -> β}, (forall (a : Set.{u2} β), (Membership.Mem.{u2, u2} (Set.{u2} β) (Set.{u2} (Set.{u2} β)) (Set.hasMem.{u2} (Set.{u2} β)) a b) -> (IsOpen.{u1} α t (Set.preimage.{u1, u2} α β f a))) -> (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toHasLe.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.partialOrder.{u1} α))) t (TopologicalSpace.induced.{u1, u2} α β f (TopologicalSpace.generateFrom.{u2} β b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [t : TopologicalSpace.{u2} α] {b : Set.{u1} (Set.{u1} β)} {f : α -> β}, (forall (a : Set.{u1} β), (Membership.mem.{u1, u1} (Set.{u1} β) (Set.{u1} (Set.{u1} β)) (Set.instMembershipSet.{u1} (Set.{u1} β)) a b) -> (IsOpen.{u2} α t (Set.preimage.{u2, u1} α β f a))) -> (LE.le.{u2} (TopologicalSpace.{u2} α) (Preorder.toLE.{u2} (TopologicalSpace.{u2} α) (PartialOrder.toPreorder.{u2} (TopologicalSpace.{u2} α) (TopologicalSpace.instPartialOrderTopologicalSpace.{u2} α))) t (TopologicalSpace.induced.{u2, u1} α β f (TopologicalSpace.generateFrom.{u1} β b)))
Case conversion may be inaccurate. Consider using '#align le_induced_generate_from le_induced_generateFromₓ'. -/
theorem le_induced_generateFrom {α β} [t : TopologicalSpace α] {b : Set (Set β)} {f : α → β}
    (h : ∀ a : Set β, a ∈ b → IsOpen (f ⁻¹' a)) : t ≤ induced f (generateFrom b) :=
  by
  rw [induced_generateFrom_eq]
  apply le_generateFrom
  simp only [mem_image, and_imp, forall_apply_eq_imp_iff₂, exists_imp]
  exact h
#align le_induced_generate_from le_induced_generateFrom

#print nhdsAdjoint /-
/-- This construction is left adjoint to the operation sending a topology on `α`
  to its neighborhood filter at a fixed point `a : α`. -/
def nhdsAdjoint (a : α) (f : Filter α) : TopologicalSpace α
    where
  IsOpen s := a ∈ s → s ∈ f
  isOpen_univ s := univ_mem
  isOpen_inter := fun s t hs ht ⟨has, hat⟩ => inter_mem (hs has) (ht hat)
  isOpen_sUnion := fun k hk ⟨u, hu, hau⟩ => mem_of_superset (hk u hu hau) (subset_sUnion_of_mem hu)
#align nhds_adjoint nhdsAdjoint
-/

/- warning: gc_nhds -> gc_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : α), GaloisConnection.{u1, u1} (Filter.{u1} α) (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α)) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.partialOrder.{u1} α)) (nhdsAdjoint.{u1} α a) (fun (t : TopologicalSpace.{u1} α) => nhds.{u1} α t a)
but is expected to have type
  forall {α : Type.{u1}} (a : α), GaloisConnection.{u1, u1} (Filter.{u1} α) (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α)) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instPartialOrderTopologicalSpace.{u1} α)) (nhdsAdjoint.{u1} α a) (fun (t : TopologicalSpace.{u1} α) => nhds.{u1} α t a)
Case conversion may be inaccurate. Consider using '#align gc_nhds gc_nhdsₓ'. -/
theorem gc_nhds (a : α) : GaloisConnection (nhdsAdjoint a) fun t => @nhds α t a := fun f t => by
  rw [le_nhds_iff]; exact ⟨fun H s hs has => H _ has hs, fun H s has hs => H _ hs has⟩
#align gc_nhds gc_nhds

/- warning: nhds_mono -> nhds_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {t₁ : TopologicalSpace.{u1} α} {t₂ : TopologicalSpace.{u1} α} {a : α}, (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toHasLe.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.partialOrder.{u1} α))) t₁ t₂) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toHasLe.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (nhds.{u1} α t₁ a) (nhds.{u1} α t₂ a))
but is expected to have type
  forall {α : Type.{u1}} {t₁ : TopologicalSpace.{u1} α} {t₂ : TopologicalSpace.{u1} α} {a : α}, (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toLE.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instPartialOrderTopologicalSpace.{u1} α))) t₁ t₂) -> (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (nhds.{u1} α t₁ a) (nhds.{u1} α t₂ a))
Case conversion may be inaccurate. Consider using '#align nhds_mono nhds_monoₓ'. -/
theorem nhds_mono {t₁ t₂ : TopologicalSpace α} {a : α} (h : t₁ ≤ t₂) :
    @nhds α t₁ a ≤ @nhds α t₂ a :=
  (gc_nhds a).monotone_u h
#align nhds_mono nhds_mono

/- warning: le_iff_nhds -> le_iff_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (t : TopologicalSpace.{u1} α) (t' : TopologicalSpace.{u1} α), Iff (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toHasLe.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.partialOrder.{u1} α))) t t') (forall (x : α), LE.le.{u1} (Filter.{u1} α) (Preorder.toHasLe.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (nhds.{u1} α t x) (nhds.{u1} α t' x))
but is expected to have type
  forall {α : Type.{u1}} (t : TopologicalSpace.{u1} α) (t' : TopologicalSpace.{u1} α), Iff (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toLE.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instPartialOrderTopologicalSpace.{u1} α))) t t') (forall (x : α), LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (nhds.{u1} α t x) (nhds.{u1} α t' x))
Case conversion may be inaccurate. Consider using '#align le_iff_nhds le_iff_nhdsₓ'. -/
theorem le_iff_nhds {α : Type _} (t t' : TopologicalSpace α) :
    t ≤ t' ↔ ∀ x, @nhds α t x ≤ @nhds α t' x :=
  ⟨fun h x => nhds_mono h, le_of_nhds_le_nhds⟩
#align le_iff_nhds le_iff_nhds

/- warning: nhds_adjoint_nhds -> nhdsAdjoint_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : α) (f : Filter.{u1} α), Eq.{succ u1} (Filter.{u1} α) (nhds.{u1} α (nhdsAdjoint.{u1} α a f) a) (Sup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))) (Pure.pure.{u1, u1} Filter.{u1} Filter.hasPure.{u1} α a) f)
but is expected to have type
  forall {α : Type.{u1}} (a : α) (f : Filter.{u1} α), Eq.{succ u1} (Filter.{u1} α) (nhds.{u1} α (nhdsAdjoint.{u1} α a f) a) (Sup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))))) (Pure.pure.{u1, u1} Filter.{u1} Filter.instPureFilter.{u1} α a) f)
Case conversion may be inaccurate. Consider using '#align nhds_adjoint_nhds nhdsAdjoint_nhdsₓ'. -/
theorem nhdsAdjoint_nhds {α : Type _} (a : α) (f : Filter α) :
    @nhds α (nhdsAdjoint a f) a = pure a ⊔ f :=
  by
  ext U
  rw [mem_nhds_iff]
  constructor
  · rintro ⟨t, htU, ht, hat⟩
    exact ⟨htU hat, mem_of_superset (ht hat) htU⟩
  · rintro ⟨haU, hU⟩
    exact ⟨U, subset.rfl, fun h => hU, haU⟩
#align nhds_adjoint_nhds nhdsAdjoint_nhds

#print nhdsAdjoint_nhds_of_ne /-
theorem nhdsAdjoint_nhds_of_ne {α : Type _} (a : α) (f : Filter α) {b : α} (h : b ≠ a) :
    @nhds α (nhdsAdjoint a f) b = pure b :=
  by
  apply le_antisymm
  · intro U hU
    rw [mem_nhds_iff]
    use {b}
    simp only [and_true_iff, singleton_subset_iff, mem_singleton]
    refine' ⟨hU, fun ha => (h.symm ha).elim⟩
  · exact @pure_le_nhds α (nhdsAdjoint a f) b
#align nhds_adjoint_nhds_of_ne nhdsAdjoint_nhds_of_ne
-/

#print isOpen_singleton_nhdsAdjoint /-
theorem isOpen_singleton_nhdsAdjoint {α : Type _} {a b : α} (f : Filter α) (hb : b ≠ a) :
    is_open[nhdsAdjoint a f] {b} :=
  by
  rw [isOpen_singleton_iff_nhds_eq_pure]
  exact nhdsAdjoint_nhds_of_ne a f hb
#align is_open_singleton_nhds_adjoint isOpen_singleton_nhdsAdjoint
-/

/- warning: le_nhds_adjoint_iff' -> le_nhdsAdjoint_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : α) (f : Filter.{u1} α) (t : TopologicalSpace.{u1} α), Iff (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toHasLe.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.partialOrder.{u1} α))) t (nhdsAdjoint.{u1} α a f)) (And (LE.le.{u1} (Filter.{u1} α) (Preorder.toHasLe.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (nhds.{u1} α t a) (Sup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))) (Pure.pure.{u1, u1} Filter.{u1} Filter.hasPure.{u1} α a) f)) (forall (b : α), (Ne.{succ u1} α b a) -> (Eq.{succ u1} (Filter.{u1} α) (nhds.{u1} α t b) (Pure.pure.{u1, u1} Filter.{u1} Filter.hasPure.{u1} α b))))
but is expected to have type
  forall {α : Type.{u1}} (a : α) (f : Filter.{u1} α) (t : TopologicalSpace.{u1} α), Iff (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toLE.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instPartialOrderTopologicalSpace.{u1} α))) t (nhdsAdjoint.{u1} α a f)) (And (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (nhds.{u1} α t a) (Sup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))))) (Pure.pure.{u1, u1} Filter.{u1} Filter.instPureFilter.{u1} α a) f)) (forall (b : α), (Ne.{succ u1} α b a) -> (Eq.{succ u1} (Filter.{u1} α) (nhds.{u1} α t b) (Pure.pure.{u1, u1} Filter.{u1} Filter.instPureFilter.{u1} α b))))
Case conversion may be inaccurate. Consider using '#align le_nhds_adjoint_iff' le_nhdsAdjoint_iff'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (b «expr ≠ » a) -/
theorem le_nhdsAdjoint_iff' {α : Type _} (a : α) (f : Filter α) (t : TopologicalSpace α) :
    t ≤ nhdsAdjoint a f ↔ @nhds α t a ≤ pure a ⊔ f ∧ ∀ (b) (_ : b ≠ a), @nhds α t b = pure b :=
  by
  rw [le_iff_nhds]
  constructor
  · intro h
    constructor
    · specialize h a
      rwa [nhdsAdjoint_nhds] at h
    · intro b hb
      apply le_antisymm _ (pure_le_nhds b)
      specialize h b
      rwa [nhdsAdjoint_nhds_of_ne a f hb] at h
  · rintro ⟨h, h'⟩ b
    by_cases hb : b = a
    · rwa [hb, nhdsAdjoint_nhds]
    · simp [nhdsAdjoint_nhds_of_ne a f hb, h' b hb]
#align le_nhds_adjoint_iff' le_nhdsAdjoint_iff'

/- warning: le_nhds_adjoint_iff -> le_nhdsAdjoint_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : α) (f : Filter.{u1} α) (t : TopologicalSpace.{u1} α), Iff (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toHasLe.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.partialOrder.{u1} α))) t (nhdsAdjoint.{u1} α a f)) (And (LE.le.{u1} (Filter.{u1} α) (Preorder.toHasLe.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (nhds.{u1} α t a) (Sup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))) (Pure.pure.{u1, u1} Filter.{u1} Filter.hasPure.{u1} α a) f)) (forall (b : α), (Ne.{succ u1} α b a) -> (IsOpen.{u1} α t (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) b))))
but is expected to have type
  forall {α : Type.{u1}} (a : α) (f : Filter.{u1} α) (t : TopologicalSpace.{u1} α), Iff (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toLE.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instPartialOrderTopologicalSpace.{u1} α))) t (nhdsAdjoint.{u1} α a f)) (And (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (nhds.{u1} α t a) (Sup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))))) (Pure.pure.{u1, u1} Filter.{u1} Filter.instPureFilter.{u1} α a) f)) (forall (b : α), (Ne.{succ u1} α b a) -> (IsOpen.{u1} α t (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) b))))
Case conversion may be inaccurate. Consider using '#align le_nhds_adjoint_iff le_nhdsAdjoint_iffₓ'. -/
theorem le_nhdsAdjoint_iff {α : Type _} (a : α) (f : Filter α) (t : TopologicalSpace α) :
    t ≤ nhdsAdjoint a f ↔ @nhds α t a ≤ pure a ⊔ f ∧ ∀ b, b ≠ a → is_open[t] {b} :=
  by
  change _ ↔ _ ∧ ∀ b : α, b ≠ a → IsOpen {b}
  rw [le_nhdsAdjoint_iff', and_congr_right_iff]
  apply fun h => forall_congr' fun b => _
  rw [@isOpen_singleton_iff_nhds_eq_pure α t b]
#align le_nhds_adjoint_iff le_nhdsAdjoint_iff

/- warning: nhds_infi -> nhds_iInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {t : ι -> (TopologicalSpace.{u1} α)} {a : α}, Eq.{succ u1} (Filter.{u1} α) (nhds.{u1} α (iInf.{u1, u2} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))) ι t) a) (iInf.{u1, u2} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ι (fun (i : ι) => nhds.{u1} α (t i) a))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {t : ι -> (TopologicalSpace.{u2} α)} {a : α}, Eq.{succ u2} (Filter.{u2} α) (nhds.{u2} α (iInf.{u2, u1} (TopologicalSpace.{u2} α) (ConditionallyCompleteLattice.toInfSet.{u2} (TopologicalSpace.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u2} α))) ι t) a) (iInf.{u2, u1} (Filter.{u2} α) (ConditionallyCompleteLattice.toInfSet.{u2} (Filter.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Filter.{u2} α) (Filter.instCompleteLatticeFilter.{u2} α))) ι (fun (i : ι) => nhds.{u2} α (t i) a))
Case conversion may be inaccurate. Consider using '#align nhds_infi nhds_iInfₓ'. -/
theorem nhds_iInf {ι : Sort _} {t : ι → TopologicalSpace α} {a : α} :
    @nhds α (iInf t) a = ⨅ i, @nhds α (t i) a :=
  (gc_nhds a).u_iInf
#align nhds_infi nhds_iInf

/- warning: nhds_Inf -> nhds_sInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} (TopologicalSpace.{u1} α)} {a : α}, Eq.{succ u1} (Filter.{u1} α) (nhds.{u1} α (InfSet.sInf.{u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))) s) a) (iInf.{u1, succ u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (TopologicalSpace.{u1} α) (fun (t : TopologicalSpace.{u1} α) => iInf.{u1, 0} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (Membership.Mem.{u1, u1} (TopologicalSpace.{u1} α) (Set.{u1} (TopologicalSpace.{u1} α)) (Set.hasMem.{u1} (TopologicalSpace.{u1} α)) t s) (fun (H : Membership.Mem.{u1, u1} (TopologicalSpace.{u1} α) (Set.{u1} (TopologicalSpace.{u1} α)) (Set.hasMem.{u1} (TopologicalSpace.{u1} α)) t s) => nhds.{u1} α t a)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} (TopologicalSpace.{u1} α)} {a : α}, Eq.{succ u1} (Filter.{u1} α) (nhds.{u1} α (InfSet.sInf.{u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toInfSet.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α))) s) a) (iInf.{u1, succ u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toInfSet.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))) (TopologicalSpace.{u1} α) (fun (t : TopologicalSpace.{u1} α) => iInf.{u1, 0} (Filter.{u1} α) (ConditionallyCompleteLattice.toInfSet.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))) (Membership.mem.{u1, u1} (TopologicalSpace.{u1} α) (Set.{u1} (TopologicalSpace.{u1} α)) (Set.instMembershipSet.{u1} (TopologicalSpace.{u1} α)) t s) (fun (H : Membership.mem.{u1, u1} (TopologicalSpace.{u1} α) (Set.{u1} (TopologicalSpace.{u1} α)) (Set.instMembershipSet.{u1} (TopologicalSpace.{u1} α)) t s) => nhds.{u1} α t a)))
Case conversion may be inaccurate. Consider using '#align nhds_Inf nhds_sInfₓ'. -/
theorem nhds_sInf {s : Set (TopologicalSpace α)} {a : α} :
    @nhds α (sInf s) a = ⨅ t ∈ s, @nhds α t a :=
  (gc_nhds a).u_sInf
#align nhds_Inf nhds_sInf

/- warning: nhds_inf -> nhds_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {t₁ : TopologicalSpace.{u1} α} {t₂ : TopologicalSpace.{u1} α} {a : α}, Eq.{succ u1} (Filter.{u1} α) (nhds.{u1} α (Inf.inf.{u1} (TopologicalSpace.{u1} α) (SemilatticeInf.toHasInf.{u1} (TopologicalSpace.{u1} α) (Lattice.toSemilatticeInf.{u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))))) t₁ t₂) a) (Inf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) (nhds.{u1} α t₁ a) (nhds.{u1} α t₂ a))
but is expected to have type
  forall {α : Type.{u1}} {t₁ : TopologicalSpace.{u1} α} {t₂ : TopologicalSpace.{u1} α} {a : α}, Eq.{succ u1} (Filter.{u1} α) (nhds.{u1} α (Inf.inf.{u1} (TopologicalSpace.{u1} α) (Lattice.toInf.{u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α)))) t₁ t₂) a) (Inf.inf.{u1} (Filter.{u1} α) (Filter.instInfFilter.{u1} α) (nhds.{u1} α t₁ a) (nhds.{u1} α t₂ a))
Case conversion may be inaccurate. Consider using '#align nhds_inf nhds_infₓ'. -/
theorem nhds_inf {t₁ t₂ : TopologicalSpace α} {a : α} :
    @nhds α (t₁ ⊓ t₂) a = @nhds α t₁ a ⊓ @nhds α t₂ a :=
  (gc_nhds a).u_inf
#align nhds_inf nhds_inf

/- warning: nhds_top -> nhds_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α}, Eq.{succ u1} (Filter.{u1} α) (nhds.{u1} α (Top.top.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toHasTop.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))) a) (Top.top.{u1} (Filter.{u1} α) (Filter.hasTop.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} {a : α}, Eq.{succ u1} (Filter.{u1} α) (nhds.{u1} α (Top.top.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toTop.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α))) a) (Top.top.{u1} (Filter.{u1} α) (Filter.instTopFilter.{u1} α))
Case conversion may be inaccurate. Consider using '#align nhds_top nhds_topₓ'. -/
theorem nhds_top {a : α} : @nhds α ⊤ a = ⊤ :=
  (gc_nhds a).u_top
#align nhds_top nhds_top

/- warning: is_open_sup -> isOpen_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {t₁ : TopologicalSpace.{u1} α} {t₂ : TopologicalSpace.{u1} α} {s : Set.{u1} α}, Iff (IsOpen.{u1} α (Sup.sup.{u1} (TopologicalSpace.{u1} α) (SemilatticeSup.toHasSup.{u1} (TopologicalSpace.{u1} α) (Lattice.toSemilatticeSup.{u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))))) t₁ t₂) s) (And (IsOpen.{u1} α t₁ s) (IsOpen.{u1} α t₂ s))
but is expected to have type
  forall {α : Type.{u1}} {t₁ : TopologicalSpace.{u1} α} {t₂ : TopologicalSpace.{u1} α} {s : Set.{u1} α}, Iff (IsOpen.{u1} α (Sup.sup.{u1} (TopologicalSpace.{u1} α) (SemilatticeSup.toSup.{u1} (TopologicalSpace.{u1} α) (Lattice.toSemilatticeSup.{u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α))))) t₁ t₂) s) (And (IsOpen.{u1} α t₁ s) (IsOpen.{u1} α t₂ s))
Case conversion may be inaccurate. Consider using '#align is_open_sup isOpen_supₓ'. -/
theorem isOpen_sup {t₁ t₂ : TopologicalSpace α} {s : Set α} :
    is_open[t₁ ⊔ t₂] s ↔ is_open[t₁] s ∧ is_open[t₂] s :=
  Iff.rfl
#align is_open_sup isOpen_sup

-- mathport name: exprcont
local notation "cont" => @Continuous _ _

-- mathport name: exprtspace
local notation "tspace" => TopologicalSpace

open TopologicalSpace

variable {γ : Type _} {f : α → β} {ι : Sort _}

/- warning: continuous_iff_coinduced_le -> continuous_iff_coinduced_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {t₁ : TopologicalSpace.{u1} α} {t₂ : TopologicalSpace.{u2} β}, Iff (Continuous.{u1, u2} α β t₁ t₂ f) (LE.le.{u2} (TopologicalSpace.{u2} β) (Preorder.toHasLe.{u2} (TopologicalSpace.{u2} β) (PartialOrder.toPreorder.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.partialOrder.{u2} β))) (TopologicalSpace.coinduced.{u1, u2} α β f t₁) t₂)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {t₁ : TopologicalSpace.{u1} α} {t₂ : TopologicalSpace.{u2} β}, Iff (Continuous.{u1, u2} α β t₁ t₂ f) (LE.le.{u2} (TopologicalSpace.{u2} β) (Preorder.toLE.{u2} (TopologicalSpace.{u2} β) (PartialOrder.toPreorder.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.instPartialOrderTopologicalSpace.{u2} β))) (TopologicalSpace.coinduced.{u1, u2} α β f t₁) t₂)
Case conversion may be inaccurate. Consider using '#align continuous_iff_coinduced_le continuous_iff_coinduced_leₓ'. -/
theorem continuous_iff_coinduced_le {t₁ : tspace α} {t₂ : tspace β} :
    cont t₁ t₂ f ↔ coinduced f t₁ ≤ t₂ :=
  continuous_def.trans Iff.rfl
#align continuous_iff_coinduced_le continuous_iff_coinduced_le

/- warning: continuous_iff_le_induced -> continuous_iff_le_induced is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {t₁ : TopologicalSpace.{u1} α} {t₂ : TopologicalSpace.{u2} β}, Iff (Continuous.{u1, u2} α β t₁ t₂ f) (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toHasLe.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.partialOrder.{u1} α))) t₁ (TopologicalSpace.induced.{u1, u2} α β f t₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {t₁ : TopologicalSpace.{u1} α} {t₂ : TopologicalSpace.{u2} β}, Iff (Continuous.{u1, u2} α β t₁ t₂ f) (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toLE.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instPartialOrderTopologicalSpace.{u1} α))) t₁ (TopologicalSpace.induced.{u1, u2} α β f t₂))
Case conversion may be inaccurate. Consider using '#align continuous_iff_le_induced continuous_iff_le_inducedₓ'. -/
theorem continuous_iff_le_induced {t₁ : tspace α} {t₂ : tspace β} :
    cont t₁ t₂ f ↔ t₁ ≤ induced f t₂ :=
  Iff.trans continuous_iff_coinduced_le (gc_coinduced_induced f _ _)
#align continuous_iff_le_induced continuous_iff_le_induced

#print continuous_generateFrom /-
theorem continuous_generateFrom {t : tspace α} {b : Set (Set β)} (h : ∀ s ∈ b, IsOpen (f ⁻¹' s)) :
    cont t (generateFrom b) f :=
  continuous_iff_coinduced_le.2 <| le_generateFrom h
#align continuous_generated_from continuous_generateFrom
-/

#print continuous_induced_dom /-
@[continuity]
theorem continuous_induced_dom {t : tspace β} : cont (induced f t) t f := by rw [continuous_def];
  intro s h; exact ⟨_, h, rfl⟩
#align continuous_induced_dom continuous_induced_dom
-/

/- warning: continuous_induced_rng -> continuous_induced_rng is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β} {g : γ -> α} {t₂ : TopologicalSpace.{u2} β} {t₁ : TopologicalSpace.{u3} γ}, Iff (Continuous.{u3, u1} γ α t₁ (TopologicalSpace.induced.{u1, u2} α β f t₂) g) (Continuous.{u3, u2} γ β t₁ t₂ (Function.comp.{succ u3, succ u1, succ u2} γ α β f g))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} {f : α -> β} {g : γ -> α} {t₂ : TopologicalSpace.{u3} β} {t₁ : TopologicalSpace.{u1} γ}, Iff (Continuous.{u1, u2} γ α t₁ (TopologicalSpace.induced.{u2, u3} α β f t₂) g) (Continuous.{u1, u3} γ β t₁ t₂ (Function.comp.{succ u1, succ u2, succ u3} γ α β f g))
Case conversion may be inaccurate. Consider using '#align continuous_induced_rng continuous_induced_rngₓ'. -/
theorem continuous_induced_rng {g : γ → α} {t₂ : tspace β} {t₁ : tspace γ} :
    cont t₁ (induced f t₂) g ↔ cont t₁ t₂ (f ∘ g) := by
  simp only [continuous_iff_le_induced, induced_compose]
#align continuous_induced_rng continuous_induced_rng

#print continuous_coinduced_rng /-
theorem continuous_coinduced_rng {t : tspace α} : cont t (coinduced f t) f := by
  rw [continuous_def]; intro s h; exact h
#align continuous_coinduced_rng continuous_coinduced_rng
-/

/- warning: continuous_coinduced_dom -> continuous_coinduced_dom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β} {g : β -> γ} {t₁ : TopologicalSpace.{u1} α} {t₂ : TopologicalSpace.{u3} γ}, Iff (Continuous.{u2, u3} β γ (TopologicalSpace.coinduced.{u1, u2} α β f t₁) t₂ g) (Continuous.{u1, u3} α γ t₁ t₂ (Function.comp.{succ u1, succ u2, succ u3} α β γ g f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} {f : α -> β} {g : β -> γ} {t₁ : TopologicalSpace.{u2} α} {t₂ : TopologicalSpace.{u1} γ}, Iff (Continuous.{u3, u1} β γ (TopologicalSpace.coinduced.{u2, u3} α β f t₁) t₂ g) (Continuous.{u2, u1} α γ t₁ t₂ (Function.comp.{succ u2, succ u3, succ u1} α β γ g f))
Case conversion may be inaccurate. Consider using '#align continuous_coinduced_dom continuous_coinduced_domₓ'. -/
theorem continuous_coinduced_dom {g : β → γ} {t₁ : tspace α} {t₂ : tspace γ} :
    cont (coinduced f t₁) t₂ g ↔ cont t₁ t₂ (g ∘ f) := by
  simp only [continuous_iff_coinduced_le, coinduced_compose]
#align continuous_coinduced_dom continuous_coinduced_dom

/- warning: continuous_le_dom -> continuous_le_dom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {t₁ : TopologicalSpace.{u1} α} {t₂ : TopologicalSpace.{u1} α} {t₃ : TopologicalSpace.{u2} β}, (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toHasLe.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.partialOrder.{u1} α))) t₂ t₁) -> (Continuous.{u1, u2} α β t₁ t₃ f) -> (Continuous.{u1, u2} α β t₂ t₃ f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {t₁ : TopologicalSpace.{u1} α} {t₂ : TopologicalSpace.{u1} α} {t₃ : TopologicalSpace.{u2} β}, (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toLE.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instPartialOrderTopologicalSpace.{u1} α))) t₂ t₁) -> (Continuous.{u1, u2} α β t₁ t₃ f) -> (Continuous.{u1, u2} α β t₂ t₃ f)
Case conversion may be inaccurate. Consider using '#align continuous_le_dom continuous_le_domₓ'. -/
theorem continuous_le_dom {t₁ t₂ : tspace α} {t₃ : tspace β} (h₁ : t₂ ≤ t₁) (h₂ : cont t₁ t₃ f) :
    cont t₂ t₃ f := by
  rw [continuous_def] at h₂⊢
  intro s h
  exact h₁ _ (h₂ s h)
#align continuous_le_dom continuous_le_dom

/- warning: continuous_le_rng -> continuous_le_rng is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {t₁ : TopologicalSpace.{u1} α} {t₂ : TopologicalSpace.{u2} β} {t₃ : TopologicalSpace.{u2} β}, (LE.le.{u2} (TopologicalSpace.{u2} β) (Preorder.toHasLe.{u2} (TopologicalSpace.{u2} β) (PartialOrder.toPreorder.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.partialOrder.{u2} β))) t₂ t₃) -> (Continuous.{u1, u2} α β t₁ t₂ f) -> (Continuous.{u1, u2} α β t₁ t₃ f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {t₁ : TopologicalSpace.{u1} α} {t₂ : TopologicalSpace.{u2} β} {t₃ : TopologicalSpace.{u2} β}, (LE.le.{u2} (TopologicalSpace.{u2} β) (Preorder.toLE.{u2} (TopologicalSpace.{u2} β) (PartialOrder.toPreorder.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.instPartialOrderTopologicalSpace.{u2} β))) t₂ t₃) -> (Continuous.{u1, u2} α β t₁ t₂ f) -> (Continuous.{u1, u2} α β t₁ t₃ f)
Case conversion may be inaccurate. Consider using '#align continuous_le_rng continuous_le_rngₓ'. -/
theorem continuous_le_rng {t₁ : tspace α} {t₂ t₃ : tspace β} (h₁ : t₂ ≤ t₃) (h₂ : cont t₁ t₂ f) :
    cont t₁ t₃ f := by
  rw [continuous_def] at h₂⊢
  intro s h
  exact h₂ s (h₁ s h)
#align continuous_le_rng continuous_le_rng

/- warning: continuous_sup_dom -> continuous_sup_dom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {t₁ : TopologicalSpace.{u1} α} {t₂ : TopologicalSpace.{u1} α} {t₃ : TopologicalSpace.{u2} β}, Iff (Continuous.{u1, u2} α β (Sup.sup.{u1} (TopologicalSpace.{u1} α) (SemilatticeSup.toHasSup.{u1} (TopologicalSpace.{u1} α) (Lattice.toSemilatticeSup.{u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))))) t₁ t₂) t₃ f) (And (Continuous.{u1, u2} α β t₁ t₃ f) (Continuous.{u1, u2} α β t₂ t₃ f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {t₁ : TopologicalSpace.{u1} α} {t₂ : TopologicalSpace.{u1} α} {t₃ : TopologicalSpace.{u2} β}, Iff (Continuous.{u1, u2} α β (Sup.sup.{u1} (TopologicalSpace.{u1} α) (SemilatticeSup.toSup.{u1} (TopologicalSpace.{u1} α) (Lattice.toSemilatticeSup.{u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α))))) t₁ t₂) t₃ f) (And (Continuous.{u1, u2} α β t₁ t₃ f) (Continuous.{u1, u2} α β t₂ t₃ f))
Case conversion may be inaccurate. Consider using '#align continuous_sup_dom continuous_sup_domₓ'. -/
theorem continuous_sup_dom {t₁ t₂ : tspace α} {t₃ : tspace β} :
    cont (t₁ ⊔ t₂) t₃ f ↔ cont t₁ t₃ f ∧ cont t₂ t₃ f := by
  simp only [continuous_iff_le_induced, sup_le_iff]
#align continuous_sup_dom continuous_sup_dom

/- warning: continuous_sup_rng_left -> continuous_sup_rng_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {t₁ : TopologicalSpace.{u1} α} {t₃ : TopologicalSpace.{u2} β} {t₂ : TopologicalSpace.{u2} β}, (Continuous.{u1, u2} α β t₁ t₂ f) -> (Continuous.{u1, u2} α β t₁ (Sup.sup.{u2} (TopologicalSpace.{u2} β) (SemilatticeSup.toHasSup.{u2} (TopologicalSpace.{u2} β) (Lattice.toSemilatticeSup.{u2} (TopologicalSpace.{u2} β) (ConditionallyCompleteLattice.toLattice.{u2} (TopologicalSpace.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.completeLattice.{u2} β))))) t₂ t₃) f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {t₁ : TopologicalSpace.{u1} α} {t₃ : TopologicalSpace.{u2} β} {t₂ : TopologicalSpace.{u2} β}, (Continuous.{u1, u2} α β t₁ t₂ f) -> (Continuous.{u1, u2} α β t₁ (Sup.sup.{u2} (TopologicalSpace.{u2} β) (SemilatticeSup.toSup.{u2} (TopologicalSpace.{u2} β) (Lattice.toSemilatticeSup.{u2} (TopologicalSpace.{u2} β) (ConditionallyCompleteLattice.toLattice.{u2} (TopologicalSpace.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u2} β))))) t₂ t₃) f)
Case conversion may be inaccurate. Consider using '#align continuous_sup_rng_left continuous_sup_rng_leftₓ'. -/
theorem continuous_sup_rng_left {t₁ : tspace α} {t₃ t₂ : tspace β} :
    cont t₁ t₂ f → cont t₁ (t₂ ⊔ t₃) f :=
  continuous_le_rng le_sup_left
#align continuous_sup_rng_left continuous_sup_rng_left

/- warning: continuous_sup_rng_right -> continuous_sup_rng_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {t₁ : TopologicalSpace.{u1} α} {t₃ : TopologicalSpace.{u2} β} {t₂ : TopologicalSpace.{u2} β}, (Continuous.{u1, u2} α β t₁ t₃ f) -> (Continuous.{u1, u2} α β t₁ (Sup.sup.{u2} (TopologicalSpace.{u2} β) (SemilatticeSup.toHasSup.{u2} (TopologicalSpace.{u2} β) (Lattice.toSemilatticeSup.{u2} (TopologicalSpace.{u2} β) (ConditionallyCompleteLattice.toLattice.{u2} (TopologicalSpace.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.completeLattice.{u2} β))))) t₂ t₃) f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {t₁ : TopologicalSpace.{u1} α} {t₃ : TopologicalSpace.{u2} β} {t₂ : TopologicalSpace.{u2} β}, (Continuous.{u1, u2} α β t₁ t₃ f) -> (Continuous.{u1, u2} α β t₁ (Sup.sup.{u2} (TopologicalSpace.{u2} β) (SemilatticeSup.toSup.{u2} (TopologicalSpace.{u2} β) (Lattice.toSemilatticeSup.{u2} (TopologicalSpace.{u2} β) (ConditionallyCompleteLattice.toLattice.{u2} (TopologicalSpace.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u2} β))))) t₂ t₃) f)
Case conversion may be inaccurate. Consider using '#align continuous_sup_rng_right continuous_sup_rng_rightₓ'. -/
theorem continuous_sup_rng_right {t₁ : tspace α} {t₃ t₂ : tspace β} :
    cont t₁ t₃ f → cont t₁ (t₂ ⊔ t₃) f :=
  continuous_le_rng le_sup_right
#align continuous_sup_rng_right continuous_sup_rng_right

/- warning: continuous_Sup_dom -> continuous_sSup_dom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {T : Set.{u1} (TopologicalSpace.{u1} α)} {t₂ : TopologicalSpace.{u2} β}, Iff (Continuous.{u1, u2} α β (SupSet.sSup.{u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toHasSup.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))) T) t₂ f) (forall (t : TopologicalSpace.{u1} α), (Membership.Mem.{u1, u1} (TopologicalSpace.{u1} α) (Set.{u1} (TopologicalSpace.{u1} α)) (Set.hasMem.{u1} (TopologicalSpace.{u1} α)) t T) -> (Continuous.{u1, u2} α β t t₂ f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {T : Set.{u1} (TopologicalSpace.{u1} α)} {t₂ : TopologicalSpace.{u2} β}, Iff (Continuous.{u1, u2} α β (SupSet.sSup.{u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toSupSet.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α))) T) t₂ f) (forall (t : TopologicalSpace.{u1} α), (Membership.mem.{u1, u1} (TopologicalSpace.{u1} α) (Set.{u1} (TopologicalSpace.{u1} α)) (Set.instMembershipSet.{u1} (TopologicalSpace.{u1} α)) t T) -> (Continuous.{u1, u2} α β t t₂ f))
Case conversion may be inaccurate. Consider using '#align continuous_Sup_dom continuous_sSup_domₓ'. -/
theorem continuous_sSup_dom {T : Set (tspace α)} {t₂ : tspace β} :
    cont (sSup T) t₂ f ↔ ∀ t ∈ T, cont t t₂ f := by
  simp only [continuous_iff_le_induced, sSup_le_iff]
#align continuous_Sup_dom continuous_sSup_dom

/- warning: continuous_Sup_rng -> continuous_sSup_rng is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {t₁ : TopologicalSpace.{u1} α} {t₂ : Set.{u2} (TopologicalSpace.{u2} β)} {t : TopologicalSpace.{u2} β}, (Membership.Mem.{u2, u2} (TopologicalSpace.{u2} β) (Set.{u2} (TopologicalSpace.{u2} β)) (Set.hasMem.{u2} (TopologicalSpace.{u2} β)) t t₂) -> (Continuous.{u1, u2} α β t₁ t f) -> (Continuous.{u1, u2} α β t₁ (SupSet.sSup.{u2} (TopologicalSpace.{u2} β) (ConditionallyCompleteLattice.toHasSup.{u2} (TopologicalSpace.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.completeLattice.{u2} β))) t₂) f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {t₁ : TopologicalSpace.{u1} α} {t₂ : Set.{u2} (TopologicalSpace.{u2} β)} {t : TopologicalSpace.{u2} β}, (Membership.mem.{u2, u2} (TopologicalSpace.{u2} β) (Set.{u2} (TopologicalSpace.{u2} β)) (Set.instMembershipSet.{u2} (TopologicalSpace.{u2} β)) t t₂) -> (Continuous.{u1, u2} α β t₁ t f) -> (Continuous.{u1, u2} α β t₁ (SupSet.sSup.{u2} (TopologicalSpace.{u2} β) (ConditionallyCompleteLattice.toSupSet.{u2} (TopologicalSpace.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u2} β))) t₂) f)
Case conversion may be inaccurate. Consider using '#align continuous_Sup_rng continuous_sSup_rngₓ'. -/
theorem continuous_sSup_rng {t₁ : tspace α} {t₂ : Set (tspace β)} {t : tspace β} (h₁ : t ∈ t₂)
    (hf : cont t₁ t f) : cont t₁ (sSup t₂) f :=
  continuous_iff_coinduced_le.2 <| le_sSup_of_le h₁ <| continuous_iff_coinduced_le.1 hf
#align continuous_Sup_rng continuous_sSup_rng

/- warning: continuous_supr_dom -> continuous_iSup_dom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {ι : Sort.{u3}} {t₁ : ι -> (TopologicalSpace.{u1} α)} {t₂ : TopologicalSpace.{u2} β}, Iff (Continuous.{u1, u2} α β (iSup.{u1, u3} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toHasSup.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))) ι t₁) t₂ f) (forall (i : ι), Continuous.{u1, u2} α β (t₁ i) t₂ f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {f : α -> β} {ι : Sort.{u1}} {t₁ : ι -> (TopologicalSpace.{u2} α)} {t₂ : TopologicalSpace.{u3} β}, Iff (Continuous.{u2, u3} α β (iSup.{u2, u1} (TopologicalSpace.{u2} α) (ConditionallyCompleteLattice.toSupSet.{u2} (TopologicalSpace.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u2} α))) ι t₁) t₂ f) (forall (i : ι), Continuous.{u2, u3} α β (t₁ i) t₂ f)
Case conversion may be inaccurate. Consider using '#align continuous_supr_dom continuous_iSup_domₓ'. -/
theorem continuous_iSup_dom {t₁ : ι → tspace α} {t₂ : tspace β} :
    cont (iSup t₁) t₂ f ↔ ∀ i, cont (t₁ i) t₂ f := by
  simp only [continuous_iff_le_induced, iSup_le_iff]
#align continuous_supr_dom continuous_iSup_dom

/- warning: continuous_supr_rng -> continuous_iSup_rng is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {ι : Sort.{u3}} {t₁ : TopologicalSpace.{u1} α} {t₂ : ι -> (TopologicalSpace.{u2} β)} {i : ι}, (Continuous.{u1, u2} α β t₁ (t₂ i) f) -> (Continuous.{u1, u2} α β t₁ (iSup.{u2, u3} (TopologicalSpace.{u2} β) (ConditionallyCompleteLattice.toHasSup.{u2} (TopologicalSpace.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.completeLattice.{u2} β))) ι t₂) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {f : α -> β} {ι : Sort.{u1}} {t₁ : TopologicalSpace.{u2} α} {t₂ : ι -> (TopologicalSpace.{u3} β)} {i : ι}, (Continuous.{u2, u3} α β t₁ (t₂ i) f) -> (Continuous.{u2, u3} α β t₁ (iSup.{u3, u1} (TopologicalSpace.{u3} β) (ConditionallyCompleteLattice.toSupSet.{u3} (TopologicalSpace.{u3} β) (CompleteLattice.toConditionallyCompleteLattice.{u3} (TopologicalSpace.{u3} β) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u3} β))) ι t₂) f)
Case conversion may be inaccurate. Consider using '#align continuous_supr_rng continuous_iSup_rngₓ'. -/
theorem continuous_iSup_rng {t₁ : tspace α} {t₂ : ι → tspace β} {i : ι} (h : cont t₁ (t₂ i) f) :
    cont t₁ (iSup t₂) f :=
  continuous_sSup_rng ⟨i, rfl⟩ h
#align continuous_supr_rng continuous_iSup_rng

/- warning: continuous_inf_rng -> continuous_inf_rng is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {t₁ : TopologicalSpace.{u1} α} {t₂ : TopologicalSpace.{u2} β} {t₃ : TopologicalSpace.{u2} β}, Iff (Continuous.{u1, u2} α β t₁ (Inf.inf.{u2} (TopologicalSpace.{u2} β) (SemilatticeInf.toHasInf.{u2} (TopologicalSpace.{u2} β) (Lattice.toSemilatticeInf.{u2} (TopologicalSpace.{u2} β) (ConditionallyCompleteLattice.toLattice.{u2} (TopologicalSpace.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.completeLattice.{u2} β))))) t₂ t₃) f) (And (Continuous.{u1, u2} α β t₁ t₂ f) (Continuous.{u1, u2} α β t₁ t₃ f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {t₁ : TopologicalSpace.{u1} α} {t₂ : TopologicalSpace.{u2} β} {t₃ : TopologicalSpace.{u2} β}, Iff (Continuous.{u1, u2} α β t₁ (Inf.inf.{u2} (TopologicalSpace.{u2} β) (Lattice.toInf.{u2} (TopologicalSpace.{u2} β) (ConditionallyCompleteLattice.toLattice.{u2} (TopologicalSpace.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u2} β)))) t₂ t₃) f) (And (Continuous.{u1, u2} α β t₁ t₂ f) (Continuous.{u1, u2} α β t₁ t₃ f))
Case conversion may be inaccurate. Consider using '#align continuous_inf_rng continuous_inf_rngₓ'. -/
theorem continuous_inf_rng {t₁ : tspace α} {t₂ t₃ : tspace β} :
    cont t₁ (t₂ ⊓ t₃) f ↔ cont t₁ t₂ f ∧ cont t₁ t₃ f := by
  simp only [continuous_iff_coinduced_le, le_inf_iff]
#align continuous_inf_rng continuous_inf_rng

/- warning: continuous_inf_dom_left -> continuous_inf_dom_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {t₁ : TopologicalSpace.{u1} α} {t₂ : TopologicalSpace.{u1} α} {t₃ : TopologicalSpace.{u2} β}, (Continuous.{u1, u2} α β t₁ t₃ f) -> (Continuous.{u1, u2} α β (Inf.inf.{u1} (TopologicalSpace.{u1} α) (SemilatticeInf.toHasInf.{u1} (TopologicalSpace.{u1} α) (Lattice.toSemilatticeInf.{u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))))) t₁ t₂) t₃ f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {t₁ : TopologicalSpace.{u1} α} {t₂ : TopologicalSpace.{u1} α} {t₃ : TopologicalSpace.{u2} β}, (Continuous.{u1, u2} α β t₁ t₃ f) -> (Continuous.{u1, u2} α β (Inf.inf.{u1} (TopologicalSpace.{u1} α) (Lattice.toInf.{u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α)))) t₁ t₂) t₃ f)
Case conversion may be inaccurate. Consider using '#align continuous_inf_dom_left continuous_inf_dom_leftₓ'. -/
theorem continuous_inf_dom_left {t₁ t₂ : tspace α} {t₃ : tspace β} :
    cont t₁ t₃ f → cont (t₁ ⊓ t₂) t₃ f :=
  continuous_le_dom inf_le_left
#align continuous_inf_dom_left continuous_inf_dom_left

/- warning: continuous_inf_dom_right -> continuous_inf_dom_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {t₁ : TopologicalSpace.{u1} α} {t₂ : TopologicalSpace.{u1} α} {t₃ : TopologicalSpace.{u2} β}, (Continuous.{u1, u2} α β t₂ t₃ f) -> (Continuous.{u1, u2} α β (Inf.inf.{u1} (TopologicalSpace.{u1} α) (SemilatticeInf.toHasInf.{u1} (TopologicalSpace.{u1} α) (Lattice.toSemilatticeInf.{u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))))) t₁ t₂) t₃ f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {t₁ : TopologicalSpace.{u1} α} {t₂ : TopologicalSpace.{u1} α} {t₃ : TopologicalSpace.{u2} β}, (Continuous.{u1, u2} α β t₂ t₃ f) -> (Continuous.{u1, u2} α β (Inf.inf.{u1} (TopologicalSpace.{u1} α) (Lattice.toInf.{u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α)))) t₁ t₂) t₃ f)
Case conversion may be inaccurate. Consider using '#align continuous_inf_dom_right continuous_inf_dom_rightₓ'. -/
theorem continuous_inf_dom_right {t₁ t₂ : tspace α} {t₃ : tspace β} :
    cont t₂ t₃ f → cont (t₁ ⊓ t₂) t₃ f :=
  continuous_le_dom inf_le_right
#align continuous_inf_dom_right continuous_inf_dom_right

/- warning: continuous_Inf_dom -> continuous_sInf_dom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {t₁ : Set.{u1} (TopologicalSpace.{u1} α)} {t₂ : TopologicalSpace.{u2} β} {t : TopologicalSpace.{u1} α}, (Membership.Mem.{u1, u1} (TopologicalSpace.{u1} α) (Set.{u1} (TopologicalSpace.{u1} α)) (Set.hasMem.{u1} (TopologicalSpace.{u1} α)) t t₁) -> (Continuous.{u1, u2} α β t t₂ f) -> (Continuous.{u1, u2} α β (InfSet.sInf.{u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))) t₁) t₂ f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {t₁ : Set.{u1} (TopologicalSpace.{u1} α)} {t₂ : TopologicalSpace.{u2} β} {t : TopologicalSpace.{u1} α}, (Membership.mem.{u1, u1} (TopologicalSpace.{u1} α) (Set.{u1} (TopologicalSpace.{u1} α)) (Set.instMembershipSet.{u1} (TopologicalSpace.{u1} α)) t t₁) -> (Continuous.{u1, u2} α β t t₂ f) -> (Continuous.{u1, u2} α β (InfSet.sInf.{u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toInfSet.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α))) t₁) t₂ f)
Case conversion may be inaccurate. Consider using '#align continuous_Inf_dom continuous_sInf_domₓ'. -/
theorem continuous_sInf_dom {t₁ : Set (tspace α)} {t₂ : tspace β} {t : tspace α} (h₁ : t ∈ t₁) :
    cont t t₂ f → cont (sInf t₁) t₂ f :=
  continuous_le_dom <| sInf_le h₁
#align continuous_Inf_dom continuous_sInf_dom

/- warning: continuous_Inf_rng -> continuous_sInf_rng is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {t₁ : TopologicalSpace.{u1} α} {T : Set.{u2} (TopologicalSpace.{u2} β)}, Iff (Continuous.{u1, u2} α β t₁ (InfSet.sInf.{u2} (TopologicalSpace.{u2} β) (ConditionallyCompleteLattice.toHasInf.{u2} (TopologicalSpace.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.completeLattice.{u2} β))) T) f) (forall (t : TopologicalSpace.{u2} β), (Membership.Mem.{u2, u2} (TopologicalSpace.{u2} β) (Set.{u2} (TopologicalSpace.{u2} β)) (Set.hasMem.{u2} (TopologicalSpace.{u2} β)) t T) -> (Continuous.{u1, u2} α β t₁ t f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {t₁ : TopologicalSpace.{u1} α} {T : Set.{u2} (TopologicalSpace.{u2} β)}, Iff (Continuous.{u1, u2} α β t₁ (InfSet.sInf.{u2} (TopologicalSpace.{u2} β) (ConditionallyCompleteLattice.toInfSet.{u2} (TopologicalSpace.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u2} β))) T) f) (forall (t : TopologicalSpace.{u2} β), (Membership.mem.{u2, u2} (TopologicalSpace.{u2} β) (Set.{u2} (TopologicalSpace.{u2} β)) (Set.instMembershipSet.{u2} (TopologicalSpace.{u2} β)) t T) -> (Continuous.{u1, u2} α β t₁ t f))
Case conversion may be inaccurate. Consider using '#align continuous_Inf_rng continuous_sInf_rngₓ'. -/
theorem continuous_sInf_rng {t₁ : tspace α} {T : Set (tspace β)} :
    cont t₁ (sInf T) f ↔ ∀ t ∈ T, cont t₁ t f := by
  simp only [continuous_iff_coinduced_le, le_sInf_iff]
#align continuous_Inf_rng continuous_sInf_rng

/- warning: continuous_infi_dom -> continuous_iInf_dom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {ι : Sort.{u3}} {t₁ : ι -> (TopologicalSpace.{u1} α)} {t₂ : TopologicalSpace.{u2} β} {i : ι}, (Continuous.{u1, u2} α β (t₁ i) t₂ f) -> (Continuous.{u1, u2} α β (iInf.{u1, u3} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))) ι t₁) t₂ f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {f : α -> β} {ι : Sort.{u1}} {t₁ : ι -> (TopologicalSpace.{u2} α)} {t₂ : TopologicalSpace.{u3} β} {i : ι}, (Continuous.{u2, u3} α β (t₁ i) t₂ f) -> (Continuous.{u2, u3} α β (iInf.{u2, u1} (TopologicalSpace.{u2} α) (ConditionallyCompleteLattice.toInfSet.{u2} (TopologicalSpace.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u2} α))) ι t₁) t₂ f)
Case conversion may be inaccurate. Consider using '#align continuous_infi_dom continuous_iInf_domₓ'. -/
theorem continuous_iInf_dom {t₁ : ι → tspace α} {t₂ : tspace β} {i : ι} :
    cont (t₁ i) t₂ f → cont (iInf t₁) t₂ f :=
  continuous_le_dom <| iInf_le _ _
#align continuous_infi_dom continuous_iInf_dom

/- warning: continuous_infi_rng -> continuous_iInf_rng is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {ι : Sort.{u3}} {t₁ : TopologicalSpace.{u1} α} {t₂ : ι -> (TopologicalSpace.{u2} β)}, Iff (Continuous.{u1, u2} α β t₁ (iInf.{u2, u3} (TopologicalSpace.{u2} β) (ConditionallyCompleteLattice.toHasInf.{u2} (TopologicalSpace.{u2} β) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.completeLattice.{u2} β))) ι t₂) f) (forall (i : ι), Continuous.{u1, u2} α β t₁ (t₂ i) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {f : α -> β} {ι : Sort.{u1}} {t₁ : TopologicalSpace.{u2} α} {t₂ : ι -> (TopologicalSpace.{u3} β)}, Iff (Continuous.{u2, u3} α β t₁ (iInf.{u3, u1} (TopologicalSpace.{u3} β) (ConditionallyCompleteLattice.toInfSet.{u3} (TopologicalSpace.{u3} β) (CompleteLattice.toConditionallyCompleteLattice.{u3} (TopologicalSpace.{u3} β) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u3} β))) ι t₂) f) (forall (i : ι), Continuous.{u2, u3} α β t₁ (t₂ i) f)
Case conversion may be inaccurate. Consider using '#align continuous_infi_rng continuous_iInf_rngₓ'. -/
theorem continuous_iInf_rng {t₁ : tspace α} {t₂ : ι → tspace β} :
    cont t₁ (iInf t₂) f ↔ ∀ i, cont t₁ (t₂ i) f := by
  simp only [continuous_iff_coinduced_le, le_iInf_iff]
#align continuous_infi_rng continuous_iInf_rng

/- warning: continuous_bot -> continuous_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {t : TopologicalSpace.{u2} β}, Continuous.{u1, u2} α β (Bot.bot.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toHasBot.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))) t f
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {t : TopologicalSpace.{u2} β}, Continuous.{u1, u2} α β (Bot.bot.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toBot.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α))) t f
Case conversion may be inaccurate. Consider using '#align continuous_bot continuous_botₓ'. -/
@[continuity]
theorem continuous_bot {t : tspace β} : cont ⊥ t f :=
  continuous_iff_le_induced.2 <| bot_le
#align continuous_bot continuous_bot

/- warning: continuous_top -> continuous_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {t : TopologicalSpace.{u1} α}, Continuous.{u1, u2} α β t (Top.top.{u2} (TopologicalSpace.{u2} β) (CompleteLattice.toHasTop.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.completeLattice.{u2} β))) f
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {t : TopologicalSpace.{u1} α}, Continuous.{u1, u2} α β t (Top.top.{u2} (TopologicalSpace.{u2} β) (CompleteLattice.toTop.{u2} (TopologicalSpace.{u2} β) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u2} β))) f
Case conversion may be inaccurate. Consider using '#align continuous_top continuous_topₓ'. -/
@[continuity]
theorem continuous_top {t : tspace α} : cont t ⊤ f :=
  continuous_iff_coinduced_le.2 <| le_top
#align continuous_top continuous_top

/- warning: continuous_id_iff_le -> continuous_id_iff_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {t : TopologicalSpace.{u1} α} {t' : TopologicalSpace.{u1} α}, Iff (Continuous.{u1, u1} α α t t' (id.{succ u1} α)) (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toHasLe.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.partialOrder.{u1} α))) t t')
but is expected to have type
  forall {α : Type.{u1}} {t : TopologicalSpace.{u1} α} {t' : TopologicalSpace.{u1} α}, Iff (Continuous.{u1, u1} α α t t' (id.{succ u1} α)) (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toLE.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instPartialOrderTopologicalSpace.{u1} α))) t t')
Case conversion may be inaccurate. Consider using '#align continuous_id_iff_le continuous_id_iff_leₓ'. -/
theorem continuous_id_iff_le {t t' : tspace α} : cont t t' id ↔ t ≤ t' :=
  @continuous_def _ _ t t' id
#align continuous_id_iff_le continuous_id_iff_le

/- warning: continuous_id_of_le -> continuous_id_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {t : TopologicalSpace.{u1} α} {t' : TopologicalSpace.{u1} α}, (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toHasLe.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.partialOrder.{u1} α))) t t') -> (Continuous.{u1, u1} α α t t' (id.{succ u1} α))
but is expected to have type
  forall {α : Type.{u1}} {t : TopologicalSpace.{u1} α} {t' : TopologicalSpace.{u1} α}, (LE.le.{u1} (TopologicalSpace.{u1} α) (Preorder.toLE.{u1} (TopologicalSpace.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instPartialOrderTopologicalSpace.{u1} α))) t t') -> (Continuous.{u1, u1} α α t t' (id.{succ u1} α))
Case conversion may be inaccurate. Consider using '#align continuous_id_of_le continuous_id_of_leₓ'. -/
theorem continuous_id_of_le {t t' : tspace α} (h : t ≤ t') : cont t t' id :=
  continuous_id_iff_le.2 h
#align continuous_id_of_le continuous_id_of_le

/- warning: mem_nhds_induced -> mem_nhds_induced is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [T : TopologicalSpace.{u1} α] (f : β -> α) (a : β) (s : Set.{u2} β), Iff (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) s (nhds.{u2} β (TopologicalSpace.induced.{u2, u1} β α f T) a)) (Exists.{succ u1} (Set.{u1} α) (fun (u : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) u (nhds.{u1} α T (f a))) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) u (nhds.{u1} α T (f a))) => HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Set.preimage.{u2, u1} β α f u) s)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [T : TopologicalSpace.{u1} α] (f : β -> α) (a : β) (s : Set.{u2} β), Iff (Membership.mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (instMembershipSetFilter.{u2} β) s (nhds.{u2} β (TopologicalSpace.induced.{u2, u1} β α f T) a)) (Exists.{succ u1} (Set.{u1} α) (fun (u : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) u (nhds.{u1} α T (f a))) (HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) (Set.preimage.{u2, u1} β α f u) s)))
Case conversion may be inaccurate. Consider using '#align mem_nhds_induced mem_nhds_inducedₓ'. -/
-- 𝓝 in the induced topology
theorem mem_nhds_induced [T : TopologicalSpace α] (f : β → α) (a : β) (s : Set β) :
    s ∈ @nhds β (TopologicalSpace.induced f T) a ↔ ∃ u ∈ 𝓝 (f a), f ⁻¹' u ⊆ s :=
  by
  simp only [mem_nhds_iff, isOpen_induced_iff, exists_prop, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, usub, ⟨v, openv, ueq⟩, au⟩
    exact ⟨v, ⟨v, Set.Subset.refl v, openv, by rwa [← ueq] at au⟩, by rw [ueq] <;> exact usub⟩
  rintro ⟨u, ⟨v, vsubu, openv, amem⟩, finvsub⟩
  exact ⟨f ⁻¹' v, Set.Subset.trans (Set.preimage_mono vsubu) finvsub, ⟨⟨v, openv, rfl⟩, amem⟩⟩
#align mem_nhds_induced mem_nhds_induced

#print nhds_induced /-
theorem nhds_induced [T : TopologicalSpace α] (f : β → α) (a : β) :
    @nhds β (TopologicalSpace.induced f T) a = comap f (𝓝 (f a)) := by ext s;
  rw [mem_nhds_induced, mem_comap]
#align nhds_induced nhds_induced
-/

#print induced_iff_nhds_eq /-
theorem induced_iff_nhds_eq [tα : TopologicalSpace α] [tβ : TopologicalSpace β] (f : β → α) :
    tβ = tα.induced f ↔ ∀ b, 𝓝 b = comap f (𝓝 <| f b) :=
  ⟨fun h a => h.symm ▸ nhds_induced f a, fun h =>
    eq_of_nhds_eq_nhds fun x => by rw [h, nhds_induced]⟩
#align induced_iff_nhds_eq induced_iff_nhds_eq
-/

#print map_nhds_induced_of_surjective /-
theorem map_nhds_induced_of_surjective [T : TopologicalSpace α] {f : β → α} (hf : Surjective f)
    (a : β) : map f (@nhds β (TopologicalSpace.induced f T) a) = 𝓝 (f a) := by
  rw [nhds_induced, map_comap_of_surjective hf]
#align map_nhds_induced_of_surjective map_nhds_induced_of_surjective
-/

end Constructions

section Induced

open TopologicalSpace

variable {α : Type _} {β : Type _}

variable [t : TopologicalSpace β] {f : α → β}

/- warning: is_open_induced_eq -> isOpen_induced_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [t : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α}, Iff (IsOpen.{u1} α (TopologicalSpace.induced.{u1, u2} α β f t) s) (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s (Set.image.{u2, u1} (Set.{u2} β) (Set.{u1} α) (Set.preimage.{u1, u2} α β f) (setOf.{u2} (Set.{u2} β) (fun (s : Set.{u2} β) => IsOpen.{u2} β t s))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [t : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α}, Iff (IsOpen.{u2} α (TopologicalSpace.induced.{u2, u1} α β f t) s) (Membership.mem.{u2, u2} (Set.{u2} α) (Set.{u2} (Set.{u2} α)) (Set.instMembershipSet.{u2} (Set.{u2} α)) s (Set.image.{u1, u2} (Set.{u1} β) (Set.{u2} α) (Set.preimage.{u2, u1} α β f) (setOf.{u1} (Set.{u1} β) (fun (s : Set.{u1} β) => IsOpen.{u1} β t s))))
Case conversion may be inaccurate. Consider using '#align is_open_induced_eq isOpen_induced_eqₓ'. -/
theorem isOpen_induced_eq {s : Set α} :
    is_open[induced f t] s ↔ s ∈ preimage f '' { s | IsOpen s } :=
  Iff.rfl
#align is_open_induced_eq isOpen_induced_eq

#print isOpen_induced /-
theorem isOpen_induced {s : Set β} (h : IsOpen s) : is_open[induced f t] (f ⁻¹' s) :=
  ⟨s, h, rfl⟩
#align is_open_induced isOpen_induced
-/

#print map_nhds_induced_eq /-
theorem map_nhds_induced_eq (a : α) : map f (@nhds α (induced f t) a) = 𝓝[range f] f a := by
  rw [nhds_induced, Filter.map_comap, nhdsWithin]
#align map_nhds_induced_eq map_nhds_induced_eq
-/

#print map_nhds_induced_of_mem /-
theorem map_nhds_induced_of_mem {a : α} (h : range f ∈ 𝓝 (f a)) :
    map f (@nhds α (induced f t) a) = 𝓝 (f a) := by rw [nhds_induced, Filter.map_comap_of_mem h]
#align map_nhds_induced_of_mem map_nhds_induced_of_mem
-/

#print closure_induced /-
theorem closure_induced [t : TopologicalSpace β] {f : α → β} {a : α} {s : Set α} :
    a ∈ @closure α (TopologicalSpace.induced f t) s ↔ f a ∈ closure (f '' s) := by
  simp only [mem_closure_iff_frequently, nhds_induced, frequently_comap, mem_image, and_comm']
#align closure_induced closure_induced
-/

#print isClosed_induced_iff' /-
theorem isClosed_induced_iff' [t : TopologicalSpace β] {f : α → β} {s : Set α} :
    is_closed[t.induced f] s ↔ ∀ a, f a ∈ closure (f '' s) → a ∈ s := by
  simp only [← closure_subset_iff_isClosed, subset_def, closure_induced]
#align is_closed_induced_iff' isClosed_induced_iff'
-/

end Induced

section Sierpinski

variable {α : Type _} [TopologicalSpace α]

#print isOpen_singleton_true /-
@[simp]
theorem isOpen_singleton_true : IsOpen ({True} : Set Prop) :=
  TopologicalSpace.GenerateOpen.basic _ (mem_singleton _)
#align is_open_singleton_true isOpen_singleton_true
-/

#print nhds_true /-
@[simp]
theorem nhds_true : 𝓝 True = pure True :=
  le_antisymm (le_pure_iff.2 <| isOpen_singleton_true.mem_nhds <| mem_singleton _) (pure_le_nhds _)
#align nhds_true nhds_true
-/

/- warning: nhds_false -> nhds_false is a dubious translation:
lean 3 declaration is
  Eq.{1} (Filter.{0} Prop) (nhds.{0} Prop sierpinskiSpace False) (Top.top.{0} (Filter.{0} Prop) (Filter.hasTop.{0} Prop))
but is expected to have type
  Eq.{1} (Filter.{0} Prop) (nhds.{0} Prop sierpinskiSpace False) (Top.top.{0} (Filter.{0} Prop) (Filter.instTopFilter.{0} Prop))
Case conversion may be inaccurate. Consider using '#align nhds_false nhds_falseₓ'. -/
@[simp]
theorem nhds_false : 𝓝 False = ⊤ :=
  TopologicalSpace.nhds_generateFrom.trans <| by simp [@and_comm (_ ∈ _)]
#align nhds_false nhds_false

#print continuous_Prop /-
theorem continuous_Prop {p : α → Prop} : Continuous p ↔ IsOpen { x | p x } :=
  ⟨fun h : Continuous p =>
    by
    have : IsOpen (p ⁻¹' {True}) := isOpen_singleton_true.Preimage h
    simpa [preimage, eq_true_iff] using this, fun h : IsOpen { x | p x } =>
    continuous_generateFrom fun s (hs : s = {True}) => by simp [hs, preimage, eq_true_iff, h]⟩
#align continuous_Prop continuous_Prop
-/

#print isOpen_iff_continuous_mem /-
theorem isOpen_iff_continuous_mem {s : Set α} : IsOpen s ↔ Continuous fun x => x ∈ s :=
  continuous_Prop.symm
#align is_open_iff_continuous_mem isOpen_iff_continuous_mem
-/

end Sierpinski

section iInf

variable {α : Type u} {ι : Sort v}

/- warning: generate_from_union -> generateFrom_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a₁ : Set.{u1} (Set.{u1} α)) (a₂ : Set.{u1} (Set.{u1} α)), Eq.{succ u1} (TopologicalSpace.{u1} α) (TopologicalSpace.generateFrom.{u1} α (Union.union.{u1} (Set.{u1} (Set.{u1} α)) (Set.hasUnion.{u1} (Set.{u1} α)) a₁ a₂)) (Inf.inf.{u1} (TopologicalSpace.{u1} α) (SemilatticeInf.toHasInf.{u1} (TopologicalSpace.{u1} α) (Lattice.toSemilatticeInf.{u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))))) (TopologicalSpace.generateFrom.{u1} α a₁) (TopologicalSpace.generateFrom.{u1} α a₂))
but is expected to have type
  forall {α : Type.{u1}} (a₁ : Set.{u1} (Set.{u1} α)) (a₂ : Set.{u1} (Set.{u1} α)), Eq.{succ u1} (TopologicalSpace.{u1} α) (TopologicalSpace.generateFrom.{u1} α (Union.union.{u1} (Set.{u1} (Set.{u1} α)) (Set.instUnionSet.{u1} (Set.{u1} α)) a₁ a₂)) (Inf.inf.{u1} (TopologicalSpace.{u1} α) (Lattice.toInf.{u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α)))) (TopologicalSpace.generateFrom.{u1} α a₁) (TopologicalSpace.generateFrom.{u1} α a₂))
Case conversion may be inaccurate. Consider using '#align generate_from_union generateFrom_unionₓ'. -/
theorem generateFrom_union (a₁ a₂ : Set (Set α)) :
    TopologicalSpace.generateFrom (a₁ ∪ a₂) =
      TopologicalSpace.generateFrom a₁ ⊓ TopologicalSpace.generateFrom a₂ :=
  (TopologicalSpace.gc_generateFrom α).u_inf
#align generate_from_union generateFrom_union

/- warning: set_of_is_open_sup -> setOf_isOpen_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (t₁ : TopologicalSpace.{u1} α) (t₂ : TopologicalSpace.{u1} α), Eq.{succ u1} (Set.{u1} (Set.{u1} α)) (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => IsOpen.{u1} α (Sup.sup.{u1} (TopologicalSpace.{u1} α) (SemilatticeSup.toHasSup.{u1} (TopologicalSpace.{u1} α) (Lattice.toSemilatticeSup.{u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))))) t₁ t₂) s)) (Inter.inter.{u1} (Set.{u1} (Set.{u1} α)) (Set.hasInter.{u1} (Set.{u1} α)) (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => IsOpen.{u1} α t₁ s)) (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => IsOpen.{u1} α t₂ s)))
but is expected to have type
  forall {α : Type.{u1}} (t₁ : TopologicalSpace.{u1} α) (t₂ : TopologicalSpace.{u1} α), Eq.{succ u1} (Set.{u1} (Set.{u1} α)) (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => IsOpen.{u1} α (Sup.sup.{u1} (TopologicalSpace.{u1} α) (SemilatticeSup.toSup.{u1} (TopologicalSpace.{u1} α) (Lattice.toSemilatticeSup.{u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α))))) t₁ t₂) s)) (Inter.inter.{u1} (Set.{u1} (Set.{u1} α)) (Set.instInterSet.{u1} (Set.{u1} α)) (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => IsOpen.{u1} α t₁ s)) (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => IsOpen.{u1} α t₂ s)))
Case conversion may be inaccurate. Consider using '#align set_of_is_open_sup setOf_isOpen_supₓ'. -/
theorem setOf_isOpen_sup (t₁ t₂ : TopologicalSpace α) :
    { s | is_open[t₁ ⊔ t₂] s } = { s | is_open[t₁] s } ∩ { s | is_open[t₂] s } :=
  rfl
#align set_of_is_open_sup setOf_isOpen_sup

/- warning: generate_from_Union -> generateFrom_iUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> (Set.{u1} (Set.{u1} α))}, Eq.{succ u1} (TopologicalSpace.{u1} α) (TopologicalSpace.generateFrom.{u1} α (Set.iUnion.{u1, u2} (Set.{u1} α) ι (fun (i : ι) => f i))) (iInf.{u1, u2} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))) ι (fun (i : ι) => TopologicalSpace.generateFrom.{u1} α (f i)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} {f : ι -> (Set.{u1} (Set.{u1} α))}, Eq.{succ u1} (TopologicalSpace.{u1} α) (TopologicalSpace.generateFrom.{u1} α (Set.iUnion.{u1, u2} (Set.{u1} α) ι (fun (i : ι) => f i))) (iInf.{u1, u2} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toInfSet.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α))) ι (fun (i : ι) => TopologicalSpace.generateFrom.{u1} α (f i)))
Case conversion may be inaccurate. Consider using '#align generate_from_Union generateFrom_iUnionₓ'. -/
theorem generateFrom_iUnion {f : ι → Set (Set α)} :
    TopologicalSpace.generateFrom (⋃ i, f i) = ⨅ i, TopologicalSpace.generateFrom (f i) :=
  (TopologicalSpace.gc_generateFrom α).u_iInf
#align generate_from_Union generateFrom_iUnion

/- warning: set_of_is_open_supr -> setOf_isOpen_iSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {t : ι -> (TopologicalSpace.{u1} α)}, Eq.{succ u1} (Set.{u1} (Set.{u1} α)) (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => IsOpen.{u1} α (iSup.{u1, u2} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toHasSup.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))) ι (fun (i : ι) => t i)) s)) (Set.iInter.{u1, u2} (Set.{u1} α) ι (fun (i : ι) => setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => IsOpen.{u1} α (t i) s)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} {t : ι -> (TopologicalSpace.{u1} α)}, Eq.{succ u1} (Set.{u1} (Set.{u1} α)) (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => IsOpen.{u1} α (iSup.{u1, u2} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toSupSet.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α))) ι (fun (i : ι) => t i)) s)) (Set.iInter.{u1, u2} (Set.{u1} α) ι (fun (i : ι) => setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => IsOpen.{u1} α (t i) s)))
Case conversion may be inaccurate. Consider using '#align set_of_is_open_supr setOf_isOpen_iSupₓ'. -/
theorem setOf_isOpen_iSup {t : ι → TopologicalSpace α} :
    { s | is_open[⨆ i, t i] s } = ⋂ i, { s | is_open[t i] s } :=
  (TopologicalSpace.gc_generateFrom α).l_iSup
#align set_of_is_open_supr setOf_isOpen_iSup

/- warning: generate_from_sUnion -> generateFrom_sUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {S : Set.{u1} (Set.{u1} (Set.{u1} α))}, Eq.{succ u1} (TopologicalSpace.{u1} α) (TopologicalSpace.generateFrom.{u1} α (Set.sUnion.{u1} (Set.{u1} α) S)) (iInf.{u1, succ u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))) (Set.{u1} (Set.{u1} α)) (fun (s : Set.{u1} (Set.{u1} α)) => iInf.{u1, 0} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))) (Membership.Mem.{u1, u1} (Set.{u1} (Set.{u1} α)) (Set.{u1} (Set.{u1} (Set.{u1} α))) (Set.hasMem.{u1} (Set.{u1} (Set.{u1} α))) s S) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} (Set.{u1} α)) (Set.{u1} (Set.{u1} (Set.{u1} α))) (Set.hasMem.{u1} (Set.{u1} (Set.{u1} α))) s S) => TopologicalSpace.generateFrom.{u1} α s)))
but is expected to have type
  forall {α : Type.{u1}} {S : Set.{u1} (Set.{u1} (Set.{u1} α))}, Eq.{succ u1} (TopologicalSpace.{u1} α) (TopologicalSpace.generateFrom.{u1} α (Set.sUnion.{u1} (Set.{u1} α) S)) (iInf.{u1, succ u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toInfSet.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α))) (Set.{u1} (Set.{u1} α)) (fun (s : Set.{u1} (Set.{u1} α)) => iInf.{u1, 0} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toInfSet.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α))) (Membership.mem.{u1, u1} (Set.{u1} (Set.{u1} α)) (Set.{u1} (Set.{u1} (Set.{u1} α))) (Set.instMembershipSet.{u1} (Set.{u1} (Set.{u1} α))) s S) (fun (H : Membership.mem.{u1, u1} (Set.{u1} (Set.{u1} α)) (Set.{u1} (Set.{u1} (Set.{u1} α))) (Set.instMembershipSet.{u1} (Set.{u1} (Set.{u1} α))) s S) => TopologicalSpace.generateFrom.{u1} α s)))
Case conversion may be inaccurate. Consider using '#align generate_from_sUnion generateFrom_sUnionₓ'. -/
theorem generateFrom_sUnion {S : Set (Set (Set α))} :
    TopologicalSpace.generateFrom (⋃₀ S) = ⨅ s ∈ S, TopologicalSpace.generateFrom s :=
  (TopologicalSpace.gc_generateFrom α).u_sInf
#align generate_from_sUnion generateFrom_sUnion

/- warning: set_of_is_open_Sup -> setOf_isOpen_sSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {T : Set.{u1} (TopologicalSpace.{u1} α)}, Eq.{succ u1} (Set.{u1} (Set.{u1} α)) (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => IsOpen.{u1} α (SupSet.sSup.{u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toHasSup.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))) T) s)) (Set.iInter.{u1, succ u1} (Set.{u1} α) (TopologicalSpace.{u1} α) (fun (t : TopologicalSpace.{u1} α) => Set.iInter.{u1, 0} (Set.{u1} α) (Membership.Mem.{u1, u1} (TopologicalSpace.{u1} α) (Set.{u1} (TopologicalSpace.{u1} α)) (Set.hasMem.{u1} (TopologicalSpace.{u1} α)) t T) (fun (H : Membership.Mem.{u1, u1} (TopologicalSpace.{u1} α) (Set.{u1} (TopologicalSpace.{u1} α)) (Set.hasMem.{u1} (TopologicalSpace.{u1} α)) t T) => setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => IsOpen.{u1} α t s))))
but is expected to have type
  forall {α : Type.{u1}} {T : Set.{u1} (TopologicalSpace.{u1} α)}, Eq.{succ u1} (Set.{u1} (Set.{u1} α)) (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => IsOpen.{u1} α (SupSet.sSup.{u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toSupSet.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α))) T) s)) (Set.iInter.{u1, succ u1} (Set.{u1} α) (TopologicalSpace.{u1} α) (fun (t : TopologicalSpace.{u1} α) => Set.iInter.{u1, 0} (Set.{u1} α) (Membership.mem.{u1, u1} (TopologicalSpace.{u1} α) (Set.{u1} (TopologicalSpace.{u1} α)) (Set.instMembershipSet.{u1} (TopologicalSpace.{u1} α)) t T) (fun (H : Membership.mem.{u1, u1} (TopologicalSpace.{u1} α) (Set.{u1} (TopologicalSpace.{u1} α)) (Set.instMembershipSet.{u1} (TopologicalSpace.{u1} α)) t T) => setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => IsOpen.{u1} α t s))))
Case conversion may be inaccurate. Consider using '#align set_of_is_open_Sup setOf_isOpen_sSupₓ'. -/
theorem setOf_isOpen_sSup {T : Set (TopologicalSpace α)} :
    { s | is_open[sSup T] s } = ⋂ t ∈ T, { s | is_open[t] s } :=
  (TopologicalSpace.gc_generateFrom α).l_sSup
#align set_of_is_open_Sup setOf_isOpen_sSup

/- warning: generate_from_union_is_open -> generateFrom_union_isOpen is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : TopologicalSpace.{u1} α) (b : TopologicalSpace.{u1} α), Eq.{succ u1} (TopologicalSpace.{u1} α) (TopologicalSpace.generateFrom.{u1} α (Union.union.{u1} (Set.{u1} (Set.{u1} α)) (Set.hasUnion.{u1} (Set.{u1} α)) (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => IsOpen.{u1} α a s)) (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => IsOpen.{u1} α b s)))) (Inf.inf.{u1} (TopologicalSpace.{u1} α) (SemilatticeInf.toHasInf.{u1} (TopologicalSpace.{u1} α) (Lattice.toSemilatticeInf.{u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))))) a b)
but is expected to have type
  forall {α : Type.{u1}} (a : TopologicalSpace.{u1} α) (b : TopologicalSpace.{u1} α), Eq.{succ u1} (TopologicalSpace.{u1} α) (TopologicalSpace.generateFrom.{u1} α (Union.union.{u1} (Set.{u1} (Set.{u1} α)) (Set.instUnionSet.{u1} (Set.{u1} α)) (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => IsOpen.{u1} α a s)) (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => IsOpen.{u1} α b s)))) (Inf.inf.{u1} (TopologicalSpace.{u1} α) (Lattice.toInf.{u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α)))) a b)
Case conversion may be inaccurate. Consider using '#align generate_from_union_is_open generateFrom_union_isOpenₓ'. -/
theorem generateFrom_union_isOpen (a b : TopologicalSpace α) :
    TopologicalSpace.generateFrom ({ s | is_open[a] s } ∪ { s | is_open[b] s }) = a ⊓ b :=
  (TopologicalSpace.gciGenerateFrom α).u_inf_l a b
#align generate_from_union_is_open generateFrom_union_isOpen

/- warning: generate_from_Union_is_open -> generateFrom_iUnion_isOpen is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} (f : ι -> (TopologicalSpace.{u1} α)), Eq.{succ u1} (TopologicalSpace.{u1} α) (TopologicalSpace.generateFrom.{u1} α (Set.iUnion.{u1, u2} (Set.{u1} α) ι (fun (i : ι) => setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => IsOpen.{u1} α (f i) s)))) (iInf.{u1, u2} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))) ι (fun (i : ι) => f i))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} (f : ι -> (TopologicalSpace.{u1} α)), Eq.{succ u1} (TopologicalSpace.{u1} α) (TopologicalSpace.generateFrom.{u1} α (Set.iUnion.{u1, u2} (Set.{u1} α) ι (fun (i : ι) => setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => IsOpen.{u1} α (f i) s)))) (iInf.{u1, u2} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toInfSet.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α))) ι (fun (i : ι) => f i))
Case conversion may be inaccurate. Consider using '#align generate_from_Union_is_open generateFrom_iUnion_isOpenₓ'. -/
theorem generateFrom_iUnion_isOpen (f : ι → TopologicalSpace α) :
    TopologicalSpace.generateFrom (⋃ i, { s | is_open[f i] s }) = ⨅ i, f i :=
  (TopologicalSpace.gciGenerateFrom α).u_iInf_l f
#align generate_from_Union_is_open generateFrom_iUnion_isOpen

/- warning: generate_from_inter -> generateFrom_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : TopologicalSpace.{u1} α) (b : TopologicalSpace.{u1} α), Eq.{succ u1} (TopologicalSpace.{u1} α) (TopologicalSpace.generateFrom.{u1} α (Inter.inter.{u1} (Set.{u1} (Set.{u1} α)) (Set.hasInter.{u1} (Set.{u1} α)) (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => IsOpen.{u1} α a s)) (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => IsOpen.{u1} α b s)))) (Sup.sup.{u1} (TopologicalSpace.{u1} α) (SemilatticeSup.toHasSup.{u1} (TopologicalSpace.{u1} α) (Lattice.toSemilatticeSup.{u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))))) a b)
but is expected to have type
  forall {α : Type.{u1}} (a : TopologicalSpace.{u1} α) (b : TopologicalSpace.{u1} α), Eq.{succ u1} (TopologicalSpace.{u1} α) (TopologicalSpace.generateFrom.{u1} α (Inter.inter.{u1} (Set.{u1} (Set.{u1} α)) (Set.instInterSet.{u1} (Set.{u1} α)) (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => IsOpen.{u1} α a s)) (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => IsOpen.{u1} α b s)))) (Sup.sup.{u1} (TopologicalSpace.{u1} α) (SemilatticeSup.toSup.{u1} (TopologicalSpace.{u1} α) (Lattice.toSemilatticeSup.{u1} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α))))) a b)
Case conversion may be inaccurate. Consider using '#align generate_from_inter generateFrom_interₓ'. -/
theorem generateFrom_inter (a b : TopologicalSpace α) :
    TopologicalSpace.generateFrom ({ s | is_open[a] s } ∩ { s | is_open[b] s }) = a ⊔ b :=
  (TopologicalSpace.gciGenerateFrom α).u_sup_l a b
#align generate_from_inter generateFrom_inter

/- warning: generate_from_Inter -> generateFrom_iInter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} (f : ι -> (TopologicalSpace.{u1} α)), Eq.{succ u1} (TopologicalSpace.{u1} α) (TopologicalSpace.generateFrom.{u1} α (Set.iInter.{u1, u2} (Set.{u1} α) ι (fun (i : ι) => setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => IsOpen.{u1} α (f i) s)))) (iSup.{u1, u2} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toHasSup.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))) ι (fun (i : ι) => f i))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} (f : ι -> (TopologicalSpace.{u1} α)), Eq.{succ u1} (TopologicalSpace.{u1} α) (TopologicalSpace.generateFrom.{u1} α (Set.iInter.{u1, u2} (Set.{u1} α) ι (fun (i : ι) => setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => IsOpen.{u1} α (f i) s)))) (iSup.{u1, u2} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toSupSet.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α))) ι (fun (i : ι) => f i))
Case conversion may be inaccurate. Consider using '#align generate_from_Inter generateFrom_iInterₓ'. -/
theorem generateFrom_iInter (f : ι → TopologicalSpace α) :
    TopologicalSpace.generateFrom (⋂ i, { s | is_open[f i] s }) = ⨆ i, f i :=
  (TopologicalSpace.gciGenerateFrom α).u_iSup_l f
#align generate_from_Inter generateFrom_iInter

/- warning: generate_from_Inter_of_generate_from_eq_self -> generateFrom_iInter_of_generateFrom_eq_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} (f : ι -> (Set.{u1} (Set.{u1} α))), (forall (i : ι), Eq.{succ u1} (Set.{u1} (Set.{u1} α)) (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => IsOpen.{u1} α (TopologicalSpace.generateFrom.{u1} α (f i)) s)) (f i)) -> (Eq.{succ u1} (TopologicalSpace.{u1} α) (TopologicalSpace.generateFrom.{u1} α (Set.iInter.{u1, u2} (Set.{u1} α) ι (fun (i : ι) => f i))) (iSup.{u1, u2} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toHasSup.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))) ι (fun (i : ι) => TopologicalSpace.generateFrom.{u1} α (f i))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} (f : ι -> (Set.{u1} (Set.{u1} α))), (forall (i : ι), Eq.{succ u1} (Set.{u1} (Set.{u1} α)) (setOf.{u1} (Set.{u1} α) (fun (s : Set.{u1} α) => IsOpen.{u1} α (TopologicalSpace.generateFrom.{u1} α (f i)) s)) (f i)) -> (Eq.{succ u1} (TopologicalSpace.{u1} α) (TopologicalSpace.generateFrom.{u1} α (Set.iInter.{u1, u2} (Set.{u1} α) ι (fun (i : ι) => f i))) (iSup.{u1, u2} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toSupSet.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α))) ι (fun (i : ι) => TopologicalSpace.generateFrom.{u1} α (f i))))
Case conversion may be inaccurate. Consider using '#align generate_from_Inter_of_generate_from_eq_self generateFrom_iInter_of_generateFrom_eq_selfₓ'. -/
theorem generateFrom_iInter_of_generateFrom_eq_self (f : ι → Set (Set α))
    (hf : ∀ i, { s | is_open[TopologicalSpace.generateFrom (f i)] s } = f i) :
    TopologicalSpace.generateFrom (⋂ i, f i) = ⨆ i, TopologicalSpace.generateFrom (f i) :=
  (TopologicalSpace.gciGenerateFrom α).u_iSup_of_lu_eq_self f hf
#align generate_from_Inter_of_generate_from_eq_self generateFrom_iInter_of_generateFrom_eq_self

variable {t : ι → TopologicalSpace α}

/- warning: is_open_supr_iff -> isOpen_iSup_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {t : ι -> (TopologicalSpace.{u1} α)} {s : Set.{u1} α}, Iff (IsOpen.{u1} α (iSup.{u1, u2} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toHasSup.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))) ι (fun (i : ι) => t i)) s) (forall (i : ι), IsOpen.{u1} α (t i) s)
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} {t : ι -> (TopologicalSpace.{u1} α)} {s : Set.{u1} α}, Iff (IsOpen.{u1} α (iSup.{u1, u2} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toSupSet.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α))) ι (fun (i : ι) => t i)) s) (forall (i : ι), IsOpen.{u1} α (t i) s)
Case conversion may be inaccurate. Consider using '#align is_open_supr_iff isOpen_iSup_iffₓ'. -/
theorem isOpen_iSup_iff {s : Set α} : is_open[⨆ i, t i] s ↔ ∀ i, is_open[t i] s :=
  show s ∈ setOf is_open[iSup t] ↔ s ∈ { x : Set α | ∀ i : ι, is_open[t i] x } by
    simp [setOf_isOpen_iSup]
#align is_open_supr_iff isOpen_iSup_iff

/- warning: is_closed_supr_iff -> isClosed_iSup_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {t : ι -> (TopologicalSpace.{u1} α)} {s : Set.{u1} α}, Iff (IsClosed.{u1} α (iSup.{u1, u2} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toHasSup.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α))) ι (fun (i : ι) => t i)) s) (forall (i : ι), IsClosed.{u1} α (t i) s)
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} {t : ι -> (TopologicalSpace.{u1} α)} {s : Set.{u1} α}, Iff (IsClosed.{u1} α (iSup.{u1, u2} (TopologicalSpace.{u1} α) (ConditionallyCompleteLattice.toSupSet.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α))) ι (fun (i : ι) => t i)) s) (forall (i : ι), IsClosed.{u1} α (t i) s)
Case conversion may be inaccurate. Consider using '#align is_closed_supr_iff isClosed_iSup_iffₓ'. -/
theorem isClosed_iSup_iff {s : Set α} : is_closed[⨆ i, t i] s ↔ ∀ i, is_closed[t i] s := by
  simp [← isOpen_compl_iff, isOpen_iSup_iff]
#align is_closed_supr_iff isClosed_iSup_iff

end iInf

