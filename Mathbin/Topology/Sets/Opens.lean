/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn

! This file was ported from Lean 3 source module topology.sets.opens
! leanprover-community/mathlib commit 28aa996fc6fb4317f0083c4e6daf79878d81be33
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Hom.CompleteLattice
import Mathbin.Topology.Bases
import Mathbin.Topology.Homeomorph
import Mathbin.Topology.ContinuousFunction.Basic
import Mathbin.Order.CompactlyGenerated
import Mathbin.Tactic.AutoCases

/-!
# Open sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Summary

We define the subtype of open sets in a topological space.

## Main Definitions

### Bundled open sets

- `opens α` is the type of open subsets of a topological space `α`.
- `opens.is_basis` is a predicate saying that a set of `opens`s form a topological basis.
- `opens.comap`: preimage of an open set under a continuous map as a `frame_hom`.
- `homeomorph.opens_congr`: order-preserving equivalence between open sets in the domain and the
  codomain of a homeomorphism.

### Bundled open neighborhoods

- `open_nhds_of x` is the type of open subsets of a topological space `α` containing `x : α`.
- `open_nhds_of.comap f x U` is the preimage of open neighborhood `U` of `f x` under `f : C(α, β)`.

## Main results

We define order structures on both `opens α` (`complete_structure`, `frame`) and `open_nhds_of x`
(`order_top`, `distrib_lattice`).
-/


open Filter Function Order Set

open Topology

variable {ι α β γ : Type _} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

namespace TopologicalSpace

variable (α)

#print TopologicalSpace.Opens /-
/-- The type of open subsets of a topological space. -/
structure Opens where
  carrier : Set α
  is_open' : IsOpen carrier
#align topological_space.opens TopologicalSpace.Opens
-/

variable {α}

namespace Opens

instance : SetLike (Opens α) α where
  coe := Opens.carrier
  coe_injective' := fun ⟨_, _⟩ ⟨_, _⟩ _ => by congr <;> assumption

instance : CanLift (Set α) (Opens α) coe IsOpen :=
  ⟨fun s h => ⟨⟨s, h⟩, rfl⟩⟩

#print TopologicalSpace.Opens.forall /-
theorem forall {p : Opens α → Prop} : (∀ U, p U) ↔ ∀ (U : Set α) (hU : IsOpen U), p ⟨U, hU⟩ :=
  ⟨fun h _ _ => h _, fun h ⟨U, hU⟩ => h _ _⟩
#align topological_space.opens.forall TopologicalSpace.Opens.forall
-/

#print TopologicalSpace.Opens.carrier_eq_coe /-
@[simp]
theorem carrier_eq_coe (U : Opens α) : U.1 = ↑U :=
  rfl
#align topological_space.opens.carrier_eq_coe TopologicalSpace.Opens.carrier_eq_coe
-/

#print TopologicalSpace.Opens.coe_mk /-
/-- the coercion `opens α → set α` applied to a pair is the same as taking the first component -/
@[simp]
theorem coe_mk {U : Set α} {hU : IsOpen U} : ↑(⟨U, hU⟩ : Opens α) = U :=
  rfl
#align topological_space.opens.coe_mk TopologicalSpace.Opens.coe_mk
-/

#print TopologicalSpace.Opens.mem_mk /-
@[simp]
theorem mem_mk {x : α} {U : Set α} {h : IsOpen U} :
    @Membership.Mem _ (Opens α) _ x ⟨U, h⟩ ↔ x ∈ U :=
  Iff.rfl
#align topological_space.opens.mem_mk TopologicalSpace.Opens.mem_mk
-/

#print TopologicalSpace.Opens.nonempty_coeSort /-
-- todo: make it `simp` for a `set_like`?
@[simp]
protected theorem nonempty_coeSort {U : Opens α} : Nonempty U ↔ (U : Set α).Nonempty :=
  Set.nonempty_coe_sort
#align topological_space.opens.nonempty_coe_sort TopologicalSpace.Opens.nonempty_coeSort
-/

#print TopologicalSpace.Opens.ext /-
@[ext]
theorem ext {U V : Opens α} (h : (U : Set α) = V) : U = V :=
  SetLike.coe_injective h
#align topological_space.opens.ext TopologicalSpace.Opens.ext
-/

#print TopologicalSpace.Opens.coe_inj /-
@[simp]
theorem coe_inj {U V : Opens α} : (U : Set α) = V ↔ U = V :=
  SetLike.ext'_iff.symm
#align topological_space.opens.coe_inj TopologicalSpace.Opens.coe_inj
-/

#print TopologicalSpace.Opens.isOpen /-
protected theorem isOpen (U : Opens α) : IsOpen (U : Set α) :=
  U.is_open'
#align topological_space.opens.is_open TopologicalSpace.Opens.isOpen
-/

#print TopologicalSpace.Opens.mk_coe /-
@[simp]
theorem mk_coe (U : Opens α) : mk (↑U) U.IsOpen = U :=
  by
  cases U
  rfl
#align topological_space.opens.mk_coe TopologicalSpace.Opens.mk_coe
-/

#print TopologicalSpace.Opens.Simps.coe /-
/-- See Note [custom simps projection]. -/
def Simps.coe (U : Opens α) : Set α :=
  U
#align topological_space.opens.simps.coe TopologicalSpace.Opens.Simps.coe
-/

initialize_simps_projections Opens (carrier → coe)

#print TopologicalSpace.Opens.interior /-
/-- The interior of a set, as an element of `opens`. -/
def interior (s : Set α) : Opens α :=
  ⟨interior s, isOpen_interior⟩
#align topological_space.opens.interior TopologicalSpace.Opens.interior
-/

/- warning: topological_space.opens.gc -> TopologicalSpace.Opens.gc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α], GaloisConnection.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (SetLike.partialOrder.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1))) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1))))) (TopologicalSpace.Opens.interior.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α], GaloisConnection.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (SetLike.instPartialOrder.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u1} α _inst_1))) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (SetLike.coe.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u1} α _inst_1)) (TopologicalSpace.Opens.interior.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align topological_space.opens.gc TopologicalSpace.Opens.gcₓ'. -/
theorem gc : GaloisConnection (coe : Opens α → Set α) interior := fun U s =>
  ⟨fun h => interior_maximal h U.IsOpen, fun h => le_trans h interior_subset⟩
#align topological_space.opens.gc TopologicalSpace.Opens.gc

/- warning: topological_space.opens.gi -> TopologicalSpace.Opens.gi is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α], GaloisCoinsertion.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (SetLike.partialOrder.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1))) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1))))) (TopologicalSpace.Opens.interior.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α], GaloisCoinsertion.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (SetLike.instPartialOrder.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u1} α _inst_1))) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (SetLike.coe.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u1} α _inst_1)) (TopologicalSpace.Opens.interior.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align topological_space.opens.gi TopologicalSpace.Opens.giₓ'. -/
/-- The galois coinsertion between sets and opens. -/
def gi : GaloisCoinsertion coe (@interior α _)
    where
  choice s hs := ⟨s, interior_eq_iff_isOpen.mp <| le_antisymm interior_subset hs⟩
  gc := gc
  u_l_le _ := interior_subset
  choice_eq s hs := le_antisymm hs interior_subset
#align topological_space.opens.gi TopologicalSpace.Opens.gi

instance : CompleteLattice (Opens α) :=
  CompleteLattice.copy (GaloisCoinsertion.liftCompleteLattice gi)
    (-- le
    fun U V => (U : Set α) ⊆ V)
    rfl-- top
    ⟨univ, isOpen_univ⟩
    (ext interior_univ.symm)-- bot
    ⟨∅, isOpen_empty⟩
    rfl
    (-- sup
    fun U V => ⟨↑U ∪ ↑V, U.2.union V.2⟩)
    rfl
    (-- inf
    fun U V => ⟨↑U ∩ ↑V, U.2.inter V.2⟩)
    (funext₂ fun U V => ext (U.2.inter V.2).interior_eq.symm)
    (-- Sup
    fun S => ⟨⋃ s ∈ S, ↑s, isOpen_bunionᵢ fun s _ => s.2⟩)
    (funext fun S => ext supₛ_image.symm)-- Inf
    _
    rfl

/- warning: topological_space.opens.mk_inf_mk -> TopologicalSpace.Opens.mk_inf_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {U : Set.{u1} α} {V : Set.{u1} α} {hU : IsOpen.{u1} α _inst_1 U} {hV : IsOpen.{u1} α _inst_1 V}, Eq.{succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (HasInf.inf.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (SemilatticeInf.toHasInf.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Lattice.toSemilatticeInf.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1))))) (TopologicalSpace.Opens.mk.{u1} α _inst_1 U hU) (TopologicalSpace.Opens.mk.{u1} α _inst_1 V hV)) (TopologicalSpace.Opens.mk.{u1} α _inst_1 (HasInf.inf.{u1} (Set.{u1} α) (SemilatticeInf.toHasInf.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Set.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))))) U V) (IsOpen.inter.{u1} α U V _inst_1 hU hV))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {U : Set.{u1} α} {V : Set.{u1} α} {hU : IsOpen.{u1} α _inst_1 U} {hV : IsOpen.{u1} α _inst_1 V}, Eq.{succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (HasInf.inf.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Lattice.toHasInf.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1)))) (TopologicalSpace.Opens.mk.{u1} α _inst_1 U hU) (TopologicalSpace.Opens.mk.{u1} α _inst_1 V hV)) (TopologicalSpace.Opens.mk.{u1} α _inst_1 (HasInf.inf.{u1} (Set.{u1} α) (Lattice.toHasInf.{u1} (Set.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Set.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) U V) (IsOpen.inter.{u1} α U V _inst_1 hU hV))
Case conversion may be inaccurate. Consider using '#align topological_space.opens.mk_inf_mk TopologicalSpace.Opens.mk_inf_mkₓ'. -/
@[simp]
theorem mk_inf_mk {U V : Set α} {hU : IsOpen U} {hV : IsOpen V} :
    (⟨U, hU⟩ ⊓ ⟨V, hV⟩ : Opens α) = ⟨U ⊓ V, IsOpen.inter hU hV⟩ :=
  rfl
#align topological_space.opens.mk_inf_mk TopologicalSpace.Opens.mk_inf_mk

/- warning: topological_space.opens.coe_inf -> TopologicalSpace.Opens.coe_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : TopologicalSpace.Opens.{u1} α _inst_1) (t : TopologicalSpace.Opens.{u1} α _inst_1), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)))) (HasInf.inf.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (SemilatticeInf.toHasInf.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Lattice.toSemilatticeInf.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1))))) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)))) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : TopologicalSpace.Opens.{u1} α _inst_1) (t : TopologicalSpace.Opens.{u1} α _inst_1), Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u1} α _inst_1) (HasInf.inf.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Lattice.toHasInf.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1)))) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u1} α _inst_1) s) (SetLike.coe.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u1} α _inst_1) t))
Case conversion may be inaccurate. Consider using '#align topological_space.opens.coe_inf TopologicalSpace.Opens.coe_infₓ'. -/
@[simp, norm_cast]
theorem coe_inf (s t : Opens α) : (↑(s ⊓ t) : Set α) = s ∩ t :=
  rfl
#align topological_space.opens.coe_inf TopologicalSpace.Opens.coe_inf

/- warning: topological_space.opens.coe_sup -> TopologicalSpace.Opens.coe_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : TopologicalSpace.Opens.{u1} α _inst_1) (t : TopologicalSpace.Opens.{u1} α _inst_1), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)))) (HasSup.sup.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (SemilatticeSup.toHasSup.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Lattice.toSemilatticeSup.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1))))) s t)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)))) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : TopologicalSpace.Opens.{u1} α _inst_1) (t : TopologicalSpace.Opens.{u1} α _inst_1), Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u1} α _inst_1) (HasSup.sup.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (SemilatticeSup.toHasSup.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Lattice.toSemilatticeSup.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1))))) s t)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u1} α _inst_1) s) (SetLike.coe.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u1} α _inst_1) t))
Case conversion may be inaccurate. Consider using '#align topological_space.opens.coe_sup TopologicalSpace.Opens.coe_supₓ'. -/
@[simp, norm_cast]
theorem coe_sup (s t : Opens α) : (↑(s ⊔ t) : Set α) = s ∪ t :=
  rfl
#align topological_space.opens.coe_sup TopologicalSpace.Opens.coe_sup

/- warning: topological_space.opens.coe_bot -> TopologicalSpace.Opens.coe_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α], Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)))) (Bot.bot.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteLattice.toHasBot.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1)))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α], Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u1} α _inst_1) (Bot.bot.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteLattice.toBot.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1)))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))
Case conversion may be inaccurate. Consider using '#align topological_space.opens.coe_bot TopologicalSpace.Opens.coe_botₓ'. -/
@[simp, norm_cast]
theorem coe_bot : ((⊥ : Opens α) : Set α) = ∅ :=
  rfl
#align topological_space.opens.coe_bot TopologicalSpace.Opens.coe_bot

/- warning: topological_space.opens.coe_top -> TopologicalSpace.Opens.coe_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α], Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)))) (Top.top.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteLattice.toHasTop.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1)))) (Set.univ.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α], Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u1} α _inst_1) (Top.top.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteLattice.toTop.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1)))) (Set.univ.{u1} α)
Case conversion may be inaccurate. Consider using '#align topological_space.opens.coe_top TopologicalSpace.Opens.coe_topₓ'. -/
@[simp, norm_cast]
theorem coe_top : ((⊤ : Opens α) : Set α) = Set.univ :=
  rfl
#align topological_space.opens.coe_top TopologicalSpace.Opens.coe_top

/- warning: topological_space.opens.coe_Sup -> TopologicalSpace.Opens.coe_supₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {S : Set.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)}, Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)))) (SupSet.supₛ.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (ConditionallyCompleteLattice.toHasSup.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1))) S)) (Set.unionᵢ.{u1, succ u1} α (TopologicalSpace.Opens.{u1} α _inst_1) (fun (i : TopologicalSpace.Opens.{u1} α _inst_1) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)) (Set.hasMem.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)) i S) (fun (H : Membership.Mem.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)) (Set.hasMem.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)) i S) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)))) i)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {S : Set.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)}, Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u1} α _inst_1) (SupSet.supₛ.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (ConditionallyCompleteLattice.toSupSet.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1))) S)) (Set.unionᵢ.{u1, succ u1} α (TopologicalSpace.Opens.{u1} α _inst_1) (fun (i : TopologicalSpace.Opens.{u1} α _inst_1) => Set.unionᵢ.{u1, 0} α (Membership.mem.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)) (Set.instMembershipSet.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)) i S) (fun (H : Membership.mem.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)) (Set.instMembershipSet.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)) i S) => SetLike.coe.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u1} α _inst_1) i)))
Case conversion may be inaccurate. Consider using '#align topological_space.opens.coe_Sup TopologicalSpace.Opens.coe_supₛₓ'. -/
@[simp, norm_cast]
theorem coe_supₛ {S : Set (Opens α)} : (↑(supₛ S) : Set α) = ⋃ i ∈ S, ↑i :=
  rfl
#align topological_space.opens.coe_Sup TopologicalSpace.Opens.coe_supₛ

/- warning: topological_space.opens.coe_finset_sup -> TopologicalSpace.Opens.coe_finset_sup is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] (f : ι -> (TopologicalSpace.Opens.{u2} α _inst_1)) (s : Finset.{u1} ι), Eq.{succ u2} (Set.{u2} α) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (TopologicalSpace.Opens.{u2} α _inst_1) (Set.{u2} α) (HasLiftT.mk.{succ u2, succ u2} (TopologicalSpace.Opens.{u2} α _inst_1) (Set.{u2} α) (CoeTCₓ.coe.{succ u2, succ u2} (TopologicalSpace.Opens.{u2} α _inst_1) (Set.{u2} α) (SetLike.Set.hasCoeT.{u2, u2} (TopologicalSpace.Opens.{u2} α _inst_1) α (TopologicalSpace.Opens.setLike.{u2} α _inst_1)))) (Finset.sup.{u2, u1} (TopologicalSpace.Opens.{u2} α _inst_1) ι (Lattice.toSemilatticeSup.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (ConditionallyCompleteLattice.toLattice.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u2} α _inst_1)))) (BoundedOrder.toOrderBot.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (Preorder.toLE.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (PartialOrder.toPreorder.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (SemilatticeSup.toPartialOrder.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (Lattice.toSemilatticeSup.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (ConditionallyCompleteLattice.toLattice.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u2} α _inst_1))))))) (CompleteLattice.toBoundedOrder.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u2} α _inst_1))) s f)) (Finset.sup.{u2, u1} (Set.{u2} α) ι (Lattice.toSemilatticeSup.{u2} (Set.{u2} α) (ConditionallyCompleteLattice.toLattice.{u2} (Set.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.completeBooleanAlgebra.{u2} α))))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} α) (Set.booleanAlgebra.{u2} α))) s (Function.comp.{succ u1, succ u2, succ u2} ι (TopologicalSpace.Opens.{u2} α _inst_1) (Set.{u2} α) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (TopologicalSpace.Opens.{u2} α _inst_1) (Set.{u2} α) (HasLiftT.mk.{succ u2, succ u2} (TopologicalSpace.Opens.{u2} α _inst_1) (Set.{u2} α) (CoeTCₓ.coe.{succ u2, succ u2} (TopologicalSpace.Opens.{u2} α _inst_1) (Set.{u2} α) (SetLike.Set.hasCoeT.{u2, u2} (TopologicalSpace.Opens.{u2} α _inst_1) α (TopologicalSpace.Opens.setLike.{u2} α _inst_1))))) f))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] (f : ι -> (TopologicalSpace.Opens.{u2} α _inst_1)) (s : Finset.{u1} ι), Eq.{succ u2} (Set.{u2} α) (SetLike.coe.{u2, u2} (TopologicalSpace.Opens.{u2} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u2} α _inst_1) (Finset.sup.{u2, u1} (TopologicalSpace.Opens.{u2} α _inst_1) ι (Lattice.toSemilatticeSup.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (ConditionallyCompleteLattice.toLattice.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} α _inst_1)))) (BoundedOrder.toOrderBot.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (Preorder.toLE.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (PartialOrder.toPreorder.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (SemilatticeSup.toPartialOrder.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (Lattice.toSemilatticeSup.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (ConditionallyCompleteLattice.toLattice.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} α _inst_1))))))) (CompleteLattice.toBoundedOrder.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} α _inst_1))) s f)) (Finset.sup.{u2, u1} (Set.{u2} α) ι (Lattice.toSemilatticeSup.{u2} (Set.{u2} α) (ConditionallyCompleteLattice.toLattice.{u2} (Set.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (SemilatticeSup.toPartialOrder.{u2} (Set.{u2} α) (Lattice.toSemilatticeSup.{u2} (Set.{u2} α) (ConditionallyCompleteLattice.toLattice.{u2} (Set.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) s (Function.comp.{succ u1, succ u2, succ u2} ι (TopologicalSpace.Opens.{u2} α _inst_1) (Set.{u2} α) (SetLike.coe.{u2, u2} (TopologicalSpace.Opens.{u2} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u2} α _inst_1)) f))
Case conversion may be inaccurate. Consider using '#align topological_space.opens.coe_finset_sup TopologicalSpace.Opens.coe_finset_supₓ'. -/
@[simp, norm_cast]
theorem coe_finset_sup (f : ι → Opens α) (s : Finset ι) : (↑(s.sup f) : Set α) = s.sup (coe ∘ f) :=
  map_finset_sup (⟨⟨coe, coe_sup⟩, coe_bot⟩ : SupBotHom (Opens α) (Set α)) _ _
#align topological_space.opens.coe_finset_sup TopologicalSpace.Opens.coe_finset_sup

/- warning: topological_space.opens.coe_finset_inf -> TopologicalSpace.Opens.coe_finset_inf is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] (f : ι -> (TopologicalSpace.Opens.{u2} α _inst_1)) (s : Finset.{u1} ι), Eq.{succ u2} (Set.{u2} α) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (TopologicalSpace.Opens.{u2} α _inst_1) (Set.{u2} α) (HasLiftT.mk.{succ u2, succ u2} (TopologicalSpace.Opens.{u2} α _inst_1) (Set.{u2} α) (CoeTCₓ.coe.{succ u2, succ u2} (TopologicalSpace.Opens.{u2} α _inst_1) (Set.{u2} α) (SetLike.Set.hasCoeT.{u2, u2} (TopologicalSpace.Opens.{u2} α _inst_1) α (TopologicalSpace.Opens.setLike.{u2} α _inst_1)))) (Finset.inf.{u2, u1} (TopologicalSpace.Opens.{u2} α _inst_1) ι (Lattice.toSemilatticeInf.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (ConditionallyCompleteLattice.toLattice.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u2} α _inst_1)))) (BoundedOrder.toOrderTop.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (Preorder.toLE.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (PartialOrder.toPreorder.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (SemilatticeInf.toPartialOrder.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (Lattice.toSemilatticeInf.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (ConditionallyCompleteLattice.toLattice.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u2} α _inst_1))))))) (CompleteLattice.toBoundedOrder.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u2} α _inst_1))) s f)) (Finset.inf.{u2, u1} (Set.{u2} α) ι (Lattice.toSemilatticeInf.{u2} (Set.{u2} α) (ConditionallyCompleteLattice.toLattice.{u2} (Set.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.completeBooleanAlgebra.{u2} α))))))) (Set.orderTop.{u2} α) s (Function.comp.{succ u1, succ u2, succ u2} ι (TopologicalSpace.Opens.{u2} α _inst_1) (Set.{u2} α) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (TopologicalSpace.Opens.{u2} α _inst_1) (Set.{u2} α) (HasLiftT.mk.{succ u2, succ u2} (TopologicalSpace.Opens.{u2} α _inst_1) (Set.{u2} α) (CoeTCₓ.coe.{succ u2, succ u2} (TopologicalSpace.Opens.{u2} α _inst_1) (Set.{u2} α) (SetLike.Set.hasCoeT.{u2, u2} (TopologicalSpace.Opens.{u2} α _inst_1) α (TopologicalSpace.Opens.setLike.{u2} α _inst_1))))) f))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] (f : ι -> (TopologicalSpace.Opens.{u2} α _inst_1)) (s : Finset.{u1} ι), Eq.{succ u2} (Set.{u2} α) (SetLike.coe.{u2, u2} (TopologicalSpace.Opens.{u2} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u2} α _inst_1) (Finset.inf.{u2, u1} (TopologicalSpace.Opens.{u2} α _inst_1) ι (Lattice.toSemilatticeInf.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (ConditionallyCompleteLattice.toLattice.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} α _inst_1)))) (BoundedOrder.toOrderTop.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (Preorder.toLE.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (PartialOrder.toPreorder.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (SemilatticeInf.toPartialOrder.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (Lattice.toSemilatticeInf.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (ConditionallyCompleteLattice.toLattice.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} α _inst_1))))))) (CompleteLattice.toBoundedOrder.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} α _inst_1))) s f)) (Finset.inf.{u2, u1} (Set.{u2} α) ι (Lattice.toSemilatticeInf.{u2} (Set.{u2} α) (ConditionallyCompleteLattice.toLattice.{u2} (Set.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) (Set.instOrderTopSetInstLESet.{u2} α) s (Function.comp.{succ u1, succ u2, succ u2} ι (TopologicalSpace.Opens.{u2} α _inst_1) (Set.{u2} α) (SetLike.coe.{u2, u2} (TopologicalSpace.Opens.{u2} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u2} α _inst_1)) f))
Case conversion may be inaccurate. Consider using '#align topological_space.opens.coe_finset_inf TopologicalSpace.Opens.coe_finset_infₓ'. -/
@[simp, norm_cast]
theorem coe_finset_inf (f : ι → Opens α) (s : Finset ι) : (↑(s.inf f) : Set α) = s.inf (coe ∘ f) :=
  map_finset_inf (⟨⟨coe, coe_inf⟩, coe_top⟩ : InfTopHom (Opens α) (Set α)) _ _
#align topological_space.opens.coe_finset_inf TopologicalSpace.Opens.coe_finset_inf

instance : Inhabited (Opens α) :=
  ⟨⊥⟩

/- warning: topological_space.opens.supr_def -> TopologicalSpace.Opens.supᵢ_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Sort.{u2}} (s : ι -> (TopologicalSpace.Opens.{u1} α _inst_1)), Eq.{succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (supᵢ.{u1, u2} (TopologicalSpace.Opens.{u1} α _inst_1) (ConditionallyCompleteLattice.toHasSup.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1))) ι (fun (i : ι) => s i)) (TopologicalSpace.Opens.mk.{u1} α _inst_1 (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)))) (s i))) (isOpen_unionᵢ.{u1, u2} α ι _inst_1 (fun (i : ι) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)))) (s i)) (fun (i : ι) => TopologicalSpace.Opens.is_open'.{u1} α _inst_1 (s i))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Sort.{u2}} (s : ι -> (TopologicalSpace.Opens.{u1} α _inst_1)), Eq.{succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (supᵢ.{u1, u2} (TopologicalSpace.Opens.{u1} α _inst_1) (ConditionallyCompleteLattice.toSupSet.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1))) ι (fun (i : ι) => s i)) (TopologicalSpace.Opens.mk.{u1} α _inst_1 (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => SetLike.coe.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u1} α _inst_1) (s i))) (isOpen_unionᵢ.{u1, u2} α ι _inst_1 (fun (i : ι) => SetLike.coe.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u1} α _inst_1) (s i)) (fun (i : ι) => TopologicalSpace.Opens.is_open'.{u1} α _inst_1 (s i))))
Case conversion may be inaccurate. Consider using '#align topological_space.opens.supr_def TopologicalSpace.Opens.supᵢ_defₓ'. -/
theorem supᵢ_def {ι} (s : ι → Opens α) : (⨆ i, s i) = ⟨⋃ i, s i, isOpen_unionᵢ fun i => (s i).2⟩ :=
  by
  ext
  simp only [supᵢ, coe_Sup, bUnion_range]
  rfl
#align topological_space.opens.supr_def TopologicalSpace.Opens.supᵢ_def

/- warning: topological_space.opens.supr_mk -> TopologicalSpace.Opens.supᵢ_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Sort.{u2}} (s : ι -> (Set.{u1} α)) (h : forall (i : ι), IsOpen.{u1} α _inst_1 (s i)), Eq.{succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (supᵢ.{u1, u2} (TopologicalSpace.Opens.{u1} α _inst_1) (ConditionallyCompleteLattice.toHasSup.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1))) ι (fun (i : ι) => TopologicalSpace.Opens.mk.{u1} α _inst_1 (s i) (h i))) (TopologicalSpace.Opens.mk.{u1} α _inst_1 (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => s i)) (isOpen_unionᵢ.{u1, u2} α ι _inst_1 (fun (i : ι) => s i) h))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Sort.{u2}} (s : ι -> (Set.{u1} α)) (h : forall (i : ι), IsOpen.{u1} α _inst_1 (s i)), Eq.{succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (supᵢ.{u1, u2} (TopologicalSpace.Opens.{u1} α _inst_1) (ConditionallyCompleteLattice.toSupSet.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1))) ι (fun (i : ι) => TopologicalSpace.Opens.mk.{u1} α _inst_1 (s i) (h i))) (TopologicalSpace.Opens.mk.{u1} α _inst_1 (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => s i)) (isOpen_unionᵢ.{u1, u2} α ι _inst_1 (fun (i : ι) => s i) h))
Case conversion may be inaccurate. Consider using '#align topological_space.opens.supr_mk TopologicalSpace.Opens.supᵢ_mkₓ'. -/
@[simp]
theorem supᵢ_mk {ι} (s : ι → Set α) (h : ∀ i, IsOpen (s i)) :
    (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_unionᵢ h⟩ :=
  by
  rw [supr_def]
  simp
#align topological_space.opens.supr_mk TopologicalSpace.Opens.supᵢ_mk

/- warning: topological_space.opens.coe_supr -> TopologicalSpace.Opens.coe_supᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Sort.{u2}} (s : ι -> (TopologicalSpace.Opens.{u1} α _inst_1)), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)))) (supᵢ.{u1, u2} (TopologicalSpace.Opens.{u1} α _inst_1) (ConditionallyCompleteLattice.toHasSup.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1))) ι (fun (i : ι) => s i))) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)))) (s i)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Sort.{u2}} (s : ι -> (TopologicalSpace.Opens.{u1} α _inst_1)), Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u1} α _inst_1) (supᵢ.{u1, u2} (TopologicalSpace.Opens.{u1} α _inst_1) (ConditionallyCompleteLattice.toSupSet.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1))) ι (fun (i : ι) => s i))) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => SetLike.coe.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u1} α _inst_1) (s i)))
Case conversion may be inaccurate. Consider using '#align topological_space.opens.coe_supr TopologicalSpace.Opens.coe_supᵢₓ'. -/
@[simp, norm_cast]
theorem coe_supᵢ {ι} (s : ι → Opens α) : ((⨆ i, s i : Opens α) : Set α) = ⋃ i, s i := by
  simp [supr_def]
#align topological_space.opens.coe_supr TopologicalSpace.Opens.coe_supᵢ

/- warning: topological_space.opens.mem_supr -> TopologicalSpace.Opens.mem_supᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Sort.{u2}} {x : α} {s : ι -> (TopologicalSpace.Opens.{u1} α _inst_1)}, Iff (Membership.Mem.{u1, u1} α (TopologicalSpace.Opens.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) x (supᵢ.{u1, u2} (TopologicalSpace.Opens.{u1} α _inst_1) (ConditionallyCompleteLattice.toHasSup.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1))) ι s)) (Exists.{u2} ι (fun (i : ι) => Membership.Mem.{u1, u1} α (TopologicalSpace.Opens.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) x (s i)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Sort.{u2}} {x : α} {s : ι -> (TopologicalSpace.Opens.{u1} α _inst_1)}, Iff (Membership.mem.{u1, u1} α (TopologicalSpace.Opens.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u1} α _inst_1)) x (supᵢ.{u1, u2} (TopologicalSpace.Opens.{u1} α _inst_1) (ConditionallyCompleteLattice.toSupSet.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1))) ι s)) (Exists.{u2} ι (fun (i : ι) => Membership.mem.{u1, u1} α (TopologicalSpace.Opens.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u1} α _inst_1)) x (s i)))
Case conversion may be inaccurate. Consider using '#align topological_space.opens.mem_supr TopologicalSpace.Opens.mem_supᵢₓ'. -/
@[simp]
theorem mem_supᵢ {ι} {x : α} {s : ι → Opens α} : x ∈ supᵢ s ↔ ∃ i, x ∈ s i :=
  by
  rw [← SetLike.mem_coe]
  simp
#align topological_space.opens.mem_supr TopologicalSpace.Opens.mem_supᵢ

/- warning: topological_space.opens.mem_Sup -> TopologicalSpace.Opens.mem_supₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {Us : Set.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)} {x : α}, Iff (Membership.Mem.{u1, u1} α (TopologicalSpace.Opens.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) x (SupSet.supₛ.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (ConditionallyCompleteLattice.toHasSup.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1))) Us)) (Exists.{succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (fun (u : TopologicalSpace.Opens.{u1} α _inst_1) => Exists.{0} (Membership.Mem.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)) (Set.hasMem.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)) u Us) (fun (H : Membership.Mem.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)) (Set.hasMem.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)) u Us) => Membership.Mem.{u1, u1} α (TopologicalSpace.Opens.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) x u)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {Us : Set.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)} {x : α}, Iff (Membership.mem.{u1, u1} α (TopologicalSpace.Opens.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u1} α _inst_1)) x (SupSet.supₛ.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (ConditionallyCompleteLattice.toSupSet.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1))) Us)) (Exists.{succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (fun (u : TopologicalSpace.Opens.{u1} α _inst_1) => And (Membership.mem.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)) (Set.instMembershipSet.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)) u Us) (Membership.mem.{u1, u1} α (TopologicalSpace.Opens.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u1} α _inst_1)) x u)))
Case conversion may be inaccurate. Consider using '#align topological_space.opens.mem_Sup TopologicalSpace.Opens.mem_supₛₓ'. -/
@[simp]
theorem mem_supₛ {Us : Set (Opens α)} {x : α} : x ∈ supₛ Us ↔ ∃ u ∈ Us, x ∈ u := by
  simp_rw [supₛ_eq_supᵢ, mem_supr]
#align topological_space.opens.mem_Sup TopologicalSpace.Opens.mem_supₛ

instance : Frame (Opens α) :=
  { Opens.completeLattice with
    supₛ := supₛ
    inf_sup_le_supᵢ_inf := fun a s =>
      (ext <| by simp only [coe_inf, coe_supr, coe_Sup, Set.inter_unionᵢ₂]).le }

/- warning: topological_space.opens.open_embedding_of_le -> TopologicalSpace.Opens.openEmbedding_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {U : TopologicalSpace.Opens.{u1} α _inst_1} {V : TopologicalSpace.Opens.{u1} α _inst_1} (i : LE.le.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Preorder.toLE.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (SetLike.partialOrder.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)))) U V), OpenEmbedding.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)))) U))) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)))) V))) (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)))) U))) _inst_1) (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)))) V))) _inst_1) (Set.inclusion.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)))) U)) (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)))) V)) i)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {U : TopologicalSpace.Opens.{u1} α _inst_1} {V : TopologicalSpace.Opens.{u1} α _inst_1} (i : LE.le.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Preorder.toLE.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1))))) U V), OpenEmbedding.{u1, u1} (Set.Elem.{u1} α (SetLike.coe.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u1} α _inst_1) U)) (Set.Elem.{u1} α (SetLike.coe.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u1} α _inst_1) V)) (instTopologicalSpaceSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (SetLike.coe.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u1} α _inst_1) U)) _inst_1) (instTopologicalSpaceSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (SetLike.coe.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u1} α _inst_1) V)) _inst_1) (Set.inclusion.{u1} α (SetLike.coe.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u1} α _inst_1) U) (SetLike.coe.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u1} α _inst_1) V) (Iff.mpr (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u1} α _inst_1) U) (SetLike.coe.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u1} α _inst_1) V)) (LE.le.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Preorder.toLE.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (SetLike.instPartialOrder.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u1} α _inst_1)))) U V) (SetLike.coe_subset_coe.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u1} α _inst_1) U V) i))
Case conversion may be inaccurate. Consider using '#align topological_space.opens.open_embedding_of_le TopologicalSpace.Opens.openEmbedding_of_leₓ'. -/
theorem openEmbedding_of_le {U V : Opens α} (i : U ≤ V) : OpenEmbedding (Set.inclusion i) :=
  { inj := Set.inclusion_injective i
    induced := (@induced_compose _ _ _ _ (Set.inclusion i) coe).symm
    open_range := by
      rw [Set.range_inclusion i]
      exact U.is_open.preimage continuous_subtype_val }
#align topological_space.opens.open_embedding_of_le TopologicalSpace.Opens.openEmbedding_of_le

/- warning: topological_space.opens.not_nonempty_iff_eq_bot -> TopologicalSpace.Opens.not_nonempty_iff_eq_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (U : TopologicalSpace.Opens.{u1} α _inst_1), Iff (Not (Set.Nonempty.{u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)))) U))) (Eq.{succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) U (Bot.bot.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteLattice.toHasBot.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (U : TopologicalSpace.Opens.{u1} α _inst_1), Iff (Not (Set.Nonempty.{u1} α (SetLike.coe.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u1} α _inst_1) U))) (Eq.{succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) U (Bot.bot.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteLattice.toBot.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align topological_space.opens.not_nonempty_iff_eq_bot TopologicalSpace.Opens.not_nonempty_iff_eq_botₓ'. -/
theorem not_nonempty_iff_eq_bot (U : Opens α) : ¬Set.Nonempty (U : Set α) ↔ U = ⊥ := by
  rw [← coe_inj, opens.coe_bot, ← Set.not_nonempty_iff_eq_empty]
#align topological_space.opens.not_nonempty_iff_eq_bot TopologicalSpace.Opens.not_nonempty_iff_eq_bot

/- warning: topological_space.opens.ne_bot_iff_nonempty -> TopologicalSpace.Opens.ne_bot_iff_nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (U : TopologicalSpace.Opens.{u1} α _inst_1), Iff (Ne.{succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) U (Bot.bot.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteLattice.toHasBot.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1)))) (Set.Nonempty.{u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)))) U))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (U : TopologicalSpace.Opens.{u1} α _inst_1), Iff (Ne.{succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) U (Bot.bot.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteLattice.toBot.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1)))) (Set.Nonempty.{u1} α (SetLike.coe.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u1} α _inst_1) U))
Case conversion may be inaccurate. Consider using '#align topological_space.opens.ne_bot_iff_nonempty TopologicalSpace.Opens.ne_bot_iff_nonemptyₓ'. -/
theorem ne_bot_iff_nonempty (U : Opens α) : U ≠ ⊥ ↔ Set.Nonempty (U : Set α) := by
  rw [Ne.def, ← opens.not_nonempty_iff_eq_bot, Classical.not_not]
#align topological_space.opens.ne_bot_iff_nonempty TopologicalSpace.Opens.ne_bot_iff_nonempty

/- warning: topological_space.opens.eq_bot_or_top -> TopologicalSpace.Opens.eq_bot_or_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α], (Eq.{succ u1} (TopologicalSpace.{u1} α) t (Top.top.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toHasTop.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.completeLattice.{u1} α)))) -> (forall (U : TopologicalSpace.Opens.{u1} α t), Or (Eq.{succ u1} (TopologicalSpace.Opens.{u1} α t) U (Bot.bot.{u1} (TopologicalSpace.Opens.{u1} α t) (CompleteLattice.toHasBot.{u1} (TopologicalSpace.Opens.{u1} α t) (TopologicalSpace.Opens.completeLattice.{u1} α t)))) (Eq.{succ u1} (TopologicalSpace.Opens.{u1} α t) U (Top.top.{u1} (TopologicalSpace.Opens.{u1} α t) (CompleteLattice.toHasTop.{u1} (TopologicalSpace.Opens.{u1} α t) (TopologicalSpace.Opens.completeLattice.{u1} α t)))))
but is expected to have type
  forall {α : Type.{u1}} [t : TopologicalSpace.{u1} α], (Eq.{succ u1} (TopologicalSpace.{u1} α) t (Top.top.{u1} (TopologicalSpace.{u1} α) (CompleteLattice.toTop.{u1} (TopologicalSpace.{u1} α) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} α)))) -> (forall (U : TopologicalSpace.Opens.{u1} α t), Or (Eq.{succ u1} (TopologicalSpace.Opens.{u1} α t) U (Bot.bot.{u1} (TopologicalSpace.Opens.{u1} α t) (CompleteLattice.toBot.{u1} (TopologicalSpace.Opens.{u1} α t) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α t)))) (Eq.{succ u1} (TopologicalSpace.Opens.{u1} α t) U (Top.top.{u1} (TopologicalSpace.Opens.{u1} α t) (CompleteLattice.toTop.{u1} (TopologicalSpace.Opens.{u1} α t) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α t)))))
Case conversion may be inaccurate. Consider using '#align topological_space.opens.eq_bot_or_top TopologicalSpace.Opens.eq_bot_or_topₓ'. -/
/-- An open set in the indiscrete topology is either empty or the whole space. -/
theorem eq_bot_or_top {α} [t : TopologicalSpace α] (h : t = ⊤) (U : Opens α) : U = ⊥ ∨ U = ⊤ :=
  by
  simp only [← coe_inj]
  subst h; letI : TopologicalSpace α := ⊤
  exact (is_open_top_iff _).1 U.2
#align topological_space.opens.eq_bot_or_top TopologicalSpace.Opens.eq_bot_or_top

#print TopologicalSpace.Opens.IsBasis /-
/-- A set of `opens α` is a basis if the set of corresponding sets is a topological basis. -/
def IsBasis (B : Set (Opens α)) : Prop :=
  IsTopologicalBasis ((coe : _ → Set α) '' B)
#align topological_space.opens.is_basis TopologicalSpace.Opens.IsBasis
-/

/- warning: topological_space.opens.is_basis_iff_nbhd -> TopologicalSpace.Opens.isBasis_iff_nbhd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {B : Set.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)}, Iff (TopologicalSpace.Opens.IsBasis.{u1} α _inst_1 B) (forall {U : TopologicalSpace.Opens.{u1} α _inst_1} {x : α}, (Membership.Mem.{u1, u1} α (TopologicalSpace.Opens.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) x U) -> (Exists.{succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (fun (U' : TopologicalSpace.Opens.{u1} α _inst_1) => Exists.{0} (Membership.Mem.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)) (Set.hasMem.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)) U' B) (fun (H : Membership.Mem.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)) (Set.hasMem.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)) U' B) => And (Membership.Mem.{u1, u1} α (TopologicalSpace.Opens.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)) x U') (LE.le.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Preorder.toLE.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (SetLike.partialOrder.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)))) U' U)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {B : Set.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)}, Iff (TopologicalSpace.Opens.IsBasis.{u1} α _inst_1 B) (forall {U : TopologicalSpace.Opens.{u1} α _inst_1} {x : α}, (Membership.mem.{u1, u1} α (TopologicalSpace.Opens.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u1} α _inst_1)) x U) -> (Exists.{succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (fun (U' : TopologicalSpace.Opens.{u1} α _inst_1) => And (Membership.mem.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)) (Set.instMembershipSet.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)) U' B) (And (Membership.mem.{u1, u1} α (TopologicalSpace.Opens.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u1} α _inst_1)) x U') (LE.le.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Preorder.toLE.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1))))) U' U)))))
Case conversion may be inaccurate. Consider using '#align topological_space.opens.is_basis_iff_nbhd TopologicalSpace.Opens.isBasis_iff_nbhdₓ'. -/
theorem isBasis_iff_nbhd {B : Set (Opens α)} :
    IsBasis B ↔ ∀ {U : Opens α} {x}, x ∈ U → ∃ U' ∈ B, x ∈ U' ∧ U' ≤ U :=
  by
  constructor <;> intro h
  · rintro ⟨sU, hU⟩ x hx
    rcases h.mem_nhds_iff.mp (IsOpen.mem_nhds hU hx) with ⟨sV, ⟨⟨V, H₁, H₂⟩, hsV⟩⟩
    refine' ⟨V, H₁, _⟩
    cases V
    dsimp at H₂
    subst H₂
    exact hsV
  · refine' is_topological_basis_of_open_of_nhds _ _
    · rintro sU ⟨U, ⟨H₁, rfl⟩⟩
      exact U.2
    · intro x sU hx hsU
      rcases@h (⟨sU, hsU⟩ : opens α) x hx with ⟨V, hV, H⟩
      exact ⟨V, ⟨V, hV, rfl⟩, H⟩
#align topological_space.opens.is_basis_iff_nbhd TopologicalSpace.Opens.isBasis_iff_nbhd

/- warning: topological_space.opens.is_basis_iff_cover -> TopologicalSpace.Opens.isBasis_iff_cover is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {B : Set.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)}, Iff (TopologicalSpace.Opens.IsBasis.{u1} α _inst_1 B) (forall (U : TopologicalSpace.Opens.{u1} α _inst_1), Exists.{succ u1} (Set.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)) (fun (Us : Set.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)) => Exists.{0} (HasSubset.Subset.{u1} (Set.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)) (Set.hasSubset.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)) Us B) (fun (H : HasSubset.Subset.{u1} (Set.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)) (Set.hasSubset.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)) Us B) => Eq.{succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) U (SupSet.supₛ.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (ConditionallyCompleteLattice.toHasSup.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1))) Us))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {B : Set.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)}, Iff (TopologicalSpace.Opens.IsBasis.{u1} α _inst_1 B) (forall (U : TopologicalSpace.Opens.{u1} α _inst_1), Exists.{succ u1} (Set.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)) (fun (Us : Set.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)) => And (HasSubset.Subset.{u1} (Set.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)) (Set.instHasSubsetSet.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)) Us B) (Eq.{succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) U (SupSet.supₛ.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (ConditionallyCompleteLattice.toSupSet.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1))) Us))))
Case conversion may be inaccurate. Consider using '#align topological_space.opens.is_basis_iff_cover TopologicalSpace.Opens.isBasis_iff_coverₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (Us «expr ⊆ » B) -/
theorem isBasis_iff_cover {B : Set (Opens α)} :
    IsBasis B ↔ ∀ U : Opens α, ∃ (Us : _)(_ : Us ⊆ B), U = supₛ Us :=
  by
  constructor
  · intro hB U
    refine' ⟨{ V : opens α | V ∈ B ∧ V ≤ U }, fun U hU => hU.left, _⟩
    apply ext
    rw [coe_Sup, hB.open_eq_sUnion' U.is_open]
    simp_rw [sUnion_eq_bUnion, Union, supᵢ_and, supᵢ_image]
    rfl
  · intro h
    rw [is_basis_iff_nbhd]
    intro U x hx
    rcases h U with ⟨Us, hUs, rfl⟩
    rcases mem_Sup.1 hx with ⟨U, Us, xU⟩
    exact ⟨U, hUs Us, xU, le_supₛ Us⟩
#align topological_space.opens.is_basis_iff_cover TopologicalSpace.Opens.isBasis_iff_cover

#print TopologicalSpace.Opens.IsBasis.isCompact_open_iff_eq_finite_unionᵢ /-
/-- If `α` has a basis consisting of compact opens, then an open set in `α` is compact open iff
  it is a finite union of some elements in the basis -/
theorem IsBasis.isCompact_open_iff_eq_finite_unionᵢ {ι : Type _} (b : ι → Opens α)
    (hb : IsBasis (Set.range b)) (hb' : ∀ i, IsCompact (b i : Set α)) (U : Set α) :
    IsCompact U ∧ IsOpen U ↔ ∃ s : Set ι, s.Finite ∧ U = ⋃ i ∈ s, b i :=
  by
  apply isCompact_open_iff_eq_finite_unionᵢ_of_isTopologicalBasis fun i : ι => (b i).1
  · convert hb
    ext
    simp
  · exact hb'
#align topological_space.opens.is_basis.is_compact_open_iff_eq_finite_Union TopologicalSpace.Opens.IsBasis.isCompact_open_iff_eq_finite_unionᵢ
-/

/- warning: topological_space.opens.is_compact_element_iff -> TopologicalSpace.Opens.isCompactElement_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : TopologicalSpace.Opens.{u1} α _inst_1), Iff (CompleteLattice.IsCompactElement.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1) s) (IsCompact.{u1} α _inst_1 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : TopologicalSpace.Opens.{u1} α _inst_1), Iff (CompleteLattice.IsCompactElement.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1) s) (IsCompact.{u1} α _inst_1 (SetLike.coe.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.instSetLikeOpens.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align topological_space.opens.is_compact_element_iff TopologicalSpace.Opens.isCompactElement_iffₓ'. -/
@[simp]
theorem isCompactElement_iff (s : Opens α) :
    CompleteLattice.IsCompactElement s ↔ IsCompact (s : Set α) :=
  by
  rw [isCompact_iff_finite_subcover, CompleteLattice.isCompactElement_iff]
  refine' ⟨_, fun H ι U hU => _⟩
  · introv H hU hU'
    obtain ⟨t, ht⟩ := H ι (fun i => ⟨U i, hU i⟩) (by simpa)
    refine' ⟨t, Set.Subset.trans ht _⟩
    rw [coe_finset_sup, Finset.sup_eq_supᵢ]
    rfl
  · obtain ⟨t, ht⟩ :=
      H (fun i => U i) (fun i => (U i).IsOpen) (by simpa using show (s : Set α) ⊆ ↑(supᵢ U) from hU)
    refine' ⟨t, Set.Subset.trans ht _⟩
    simp only [Set.unionᵢ_subset_iff]
    show ∀ i ∈ t, U i ≤ t.sup U
    exact fun i => Finset.le_sup
#align topological_space.opens.is_compact_element_iff TopologicalSpace.Opens.isCompactElement_iff

/- warning: topological_space.opens.comap -> TopologicalSpace.Opens.comap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) -> (FrameHom.{u2, u1} (TopologicalSpace.Opens.{u2} β _inst_2) (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u2} β _inst_2) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) -> (FrameHom.{u2, u1} (TopologicalSpace.Opens.{u2} β _inst_2) (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align topological_space.opens.comap TopologicalSpace.Opens.comapₓ'. -/
/-- The preimage of an open set, as an open set. -/
def comap (f : C(α, β)) : FrameHom (Opens β) (Opens α)
    where
  toFun s := ⟨f ⁻¹' s, s.2.Preimage f.Continuous⟩
  map_Sup' s := ext <| by simp only [coe_Sup, preimage_Union, bUnion_image, coe_mk]
  map_inf' a b := rfl
  map_top' := rfl
#align topological_space.opens.comap TopologicalSpace.Opens.comap

/- warning: topological_space.opens.comap_id -> TopologicalSpace.Opens.comap_id is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α], Eq.{succ u1} (FrameHom.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1)) (TopologicalSpace.Opens.comap.{u1, u1} α α _inst_1 _inst_1 (ContinuousMap.id.{u1} α _inst_1)) (FrameHom.id.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α], Eq.{succ u1} (FrameHom.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1)) (TopologicalSpace.Opens.comap.{u1, u1} α α _inst_1 _inst_1 (ContinuousMap.id.{u1} α _inst_1)) (FrameHom.id.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align topological_space.opens.comap_id TopologicalSpace.Opens.comap_idₓ'. -/
@[simp]
theorem comap_id : comap (ContinuousMap.id α) = FrameHom.id _ :=
  FrameHom.ext fun a => ext rfl
#align topological_space.opens.comap_id TopologicalSpace.Opens.comap_id

/- warning: topological_space.opens.comap_mono -> TopologicalSpace.Opens.comap_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) {s : TopologicalSpace.Opens.{u2} β _inst_2} {t : TopologicalSpace.Opens.{u2} β _inst_2}, (LE.le.{u2} (TopologicalSpace.Opens.{u2} β _inst_2) (Preorder.toLE.{u2} (TopologicalSpace.Opens.{u2} β _inst_2) (PartialOrder.toPreorder.{u2} (TopologicalSpace.Opens.{u2} β _inst_2) (SetLike.partialOrder.{u2, u2} (TopologicalSpace.Opens.{u2} β _inst_2) β (TopologicalSpace.Opens.setLike.{u2} β _inst_2)))) s t) -> (LE.le.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Preorder.toLE.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (SetLike.partialOrder.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)))) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (FrameHom.{u2, u1} (TopologicalSpace.Opens.{u2} β _inst_2) (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u2} β _inst_2) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1)) (fun (_x : FrameHom.{u2, u1} (TopologicalSpace.Opens.{u2} β _inst_2) (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u2} β _inst_2) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1)) => (TopologicalSpace.Opens.{u2} β _inst_2) -> (TopologicalSpace.Opens.{u1} α _inst_1)) (FrameHom.hasCoeToFun.{u2, u1} (TopologicalSpace.Opens.{u2} β _inst_2) (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u2} β _inst_2) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1)) (TopologicalSpace.Opens.comap.{u1, u2} α β _inst_1 _inst_2 f) s) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (FrameHom.{u2, u1} (TopologicalSpace.Opens.{u2} β _inst_2) (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u2} β _inst_2) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1)) (fun (_x : FrameHom.{u2, u1} (TopologicalSpace.Opens.{u2} β _inst_2) (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u2} β _inst_2) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1)) => (TopologicalSpace.Opens.{u2} β _inst_2) -> (TopologicalSpace.Opens.{u1} α _inst_1)) (FrameHom.hasCoeToFun.{u2, u1} (TopologicalSpace.Opens.{u2} β _inst_2) (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u2} β _inst_2) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1)) (TopologicalSpace.Opens.comap.{u1, u2} α β _inst_1 _inst_2 f) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (f : ContinuousMap.{u2, u1} α β _inst_1 _inst_2) {s : TopologicalSpace.Opens.{u1} β _inst_2} {t : TopologicalSpace.Opens.{u1} β _inst_2}, (LE.le.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (Preorder.toLE.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} β _inst_2))))) s t) -> (LE.le.{u2} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : TopologicalSpace.Opens.{u1} β _inst_2) => TopologicalSpace.Opens.{u2} α _inst_1) s) (Preorder.toLE.{u2} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : TopologicalSpace.Opens.{u1} β _inst_2) => TopologicalSpace.Opens.{u2} α _inst_1) s) (PartialOrder.toPreorder.{u2} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : TopologicalSpace.Opens.{u1} β _inst_2) => TopologicalSpace.Opens.{u2} α _inst_1) s) (CompleteSemilatticeInf.toPartialOrder.{u2} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : TopologicalSpace.Opens.{u1} β _inst_2) => TopologicalSpace.Opens.{u2} α _inst_1) s) (CompleteLattice.toCompleteSemilatticeInf.{u2} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : TopologicalSpace.Opens.{u1} β _inst_2) => TopologicalSpace.Opens.{u2} α _inst_1) s) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} α _inst_1))))) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (FrameHom.{u1, u2} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.{u2} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} α _inst_1)) (TopologicalSpace.Opens.{u1} β _inst_2) (fun (_x : TopologicalSpace.Opens.{u1} β _inst_2) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : TopologicalSpace.Opens.{u1} β _inst_2) => TopologicalSpace.Opens.{u2} α _inst_1) _x) (SupₛHomClass.toFunLike.{max u2 u1, u1, u2} (FrameHom.{u1, u2} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.{u2} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} α _inst_1)) (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.{u2} α _inst_1) (CompleteLattice.toSupSet.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} β _inst_2)) (CompleteLattice.toSupSet.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} α _inst_1)) (FrameHomClass.toSupₛHomClass.{max u2 u1, u1, u2} (FrameHom.{u1, u2} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.{u2} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} α _inst_1)) (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.{u2} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} α _inst_1) (FrameHom.instFrameHomClassFrameHom.{u1, u2} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.{u2} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} α _inst_1)))) (TopologicalSpace.Opens.comap.{u2, u1} α β _inst_1 _inst_2 f) s) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (FrameHom.{u1, u2} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.{u2} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} α _inst_1)) (TopologicalSpace.Opens.{u1} β _inst_2) (fun (_x : TopologicalSpace.Opens.{u1} β _inst_2) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : TopologicalSpace.Opens.{u1} β _inst_2) => TopologicalSpace.Opens.{u2} α _inst_1) _x) (SupₛHomClass.toFunLike.{max u2 u1, u1, u2} (FrameHom.{u1, u2} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.{u2} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} α _inst_1)) (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.{u2} α _inst_1) (CompleteLattice.toSupSet.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} β _inst_2)) (CompleteLattice.toSupSet.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} α _inst_1)) (FrameHomClass.toSupₛHomClass.{max u2 u1, u1, u2} (FrameHom.{u1, u2} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.{u2} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} α _inst_1)) (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.{u2} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} α _inst_1) (FrameHom.instFrameHomClassFrameHom.{u1, u2} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.{u2} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} α _inst_1)))) (TopologicalSpace.Opens.comap.{u2, u1} α β _inst_1 _inst_2 f) t))
Case conversion may be inaccurate. Consider using '#align topological_space.opens.comap_mono TopologicalSpace.Opens.comap_monoₓ'. -/
theorem comap_mono (f : C(α, β)) {s t : Opens β} (h : s ≤ t) : comap f s ≤ comap f t :=
  OrderHomClass.mono (comap f) h
#align topological_space.opens.comap_mono TopologicalSpace.Opens.comap_mono

/- warning: topological_space.opens.coe_comap -> TopologicalSpace.Opens.coe_comap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (U : TopologicalSpace.Opens.{u2} β _inst_2), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)))) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (FrameHom.{u2, u1} (TopologicalSpace.Opens.{u2} β _inst_2) (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u2} β _inst_2) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1)) (fun (_x : FrameHom.{u2, u1} (TopologicalSpace.Opens.{u2} β _inst_2) (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u2} β _inst_2) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1)) => (TopologicalSpace.Opens.{u2} β _inst_2) -> (TopologicalSpace.Opens.{u1} α _inst_1)) (FrameHom.hasCoeToFun.{u2, u1} (TopologicalSpace.Opens.{u2} β _inst_2) (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u2} β _inst_2) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1)) (TopologicalSpace.Opens.comap.{u1, u2} α β _inst_1 _inst_2 f) U)) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (TopologicalSpace.Opens.{u2} β _inst_2) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (TopologicalSpace.Opens.{u2} β _inst_2) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (TopologicalSpace.Opens.{u2} β _inst_2) (Set.{u2} β) (SetLike.Set.hasCoeT.{u2, u2} (TopologicalSpace.Opens.{u2} β _inst_2) β (TopologicalSpace.Opens.setLike.{u2} β _inst_2)))) U))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (f : ContinuousMap.{u2, u1} α β _inst_1 _inst_2) (U : TopologicalSpace.Opens.{u1} β _inst_2), Eq.{succ u2} (Set.{u2} α) (SetLike.coe.{u2, u2} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : TopologicalSpace.Opens.{u1} β _inst_2) => TopologicalSpace.Opens.{u2} α _inst_1) U) α (TopologicalSpace.Opens.instSetLikeOpens.{u2} α _inst_1) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (FrameHom.{u1, u2} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.{u2} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} α _inst_1)) (TopologicalSpace.Opens.{u1} β _inst_2) (fun (_x : TopologicalSpace.Opens.{u1} β _inst_2) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : TopologicalSpace.Opens.{u1} β _inst_2) => TopologicalSpace.Opens.{u2} α _inst_1) _x) (SupₛHomClass.toFunLike.{max u2 u1, u1, u2} (FrameHom.{u1, u2} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.{u2} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} α _inst_1)) (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.{u2} α _inst_1) (CompleteLattice.toSupSet.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} β _inst_2)) (CompleteLattice.toSupSet.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} α _inst_1)) (FrameHomClass.toSupₛHomClass.{max u2 u1, u1, u2} (FrameHom.{u1, u2} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.{u2} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} α _inst_1)) (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.{u2} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} α _inst_1) (FrameHom.instFrameHomClassFrameHom.{u1, u2} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.{u2} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} α _inst_1)))) (TopologicalSpace.Opens.comap.{u2, u1} α β _inst_1 _inst_2 f) U)) (Set.preimage.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} α β _inst_1 _inst_2)) f) (SetLike.coe.{u1, u1} (TopologicalSpace.Opens.{u1} β _inst_2) β (TopologicalSpace.Opens.instSetLikeOpens.{u1} β _inst_2) U))
Case conversion may be inaccurate. Consider using '#align topological_space.opens.coe_comap TopologicalSpace.Opens.coe_comapₓ'. -/
@[simp]
theorem coe_comap (f : C(α, β)) (U : Opens β) : ↑(comap f U) = f ⁻¹' U :=
  rfl
#align topological_space.opens.coe_comap TopologicalSpace.Opens.coe_comap

/- warning: topological_space.opens.comap_comp -> TopologicalSpace.Opens.comap_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (g : ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u3) (succ u1)} (FrameHom.{u3, u1} (TopologicalSpace.Opens.{u3} γ _inst_3) (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u3} γ _inst_3) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1)) (TopologicalSpace.Opens.comap.{u1, u3} α γ _inst_1 _inst_3 (ContinuousMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g f)) (FrameHom.comp.{u3, u2, u1} (TopologicalSpace.Opens.{u3} γ _inst_3) (TopologicalSpace.Opens.{u2} β _inst_2) (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u3} γ _inst_3) (TopologicalSpace.Opens.completeLattice.{u2} β _inst_2) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1) (TopologicalSpace.Opens.comap.{u1, u2} α β _inst_1 _inst_2 f) (TopologicalSpace.Opens.comap.{u2, u3} β γ _inst_2 _inst_3 g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] (g : ContinuousMap.{u3, u2} β γ _inst_2 _inst_3) (f : ContinuousMap.{u1, u3} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (FrameHom.{u2, u1} (TopologicalSpace.Opens.{u2} γ _inst_3) (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} γ _inst_3) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1)) (TopologicalSpace.Opens.comap.{u1, u2} α γ _inst_1 _inst_3 (ContinuousMap.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f)) (FrameHom.comp.{u2, u3, u1} (TopologicalSpace.Opens.{u2} γ _inst_3) (TopologicalSpace.Opens.{u3} β _inst_2) (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} γ _inst_3) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u3} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1) (TopologicalSpace.Opens.comap.{u1, u3} α β _inst_1 _inst_2 f) (TopologicalSpace.Opens.comap.{u3, u2} β γ _inst_2 _inst_3 g))
Case conversion may be inaccurate. Consider using '#align topological_space.opens.comap_comp TopologicalSpace.Opens.comap_compₓ'. -/
protected theorem comap_comp (g : C(β, γ)) (f : C(α, β)) :
    comap (g.comp f) = (comap f).comp (comap g) :=
  rfl
#align topological_space.opens.comap_comp TopologicalSpace.Opens.comap_comp

/- warning: topological_space.opens.comap_comap -> TopologicalSpace.Opens.comap_comap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (g : ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (U : TopologicalSpace.Opens.{u3} γ _inst_3), Eq.{succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (FrameHom.{u2, u1} (TopologicalSpace.Opens.{u2} β _inst_2) (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u2} β _inst_2) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1)) (fun (_x : FrameHom.{u2, u1} (TopologicalSpace.Opens.{u2} β _inst_2) (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u2} β _inst_2) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1)) => (TopologicalSpace.Opens.{u2} β _inst_2) -> (TopologicalSpace.Opens.{u1} α _inst_1)) (FrameHom.hasCoeToFun.{u2, u1} (TopologicalSpace.Opens.{u2} β _inst_2) (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u2} β _inst_2) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1)) (TopologicalSpace.Opens.comap.{u1, u2} α β _inst_1 _inst_2 f) (coeFn.{max (succ u3) (succ u2), max (succ u3) (succ u2)} (FrameHom.{u3, u2} (TopologicalSpace.Opens.{u3} γ _inst_3) (TopologicalSpace.Opens.{u2} β _inst_2) (TopologicalSpace.Opens.completeLattice.{u3} γ _inst_3) (TopologicalSpace.Opens.completeLattice.{u2} β _inst_2)) (fun (_x : FrameHom.{u3, u2} (TopologicalSpace.Opens.{u3} γ _inst_3) (TopologicalSpace.Opens.{u2} β _inst_2) (TopologicalSpace.Opens.completeLattice.{u3} γ _inst_3) (TopologicalSpace.Opens.completeLattice.{u2} β _inst_2)) => (TopologicalSpace.Opens.{u3} γ _inst_3) -> (TopologicalSpace.Opens.{u2} β _inst_2)) (FrameHom.hasCoeToFun.{u3, u2} (TopologicalSpace.Opens.{u3} γ _inst_3) (TopologicalSpace.Opens.{u2} β _inst_2) (TopologicalSpace.Opens.completeLattice.{u3} γ _inst_3) (TopologicalSpace.Opens.completeLattice.{u2} β _inst_2)) (TopologicalSpace.Opens.comap.{u2, u3} β γ _inst_2 _inst_3 g) U)) (coeFn.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (FrameHom.{u3, u1} (TopologicalSpace.Opens.{u3} γ _inst_3) (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u3} γ _inst_3) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1)) (fun (_x : FrameHom.{u3, u1} (TopologicalSpace.Opens.{u3} γ _inst_3) (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u3} γ _inst_3) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1)) => (TopologicalSpace.Opens.{u3} γ _inst_3) -> (TopologicalSpace.Opens.{u1} α _inst_1)) (FrameHom.hasCoeToFun.{u3, u1} (TopologicalSpace.Opens.{u3} γ _inst_3) (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u3} γ _inst_3) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1)) (TopologicalSpace.Opens.comap.{u1, u3} α γ _inst_1 _inst_3 (ContinuousMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g f)) U)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] (g : ContinuousMap.{u3, u2} β γ _inst_2 _inst_3) (f : ContinuousMap.{u1, u3} α β _inst_1 _inst_2) (U : TopologicalSpace.Opens.{u2} γ _inst_3), Eq.{succ u1} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : TopologicalSpace.Opens.{u3} β _inst_2) => TopologicalSpace.Opens.{u1} α _inst_1) (FunLike.coe.{max (succ u3) (succ u2), succ u2, succ u3} (FrameHom.{u2, u3} (TopologicalSpace.Opens.{u2} γ _inst_3) (TopologicalSpace.Opens.{u3} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} γ _inst_3) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u3} β _inst_2)) (TopologicalSpace.Opens.{u2} γ _inst_3) (fun (a : TopologicalSpace.Opens.{u2} γ _inst_3) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : TopologicalSpace.Opens.{u2} γ _inst_3) => TopologicalSpace.Opens.{u3} β _inst_2) a) (SupₛHomClass.toFunLike.{max u3 u2, u2, u3} (FrameHom.{u2, u3} (TopologicalSpace.Opens.{u2} γ _inst_3) (TopologicalSpace.Opens.{u3} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} γ _inst_3) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u3} β _inst_2)) (TopologicalSpace.Opens.{u2} γ _inst_3) (TopologicalSpace.Opens.{u3} β _inst_2) (CompleteLattice.toSupSet.{u2} (TopologicalSpace.Opens.{u2} γ _inst_3) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} γ _inst_3)) (CompleteLattice.toSupSet.{u3} (TopologicalSpace.Opens.{u3} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u3} β _inst_2)) (FrameHomClass.toSupₛHomClass.{max u3 u2, u2, u3} (FrameHom.{u2, u3} (TopologicalSpace.Opens.{u2} γ _inst_3) (TopologicalSpace.Opens.{u3} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} γ _inst_3) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u3} β _inst_2)) (TopologicalSpace.Opens.{u2} γ _inst_3) (TopologicalSpace.Opens.{u3} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} γ _inst_3) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u3} β _inst_2) (FrameHom.instFrameHomClassFrameHom.{u2, u3} (TopologicalSpace.Opens.{u2} γ _inst_3) (TopologicalSpace.Opens.{u3} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} γ _inst_3) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u3} β _inst_2)))) (TopologicalSpace.Opens.comap.{u3, u2} β γ _inst_2 _inst_3 g) U)) (FunLike.coe.{max (succ u1) (succ u3), succ u3, succ u1} (FrameHom.{u3, u1} (TopologicalSpace.Opens.{u3} β _inst_2) (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u3} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1)) (TopologicalSpace.Opens.{u3} β _inst_2) (fun (_x : TopologicalSpace.Opens.{u3} β _inst_2) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : TopologicalSpace.Opens.{u3} β _inst_2) => TopologicalSpace.Opens.{u1} α _inst_1) _x) (SupₛHomClass.toFunLike.{max u1 u3, u3, u1} (FrameHom.{u3, u1} (TopologicalSpace.Opens.{u3} β _inst_2) (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u3} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1)) (TopologicalSpace.Opens.{u3} β _inst_2) (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteLattice.toSupSet.{u3} (TopologicalSpace.Opens.{u3} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u3} β _inst_2)) (CompleteLattice.toSupSet.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1)) (FrameHomClass.toSupₛHomClass.{max u1 u3, u3, u1} (FrameHom.{u3, u1} (TopologicalSpace.Opens.{u3} β _inst_2) (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u3} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1)) (TopologicalSpace.Opens.{u3} β _inst_2) (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u3} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1) (FrameHom.instFrameHomClassFrameHom.{u3, u1} (TopologicalSpace.Opens.{u3} β _inst_2) (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u3} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1)))) (TopologicalSpace.Opens.comap.{u1, u3} α β _inst_1 _inst_2 f) (FunLike.coe.{max (succ u3) (succ u2), succ u2, succ u3} (FrameHom.{u2, u3} (TopologicalSpace.Opens.{u2} γ _inst_3) (TopologicalSpace.Opens.{u3} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} γ _inst_3) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u3} β _inst_2)) (TopologicalSpace.Opens.{u2} γ _inst_3) (fun (_x : TopologicalSpace.Opens.{u2} γ _inst_3) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : TopologicalSpace.Opens.{u2} γ _inst_3) => TopologicalSpace.Opens.{u3} β _inst_2) _x) (SupₛHomClass.toFunLike.{max u3 u2, u2, u3} (FrameHom.{u2, u3} (TopologicalSpace.Opens.{u2} γ _inst_3) (TopologicalSpace.Opens.{u3} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} γ _inst_3) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u3} β _inst_2)) (TopologicalSpace.Opens.{u2} γ _inst_3) (TopologicalSpace.Opens.{u3} β _inst_2) (CompleteLattice.toSupSet.{u2} (TopologicalSpace.Opens.{u2} γ _inst_3) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} γ _inst_3)) (CompleteLattice.toSupSet.{u3} (TopologicalSpace.Opens.{u3} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u3} β _inst_2)) (FrameHomClass.toSupₛHomClass.{max u3 u2, u2, u3} (FrameHom.{u2, u3} (TopologicalSpace.Opens.{u2} γ _inst_3) (TopologicalSpace.Opens.{u3} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} γ _inst_3) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u3} β _inst_2)) (TopologicalSpace.Opens.{u2} γ _inst_3) (TopologicalSpace.Opens.{u3} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} γ _inst_3) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u3} β _inst_2) (FrameHom.instFrameHomClassFrameHom.{u2, u3} (TopologicalSpace.Opens.{u2} γ _inst_3) (TopologicalSpace.Opens.{u3} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} γ _inst_3) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u3} β _inst_2)))) (TopologicalSpace.Opens.comap.{u3, u2} β γ _inst_2 _inst_3 g) U)) (FunLike.coe.{max (succ u1) (succ u2), succ u2, succ u1} (FrameHom.{u2, u1} (TopologicalSpace.Opens.{u2} γ _inst_3) (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} γ _inst_3) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1)) (TopologicalSpace.Opens.{u2} γ _inst_3) (fun (_x : TopologicalSpace.Opens.{u2} γ _inst_3) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : TopologicalSpace.Opens.{u2} γ _inst_3) => TopologicalSpace.Opens.{u1} α _inst_1) _x) (SupₛHomClass.toFunLike.{max u1 u2, u2, u1} (FrameHom.{u2, u1} (TopologicalSpace.Opens.{u2} γ _inst_3) (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} γ _inst_3) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1)) (TopologicalSpace.Opens.{u2} γ _inst_3) (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteLattice.toSupSet.{u2} (TopologicalSpace.Opens.{u2} γ _inst_3) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} γ _inst_3)) (CompleteLattice.toSupSet.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1)) (FrameHomClass.toSupₛHomClass.{max u1 u2, u2, u1} (FrameHom.{u2, u1} (TopologicalSpace.Opens.{u2} γ _inst_3) (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} γ _inst_3) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1)) (TopologicalSpace.Opens.{u2} γ _inst_3) (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} γ _inst_3) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1) (FrameHom.instFrameHomClassFrameHom.{u2, u1} (TopologicalSpace.Opens.{u2} γ _inst_3) (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} γ _inst_3) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1)))) (TopologicalSpace.Opens.comap.{u1, u2} α γ _inst_1 _inst_3 (ContinuousMap.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f)) U)
Case conversion may be inaccurate. Consider using '#align topological_space.opens.comap_comap TopologicalSpace.Opens.comap_comapₓ'. -/
protected theorem comap_comap (g : C(β, γ)) (f : C(α, β)) (U : Opens γ) :
    comap f (comap g U) = comap (g.comp f) U :=
  rfl
#align topological_space.opens.comap_comap TopologicalSpace.Opens.comap_comap

/- warning: topological_space.opens.comap_injective -> TopologicalSpace.Opens.comap_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : T0Space.{u2} β _inst_2], Function.Injective.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (FrameHom.{u2, u1} (TopologicalSpace.Opens.{u2} β _inst_2) (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u2} β _inst_2) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1)) (TopologicalSpace.Opens.comap.{u1, u2} α β _inst_1 _inst_2)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : T0Space.{u2} β _inst_2], Function.Injective.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (FrameHom.{u2, u1} (TopologicalSpace.Opens.{u2} β _inst_2) (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1)) (TopologicalSpace.Opens.comap.{u1, u2} α β _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align topological_space.opens.comap_injective TopologicalSpace.Opens.comap_injectiveₓ'. -/
theorem comap_injective [T0Space β] : Injective (comap : C(α, β) → FrameHom (Opens β) (Opens α)) :=
  fun f g h =>
  ContinuousMap.ext fun a =>
    Inseparable.eq <|
      inseparable_iff_forall_open.2 fun s hs =>
        have : comap f ⟨s, hs⟩ = comap g ⟨s, hs⟩ := FunLike.congr_fun h ⟨_, hs⟩
        show a ∈ f ⁻¹' s ↔ a ∈ g ⁻¹' s from Set.ext_iff.1 (coe_inj.2 this) a
#align topological_space.opens.comap_injective TopologicalSpace.Opens.comap_injective

/- warning: homeomorph.opens_congr -> Homeomorph.opensCongr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], (Homeomorph.{u1, u2} α β _inst_1 _inst_2) -> (OrderIso.{u1, u2} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.{u2} β _inst_2) (Preorder.toLE.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (SetLike.partialOrder.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)))) (Preorder.toLE.{u2} (TopologicalSpace.Opens.{u2} β _inst_2) (PartialOrder.toPreorder.{u2} (TopologicalSpace.Opens.{u2} β _inst_2) (SetLike.partialOrder.{u2, u2} (TopologicalSpace.Opens.{u2} β _inst_2) β (TopologicalSpace.Opens.setLike.{u2} β _inst_2)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], (Homeomorph.{u1, u2} α β _inst_1 _inst_2) -> (OrderIso.{u1, u2} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.{u2} β _inst_2) (Preorder.toLE.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1))))) (Preorder.toLE.{u2} (TopologicalSpace.Opens.{u2} β _inst_2) (PartialOrder.toPreorder.{u2} (TopologicalSpace.Opens.{u2} β _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u2} (TopologicalSpace.Opens.{u2} β _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u2} (TopologicalSpace.Opens.{u2} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} β _inst_2))))))
Case conversion may be inaccurate. Consider using '#align homeomorph.opens_congr Homeomorph.opensCongrₓ'. -/
/-- A homeomorphism induces an order-preserving equivalence on open sets, by taking comaps. -/
@[simps (config := { fullyApplied := false }) apply]
def Homeomorph.opensCongr (f : α ≃ₜ β) : Opens α ≃o Opens β
    where
  toFun := Opens.comap f.symm.toContinuousMap
  invFun := Opens.comap f.toContinuousMap
  left_inv := by
    intro U
    ext1
    exact f.to_equiv.preimage_symm_preimage _
  right_inv := by
    intro U
    ext1
    exact f.to_equiv.symm_preimage_preimage _
  map_rel_iff' U V := by
    simp only [← SetLike.coe_subset_coe] <;> exact f.symm.surjective.preimage_subset_preimage_iff
#align homeomorph.opens_congr Homeomorph.opensCongr

/- warning: homeomorph.opens_congr_symm -> Homeomorph.opensCongr_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : Homeomorph.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (OrderIso.{u2, u1} (TopologicalSpace.Opens.{u2} β _inst_2) (TopologicalSpace.Opens.{u1} α _inst_1) (Preorder.toLE.{u2} (TopologicalSpace.Opens.{u2} β _inst_2) (PartialOrder.toPreorder.{u2} (TopologicalSpace.Opens.{u2} β _inst_2) (SetLike.partialOrder.{u2, u2} (TopologicalSpace.Opens.{u2} β _inst_2) β (TopologicalSpace.Opens.setLike.{u2} β _inst_2)))) (Preorder.toLE.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (SetLike.partialOrder.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1))))) (OrderIso.symm.{u1, u2} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.{u2} β _inst_2) (Preorder.toLE.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (SetLike.partialOrder.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)))) (Preorder.toLE.{u2} (TopologicalSpace.Opens.{u2} β _inst_2) (PartialOrder.toPreorder.{u2} (TopologicalSpace.Opens.{u2} β _inst_2) (SetLike.partialOrder.{u2, u2} (TopologicalSpace.Opens.{u2} β _inst_2) β (TopologicalSpace.Opens.setLike.{u2} β _inst_2)))) (Homeomorph.opensCongr.{u1, u2} α β _inst_1 _inst_2 f)) (Homeomorph.opensCongr.{u2, u1} β α _inst_2 _inst_1 (Homeomorph.symm.{u1, u2} α β _inst_1 _inst_2 f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (f : Homeomorph.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (OrderIso.{u1, u2} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.{u2} α _inst_1) (Preorder.toLE.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} β _inst_2))))) (Preorder.toLE.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (PartialOrder.toPreorder.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} α _inst_1)))))) (OrderIso.symm.{u2, u1} (TopologicalSpace.Opens.{u2} α _inst_1) (TopologicalSpace.Opens.{u1} β _inst_2) (Preorder.toLE.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (PartialOrder.toPreorder.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u2} (TopologicalSpace.Opens.{u2} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u2} α _inst_1))))) (Preorder.toLE.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u1} (TopologicalSpace.Opens.{u1} β _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} β _inst_2))))) (Homeomorph.opensCongr.{u2, u1} α β _inst_1 _inst_2 f)) (Homeomorph.opensCongr.{u1, u2} β α _inst_2 _inst_1 (Homeomorph.symm.{u2, u1} α β _inst_1 _inst_2 f))
Case conversion may be inaccurate. Consider using '#align homeomorph.opens_congr_symm Homeomorph.opensCongr_symmₓ'. -/
@[simp]
theorem Homeomorph.opensCongr_symm (f : α ≃ₜ β) : f.opensCongr.symm = f.symm.opensCongr :=
  rfl
#align homeomorph.opens_congr_symm Homeomorph.opensCongr_symm

instance [Finite α] : Finite (Opens α) :=
  Finite.of_injective _ SetLike.coe_injective

end Opens

#print TopologicalSpace.OpenNhdsOf /-
/-- The open neighborhoods of a point. See also `opens` or `nhds`. -/
structure OpenNhdsOf (x : α) extends Opens α where
  mem' : x ∈ carrier
#align topological_space.open_nhds_of TopologicalSpace.OpenNhdsOf
-/

namespace OpenNhdsOf

variable {x : α}

#print TopologicalSpace.OpenNhdsOf.toOpens_injective /-
theorem toOpens_injective : Injective (toOpens : OpenNhdsOf x → Opens α)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl
#align topological_space.open_nhds_of.to_opens_injective TopologicalSpace.OpenNhdsOf.toOpens_injective
-/

instance : SetLike (OpenNhdsOf x) α where
  coe U := U.1
  coe_injective' := SetLike.coe_injective.comp toOpens_injective

#print TopologicalSpace.OpenNhdsOf.canLiftSet /-
instance canLiftSet : CanLift (Set α) (OpenNhdsOf x) coe fun s => IsOpen s ∧ x ∈ s :=
  ⟨fun s hs => ⟨⟨⟨s, hs.1⟩, hs.2⟩, rfl⟩⟩
#align topological_space.open_nhds_of.can_lift_set TopologicalSpace.OpenNhdsOf.canLiftSet
-/

#print TopologicalSpace.OpenNhdsOf.mem /-
protected theorem mem (U : OpenNhdsOf x) : x ∈ U :=
  U.mem'
#align topological_space.open_nhds_of.mem TopologicalSpace.OpenNhdsOf.mem
-/

#print TopologicalSpace.OpenNhdsOf.isOpen /-
protected theorem isOpen (U : OpenNhdsOf x) : IsOpen (U : Set α) :=
  U.is_open'
#align topological_space.open_nhds_of.is_open TopologicalSpace.OpenNhdsOf.isOpen
-/

instance : OrderTop (OpenNhdsOf x)
    where
  top := ⟨⊤, Set.mem_univ _⟩
  le_top _ := subset_univ _

instance : Inhabited (OpenNhdsOf x) :=
  ⟨⊤⟩

instance : HasInf (OpenNhdsOf x) :=
  ⟨fun U V => ⟨U.1 ⊓ V.1, U.2, V.2⟩⟩

instance : HasSup (OpenNhdsOf x) :=
  ⟨fun U V => ⟨U.1 ⊔ V.1, Or.inl U.2⟩⟩

instance : DistribLattice (OpenNhdsOf x) :=
  toOpens_injective.DistribLattice _ (fun _ _ => rfl) fun _ _ => rfl

#print TopologicalSpace.OpenNhdsOf.basis_nhds /-
theorem basis_nhds : (𝓝 x).HasBasis (fun U : OpenNhdsOf x => True) coe :=
  (nhds_basis_opens x).to_hasBasis (fun U hU => ⟨⟨⟨U, hU.2⟩, hU.1⟩, trivial, Subset.rfl⟩) fun U _ =>
    ⟨U, ⟨⟨U.Mem, U.IsOpen⟩, Subset.rfl⟩⟩
#align topological_space.open_nhds_of.basis_nhds TopologicalSpace.OpenNhdsOf.basis_nhds
-/

/- warning: topological_space.open_nhds_of.comap -> TopologicalSpace.OpenNhdsOf.comap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (x : α), LatticeHom.{u2, u1} (TopologicalSpace.OpenNhdsOf.{u2} β _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f x)) (TopologicalSpace.OpenNhdsOf.{u1} α _inst_1 x) (DistribLattice.toLattice.{u2} (TopologicalSpace.OpenNhdsOf.{u2} β _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f x)) (TopologicalSpace.OpenNhdsOf.distribLattice.{u2} β _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f x))) (DistribLattice.toLattice.{u1} (TopologicalSpace.OpenNhdsOf.{u1} α _inst_1 x) (TopologicalSpace.OpenNhdsOf.distribLattice.{u1} α _inst_1 x))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (x : α), LatticeHom.{u2, u1} (TopologicalSpace.OpenNhdsOf.{u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) _inst_2 (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) f x)) (TopologicalSpace.OpenNhdsOf.{u1} α _inst_1 x) (DistribLattice.toLattice.{u2} (TopologicalSpace.OpenNhdsOf.{u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) _inst_2 (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) f x)) (TopologicalSpace.OpenNhdsOf.instDistribLatticeOpenNhdsOf.{u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) _inst_2 (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) f x))) (DistribLattice.toLattice.{u1} (TopologicalSpace.OpenNhdsOf.{u1} α _inst_1 x) (TopologicalSpace.OpenNhdsOf.instDistribLatticeOpenNhdsOf.{u1} α _inst_1 x))
Case conversion may be inaccurate. Consider using '#align topological_space.open_nhds_of.comap TopologicalSpace.OpenNhdsOf.comapₓ'. -/
/-- Preimage of an open neighborhood of `f x` under a continuous map `f` as a `lattice_hom`. -/
def comap (f : C(α, β)) (x : α) : LatticeHom (OpenNhdsOf (f x)) (OpenNhdsOf x)
    where
  toFun U := ⟨Opens.comap f U.1, U.Mem⟩
  map_sup' U V := rfl
  map_inf' U V := rfl
#align topological_space.open_nhds_of.comap TopologicalSpace.OpenNhdsOf.comap

end OpenNhdsOf

end TopologicalSpace

namespace Tactic

namespace AutoCases

/-- Find an `auto_cases_tac` which matches `topological_space.opens`. -/
unsafe def opens_find_tac : expr → Option auto_cases_tac
  | q(TopologicalSpace.Opens _) => tac_cases
  | _ => none
#align tactic.auto_cases.opens_find_tac tactic.auto_cases.opens_find_tac

end AutoCases

/-- A version of `tactic.auto_cases` that works for `topological_space.opens`. -/
@[hint_tactic]
unsafe def auto_cases_opens : tactic String :=
  auto_cases tactic.auto_cases.opens_find_tac
#align tactic.auto_cases_opens tactic.auto_cases_opens

end Tactic

