/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies

! This file was ported from Lean 3 source module topology.sets.closeds
! leanprover-community/mathlib commit 28aa996fc6fb4317f0083c4e6daf79878d81be33
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Sets.Opens

/-!
# Closed sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define a few types of closed sets in a topological space.

## Main Definitions

For a topological space `α`,
* `closeds α`: The type of closed sets.
* `clopens α`: The type of clopen sets.
-/


open Order OrderDual Set

variable {ι α β : Type _} [TopologicalSpace α] [TopologicalSpace β]

namespace TopologicalSpace

/-! ### Closed sets -/


#print TopologicalSpace.Closeds /-
/-- The type of closed subsets of a topological space. -/
structure Closeds (α : Type _) [TopologicalSpace α] where
  carrier : Set α
  closed' : IsClosed carrier
#align topological_space.closeds TopologicalSpace.Closeds
-/

namespace Closeds

variable {α}

instance : SetLike (Closeds α) α where
  coe := Closeds.carrier
  coe_injective' s t h := by
    cases s
    cases t
    congr

#print TopologicalSpace.Closeds.closed /-
theorem closed (s : Closeds α) : IsClosed (s : Set α) :=
  s.closed'
#align topological_space.closeds.closed TopologicalSpace.Closeds.closed
-/

#print TopologicalSpace.Closeds.ext /-
@[ext]
protected theorem ext {s t : Closeds α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h
#align topological_space.closeds.ext TopologicalSpace.Closeds.ext
-/

#print TopologicalSpace.Closeds.coe_mk /-
@[simp]
theorem coe_mk (s : Set α) (h) : (mk s h : Set α) = s :=
  rfl
#align topological_space.closeds.coe_mk TopologicalSpace.Closeds.coe_mk
-/

#print TopologicalSpace.Closeds.closure /-
/-- The closure of a set, as an element of `closeds`. -/
protected def closure (s : Set α) : Closeds α :=
  ⟨closure s, isClosed_closure⟩
#align topological_space.closeds.closure TopologicalSpace.Closeds.closure
-/

/- warning: topological_space.closeds.gc -> TopologicalSpace.Closeds.gc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α], GaloisConnection.{u1, u1} (Set.{u1} α) (TopologicalSpace.Closeds.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (SetLike.partialOrder.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.setLike.{u1} α _inst_1))) (TopologicalSpace.Closeds.closure.{u1} α _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.setLike.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α], GaloisConnection.{u1, u1} (Set.{u1} α) (TopologicalSpace.Closeds.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (SetLike.instPartialOrder.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.instSetLikeCloseds.{u1} α _inst_1))) (TopologicalSpace.Closeds.closure.{u1} α _inst_1) (SetLike.coe.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.instSetLikeCloseds.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align topological_space.closeds.gc TopologicalSpace.Closeds.gcₓ'. -/
theorem gc : GaloisConnection Closeds.closure (coe : Closeds α → Set α) := fun s U =>
  ⟨subset_closure.trans, fun h => closure_minimal h U.closed⟩
#align topological_space.closeds.gc TopologicalSpace.Closeds.gc

/- warning: topological_space.closeds.gi -> TopologicalSpace.Closeds.gi is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α], GaloisInsertion.{u1, u1} (Set.{u1} α) (TopologicalSpace.Closeds.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (SetLike.partialOrder.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.setLike.{u1} α _inst_1))) (TopologicalSpace.Closeds.closure.{u1} α _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.setLike.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α], GaloisInsertion.{u1, u1} (Set.{u1} α) (TopologicalSpace.Closeds.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (SetLike.instPartialOrder.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.instSetLikeCloseds.{u1} α _inst_1))) (TopologicalSpace.Closeds.closure.{u1} α _inst_1) (SetLike.coe.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.instSetLikeCloseds.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align topological_space.closeds.gi TopologicalSpace.Closeds.giₓ'. -/
/-- The galois coinsertion between sets and opens. -/
def gi : GaloisInsertion (@Closeds.closure α _) coe
    where
  choice s hs := ⟨s, closure_eq_iff_isClosed.1 <| hs.antisymm subset_closure⟩
  gc := gc
  le_l_u _ := subset_closure
  choice_eq s hs := SetLike.coe_injective <| subset_closure.antisymm hs
#align topological_space.closeds.gi TopologicalSpace.Closeds.gi

instance : CompleteLattice (Closeds α) :=
  CompleteLattice.copy
    (GaloisInsertion.liftCompleteLattice gi)-- le
    _
    rfl-- top
    ⟨univ, isClosed_univ⟩
    rfl-- bot
    ⟨∅, isClosed_empty⟩
    (SetLike.coe_injective closure_empty.symm)
    (-- sup
    fun s t => ⟨s ∪ t, s.2.union t.2⟩)
    (funext fun s => funext fun t => SetLike.coe_injective (s.2.union t.2).closure_eq.symm)
    (-- inf
    fun s t => ⟨s ∩ t, s.2.inter t.2⟩)
    rfl-- Sup
    _
    rfl
    (-- Inf
    fun S => ⟨⋂ s ∈ S, ↑s, isClosed_binterᵢ fun s _ => s.2⟩)
    (funext fun S => SetLike.coe_injective infₛ_image.symm)

/-- The type of closed sets is inhabited, with default element the empty set. -/
instance : Inhabited (Closeds α) :=
  ⟨⊥⟩

/- warning: topological_space.closeds.coe_sup -> TopologicalSpace.Closeds.coe_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : TopologicalSpace.Closeds.{u1} α _inst_1) (t : TopologicalSpace.Closeds.{u1} α _inst_1), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.setLike.{u1} α _inst_1)))) (HasSup.sup.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (SemilatticeSup.toHasSup.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Lattice.toSemilatticeSup.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (TopologicalSpace.Closeds.completeLattice.{u1} α _inst_1))))) s t)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.setLike.{u1} α _inst_1)))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.setLike.{u1} α _inst_1)))) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : TopologicalSpace.Closeds.{u1} α _inst_1) (t : TopologicalSpace.Closeds.{u1} α _inst_1), Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.instSetLikeCloseds.{u1} α _inst_1) (HasSup.sup.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (SemilatticeSup.toHasSup.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Lattice.toSemilatticeSup.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (TopologicalSpace.Closeds.instCompleteLatticeCloseds.{u1} α _inst_1))))) s t)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.instSetLikeCloseds.{u1} α _inst_1) s) (SetLike.coe.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.instSetLikeCloseds.{u1} α _inst_1) t))
Case conversion may be inaccurate. Consider using '#align topological_space.closeds.coe_sup TopologicalSpace.Closeds.coe_supₓ'. -/
@[simp, norm_cast]
theorem coe_sup (s t : Closeds α) : (↑(s ⊔ t) : Set α) = s ∪ t :=
  rfl
#align topological_space.closeds.coe_sup TopologicalSpace.Closeds.coe_sup

/- warning: topological_space.closeds.coe_inf -> TopologicalSpace.Closeds.coe_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : TopologicalSpace.Closeds.{u1} α _inst_1) (t : TopologicalSpace.Closeds.{u1} α _inst_1), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.setLike.{u1} α _inst_1)))) (HasInf.inf.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (SemilatticeInf.toHasInf.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Lattice.toSemilatticeInf.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (TopologicalSpace.Closeds.completeLattice.{u1} α _inst_1))))) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.setLike.{u1} α _inst_1)))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.setLike.{u1} α _inst_1)))) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : TopologicalSpace.Closeds.{u1} α _inst_1) (t : TopologicalSpace.Closeds.{u1} α _inst_1), Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.instSetLikeCloseds.{u1} α _inst_1) (HasInf.inf.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Lattice.toHasInf.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (TopologicalSpace.Closeds.instCompleteLatticeCloseds.{u1} α _inst_1)))) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.instSetLikeCloseds.{u1} α _inst_1) s) (SetLike.coe.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.instSetLikeCloseds.{u1} α _inst_1) t))
Case conversion may be inaccurate. Consider using '#align topological_space.closeds.coe_inf TopologicalSpace.Closeds.coe_infₓ'. -/
@[simp, norm_cast]
theorem coe_inf (s t : Closeds α) : (↑(s ⊓ t) : Set α) = s ∩ t :=
  rfl
#align topological_space.closeds.coe_inf TopologicalSpace.Closeds.coe_inf

/- warning: topological_space.closeds.coe_top -> TopologicalSpace.Closeds.coe_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α], Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.setLike.{u1} α _inst_1)))) (Top.top.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (CompleteLattice.toHasTop.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (TopologicalSpace.Closeds.completeLattice.{u1} α _inst_1)))) (Set.univ.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α], Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.instSetLikeCloseds.{u1} α _inst_1) (Top.top.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (CompleteLattice.toTop.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (TopologicalSpace.Closeds.instCompleteLatticeCloseds.{u1} α _inst_1)))) (Set.univ.{u1} α)
Case conversion may be inaccurate. Consider using '#align topological_space.closeds.coe_top TopologicalSpace.Closeds.coe_topₓ'. -/
@[simp, norm_cast]
theorem coe_top : (↑(⊤ : Closeds α) : Set α) = univ :=
  rfl
#align topological_space.closeds.coe_top TopologicalSpace.Closeds.coe_top

/- warning: topological_space.closeds.coe_bot -> TopologicalSpace.Closeds.coe_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α], Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.setLike.{u1} α _inst_1)))) (Bot.bot.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (CompleteLattice.toHasBot.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (TopologicalSpace.Closeds.completeLattice.{u1} α _inst_1)))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α], Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.instSetLikeCloseds.{u1} α _inst_1) (Bot.bot.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (CompleteLattice.toBot.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (TopologicalSpace.Closeds.instCompleteLatticeCloseds.{u1} α _inst_1)))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))
Case conversion may be inaccurate. Consider using '#align topological_space.closeds.coe_bot TopologicalSpace.Closeds.coe_botₓ'. -/
@[simp, norm_cast]
theorem coe_bot : (↑(⊥ : Closeds α) : Set α) = ∅ :=
  rfl
#align topological_space.closeds.coe_bot TopologicalSpace.Closeds.coe_bot

/- warning: topological_space.closeds.coe_Inf -> TopologicalSpace.Closeds.coe_infₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {S : Set.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1)}, Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.setLike.{u1} α _inst_1)))) (InfSet.infₛ.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (ConditionallyCompleteLattice.toHasInf.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (TopologicalSpace.Closeds.completeLattice.{u1} α _inst_1))) S)) (Set.interᵢ.{u1, succ u1} α (TopologicalSpace.Closeds.{u1} α _inst_1) (fun (i : TopologicalSpace.Closeds.{u1} α _inst_1) => Set.interᵢ.{u1, 0} α (Membership.Mem.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1)) (Set.hasMem.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1)) i S) (fun (H : Membership.Mem.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1)) (Set.hasMem.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1)) i S) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.setLike.{u1} α _inst_1)))) i)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {S : Set.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1)}, Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.instSetLikeCloseds.{u1} α _inst_1) (InfSet.infₛ.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (ConditionallyCompleteLattice.toInfSet.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (TopologicalSpace.Closeds.instCompleteLatticeCloseds.{u1} α _inst_1))) S)) (Set.interᵢ.{u1, succ u1} α (TopologicalSpace.Closeds.{u1} α _inst_1) (fun (i : TopologicalSpace.Closeds.{u1} α _inst_1) => Set.interᵢ.{u1, 0} α (Membership.mem.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1)) (Set.instMembershipSet.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1)) i S) (fun (H : Membership.mem.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1)) (Set.instMembershipSet.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1)) i S) => SetLike.coe.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.instSetLikeCloseds.{u1} α _inst_1) i)))
Case conversion may be inaccurate. Consider using '#align topological_space.closeds.coe_Inf TopologicalSpace.Closeds.coe_infₛₓ'. -/
@[simp, norm_cast]
theorem coe_infₛ {S : Set (Closeds α)} : (↑(infₛ S) : Set α) = ⋂ i ∈ S, ↑i :=
  rfl
#align topological_space.closeds.coe_Inf TopologicalSpace.Closeds.coe_infₛ

/- warning: topological_space.closeds.coe_finset_sup -> TopologicalSpace.Closeds.coe_finset_sup is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] (f : ι -> (TopologicalSpace.Closeds.{u2} α _inst_1)) (s : Finset.{u1} ι), Eq.{succ u2} (Set.{u2} α) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (TopologicalSpace.Closeds.{u2} α _inst_1) (Set.{u2} α) (HasLiftT.mk.{succ u2, succ u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (Set.{u2} α) (CoeTCₓ.coe.{succ u2, succ u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (Set.{u2} α) (SetLike.Set.hasCoeT.{u2, u2} (TopologicalSpace.Closeds.{u2} α _inst_1) α (TopologicalSpace.Closeds.setLike.{u2} α _inst_1)))) (Finset.sup.{u2, u1} (TopologicalSpace.Closeds.{u2} α _inst_1) ι (Lattice.toSemilatticeSup.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (ConditionallyCompleteLattice.toLattice.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (TopologicalSpace.Closeds.completeLattice.{u2} α _inst_1)))) (BoundedOrder.toOrderBot.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (Preorder.toLE.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (PartialOrder.toPreorder.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (SemilatticeSup.toPartialOrder.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (Lattice.toSemilatticeSup.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (ConditionallyCompleteLattice.toLattice.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (TopologicalSpace.Closeds.completeLattice.{u2} α _inst_1))))))) (CompleteLattice.toBoundedOrder.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (TopologicalSpace.Closeds.completeLattice.{u2} α _inst_1))) s f)) (Finset.sup.{u2, u1} (Set.{u2} α) ι (Lattice.toSemilatticeSup.{u2} (Set.{u2} α) (ConditionallyCompleteLattice.toLattice.{u2} (Set.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.completeBooleanAlgebra.{u2} α))))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} α) (Set.booleanAlgebra.{u2} α))) s (Function.comp.{succ u1, succ u2, succ u2} ι (TopologicalSpace.Closeds.{u2} α _inst_1) (Set.{u2} α) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (TopologicalSpace.Closeds.{u2} α _inst_1) (Set.{u2} α) (HasLiftT.mk.{succ u2, succ u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (Set.{u2} α) (CoeTCₓ.coe.{succ u2, succ u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (Set.{u2} α) (SetLike.Set.hasCoeT.{u2, u2} (TopologicalSpace.Closeds.{u2} α _inst_1) α (TopologicalSpace.Closeds.setLike.{u2} α _inst_1))))) f))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] (f : ι -> (TopologicalSpace.Closeds.{u2} α _inst_1)) (s : Finset.{u1} ι), Eq.{succ u2} (Set.{u2} α) (SetLike.coe.{u2, u2} (TopologicalSpace.Closeds.{u2} α _inst_1) α (TopologicalSpace.Closeds.instSetLikeCloseds.{u2} α _inst_1) (Finset.sup.{u2, u1} (TopologicalSpace.Closeds.{u2} α _inst_1) ι (Lattice.toSemilatticeSup.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (ConditionallyCompleteLattice.toLattice.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (TopologicalSpace.Closeds.instCompleteLatticeCloseds.{u2} α _inst_1)))) (BoundedOrder.toOrderBot.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (Preorder.toLE.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (PartialOrder.toPreorder.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (SemilatticeSup.toPartialOrder.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (Lattice.toSemilatticeSup.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (ConditionallyCompleteLattice.toLattice.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (TopologicalSpace.Closeds.instCompleteLatticeCloseds.{u2} α _inst_1))))))) (CompleteLattice.toBoundedOrder.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (TopologicalSpace.Closeds.instCompleteLatticeCloseds.{u2} α _inst_1))) s f)) (Finset.sup.{u2, u1} (Set.{u2} α) ι (Lattice.toSemilatticeSup.{u2} (Set.{u2} α) (ConditionallyCompleteLattice.toLattice.{u2} (Set.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (SemilatticeSup.toPartialOrder.{u2} (Set.{u2} α) (Lattice.toSemilatticeSup.{u2} (Set.{u2} α) (ConditionallyCompleteLattice.toLattice.{u2} (Set.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) s (Function.comp.{succ u1, succ u2, succ u2} ι (TopologicalSpace.Closeds.{u2} α _inst_1) (Set.{u2} α) (SetLike.coe.{u2, u2} (TopologicalSpace.Closeds.{u2} α _inst_1) α (TopologicalSpace.Closeds.instSetLikeCloseds.{u2} α _inst_1)) f))
Case conversion may be inaccurate. Consider using '#align topological_space.closeds.coe_finset_sup TopologicalSpace.Closeds.coe_finset_supₓ'. -/
@[simp, norm_cast]
theorem coe_finset_sup (f : ι → Closeds α) (s : Finset ι) :
    (↑(s.sup f) : Set α) = s.sup (coe ∘ f) :=
  map_finset_sup (⟨⟨coe, coe_sup⟩, coe_bot⟩ : SupBotHom (Closeds α) (Set α)) _ _
#align topological_space.closeds.coe_finset_sup TopologicalSpace.Closeds.coe_finset_sup

/- warning: topological_space.closeds.coe_finset_inf -> TopologicalSpace.Closeds.coe_finset_inf is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] (f : ι -> (TopologicalSpace.Closeds.{u2} α _inst_1)) (s : Finset.{u1} ι), Eq.{succ u2} (Set.{u2} α) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (TopologicalSpace.Closeds.{u2} α _inst_1) (Set.{u2} α) (HasLiftT.mk.{succ u2, succ u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (Set.{u2} α) (CoeTCₓ.coe.{succ u2, succ u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (Set.{u2} α) (SetLike.Set.hasCoeT.{u2, u2} (TopologicalSpace.Closeds.{u2} α _inst_1) α (TopologicalSpace.Closeds.setLike.{u2} α _inst_1)))) (Finset.inf.{u2, u1} (TopologicalSpace.Closeds.{u2} α _inst_1) ι (Lattice.toSemilatticeInf.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (ConditionallyCompleteLattice.toLattice.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (TopologicalSpace.Closeds.completeLattice.{u2} α _inst_1)))) (BoundedOrder.toOrderTop.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (Preorder.toLE.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (PartialOrder.toPreorder.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (SemilatticeInf.toPartialOrder.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (Lattice.toSemilatticeInf.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (ConditionallyCompleteLattice.toLattice.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (TopologicalSpace.Closeds.completeLattice.{u2} α _inst_1))))))) (CompleteLattice.toBoundedOrder.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (TopologicalSpace.Closeds.completeLattice.{u2} α _inst_1))) s f)) (Finset.inf.{u2, u1} (Set.{u2} α) ι (Lattice.toSemilatticeInf.{u2} (Set.{u2} α) (ConditionallyCompleteLattice.toLattice.{u2} (Set.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.completeBooleanAlgebra.{u2} α))))))) (Set.orderTop.{u2} α) s (Function.comp.{succ u1, succ u2, succ u2} ι (TopologicalSpace.Closeds.{u2} α _inst_1) (Set.{u2} α) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (TopologicalSpace.Closeds.{u2} α _inst_1) (Set.{u2} α) (HasLiftT.mk.{succ u2, succ u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (Set.{u2} α) (CoeTCₓ.coe.{succ u2, succ u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (Set.{u2} α) (SetLike.Set.hasCoeT.{u2, u2} (TopologicalSpace.Closeds.{u2} α _inst_1) α (TopologicalSpace.Closeds.setLike.{u2} α _inst_1))))) f))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] (f : ι -> (TopologicalSpace.Closeds.{u2} α _inst_1)) (s : Finset.{u1} ι), Eq.{succ u2} (Set.{u2} α) (SetLike.coe.{u2, u2} (TopologicalSpace.Closeds.{u2} α _inst_1) α (TopologicalSpace.Closeds.instSetLikeCloseds.{u2} α _inst_1) (Finset.inf.{u2, u1} (TopologicalSpace.Closeds.{u2} α _inst_1) ι (Lattice.toSemilatticeInf.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (ConditionallyCompleteLattice.toLattice.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (TopologicalSpace.Closeds.instCompleteLatticeCloseds.{u2} α _inst_1)))) (BoundedOrder.toOrderTop.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (Preorder.toLE.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (PartialOrder.toPreorder.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (SemilatticeInf.toPartialOrder.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (Lattice.toSemilatticeInf.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (ConditionallyCompleteLattice.toLattice.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (TopologicalSpace.Closeds.instCompleteLatticeCloseds.{u2} α _inst_1))))))) (CompleteLattice.toBoundedOrder.{u2} (TopologicalSpace.Closeds.{u2} α _inst_1) (TopologicalSpace.Closeds.instCompleteLatticeCloseds.{u2} α _inst_1))) s f)) (Finset.inf.{u2, u1} (Set.{u2} α) ι (Lattice.toSemilatticeInf.{u2} (Set.{u2} α) (ConditionallyCompleteLattice.toLattice.{u2} (Set.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) (Set.instOrderTopSetInstLESet.{u2} α) s (Function.comp.{succ u1, succ u2, succ u2} ι (TopologicalSpace.Closeds.{u2} α _inst_1) (Set.{u2} α) (SetLike.coe.{u2, u2} (TopologicalSpace.Closeds.{u2} α _inst_1) α (TopologicalSpace.Closeds.instSetLikeCloseds.{u2} α _inst_1)) f))
Case conversion may be inaccurate. Consider using '#align topological_space.closeds.coe_finset_inf TopologicalSpace.Closeds.coe_finset_infₓ'. -/
@[simp, norm_cast]
theorem coe_finset_inf (f : ι → Closeds α) (s : Finset ι) :
    (↑(s.inf f) : Set α) = s.inf (coe ∘ f) :=
  map_finset_inf (⟨⟨coe, coe_inf⟩, coe_top⟩ : InfTopHom (Closeds α) (Set α)) _ _
#align topological_space.closeds.coe_finset_inf TopologicalSpace.Closeds.coe_finset_inf

/- warning: topological_space.closeds.infi_def -> TopologicalSpace.Closeds.infᵢ_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Sort.{u2}} (s : ι -> (TopologicalSpace.Closeds.{u1} α _inst_1)), Eq.{succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (infᵢ.{u1, u2} (TopologicalSpace.Closeds.{u1} α _inst_1) (ConditionallyCompleteLattice.toHasInf.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (TopologicalSpace.Closeds.completeLattice.{u1} α _inst_1))) ι (fun (i : ι) => s i)) (TopologicalSpace.Closeds.mk.{u1} α _inst_1 (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.setLike.{u1} α _inst_1)))) (s i))) (isClosed_interᵢ.{u1, u2} α ι _inst_1 (fun (i : ι) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.setLike.{u1} α _inst_1)))) (s i)) (fun (i : ι) => TopologicalSpace.Closeds.closed'.{u1} α _inst_1 (s i))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Sort.{u2}} (s : ι -> (TopologicalSpace.Closeds.{u1} α _inst_1)), Eq.{succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (infᵢ.{u1, u2} (TopologicalSpace.Closeds.{u1} α _inst_1) (ConditionallyCompleteLattice.toInfSet.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (TopologicalSpace.Closeds.instCompleteLatticeCloseds.{u1} α _inst_1))) ι (fun (i : ι) => s i)) (TopologicalSpace.Closeds.mk.{u1} α _inst_1 (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => SetLike.coe.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.instSetLikeCloseds.{u1} α _inst_1) (s i))) (isClosed_interᵢ.{u1, u2} α ι _inst_1 (fun (i : ι) => SetLike.coe.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.instSetLikeCloseds.{u1} α _inst_1) (s i)) (fun (i : ι) => TopologicalSpace.Closeds.closed'.{u1} α _inst_1 (s i))))
Case conversion may be inaccurate. Consider using '#align topological_space.closeds.infi_def TopologicalSpace.Closeds.infᵢ_defₓ'. -/
theorem infᵢ_def {ι} (s : ι → Closeds α) :
    (⨅ i, s i) = ⟨⋂ i, s i, isClosed_interᵢ fun i => (s i).2⟩ :=
  by
  ext
  simp only [infᵢ, coe_Inf, bInter_range]
  rfl
#align topological_space.closeds.infi_def TopologicalSpace.Closeds.infᵢ_def

/- warning: topological_space.closeds.infi_mk -> TopologicalSpace.Closeds.infᵢ_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Sort.{u2}} (s : ι -> (Set.{u1} α)) (h : forall (i : ι), IsClosed.{u1} α _inst_1 (s i)), Eq.{succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (infᵢ.{u1, u2} (TopologicalSpace.Closeds.{u1} α _inst_1) (ConditionallyCompleteLattice.toHasInf.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (TopologicalSpace.Closeds.completeLattice.{u1} α _inst_1))) ι (fun (i : ι) => TopologicalSpace.Closeds.mk.{u1} α _inst_1 (s i) (h i))) (TopologicalSpace.Closeds.mk.{u1} α _inst_1 (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => s i)) (isClosed_interᵢ.{u1, u2} α ι _inst_1 (fun (i : ι) => s i) h))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Sort.{u2}} (s : ι -> (Set.{u1} α)) (h : forall (i : ι), IsClosed.{u1} α _inst_1 (s i)), Eq.{succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (infᵢ.{u1, u2} (TopologicalSpace.Closeds.{u1} α _inst_1) (ConditionallyCompleteLattice.toInfSet.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (TopologicalSpace.Closeds.instCompleteLatticeCloseds.{u1} α _inst_1))) ι (fun (i : ι) => TopologicalSpace.Closeds.mk.{u1} α _inst_1 (s i) (h i))) (TopologicalSpace.Closeds.mk.{u1} α _inst_1 (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => s i)) (isClosed_interᵢ.{u1, u2} α ι _inst_1 (fun (i : ι) => s i) h))
Case conversion may be inaccurate. Consider using '#align topological_space.closeds.infi_mk TopologicalSpace.Closeds.infᵢ_mkₓ'. -/
@[simp]
theorem infᵢ_mk {ι} (s : ι → Set α) (h : ∀ i, IsClosed (s i)) :
    (⨅ i, ⟨s i, h i⟩ : Closeds α) = ⟨⋂ i, s i, isClosed_interᵢ h⟩ := by simp [infi_def]
#align topological_space.closeds.infi_mk TopologicalSpace.Closeds.infᵢ_mk

/- warning: topological_space.closeds.coe_infi -> TopologicalSpace.Closeds.coe_infᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Sort.{u2}} (s : ι -> (TopologicalSpace.Closeds.{u1} α _inst_1)), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.setLike.{u1} α _inst_1)))) (infᵢ.{u1, u2} (TopologicalSpace.Closeds.{u1} α _inst_1) (ConditionallyCompleteLattice.toHasInf.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (TopologicalSpace.Closeds.completeLattice.{u1} α _inst_1))) ι (fun (i : ι) => s i))) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.setLike.{u1} α _inst_1)))) (s i)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Sort.{u2}} (s : ι -> (TopologicalSpace.Closeds.{u1} α _inst_1)), Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.instSetLikeCloseds.{u1} α _inst_1) (infᵢ.{u1, u2} (TopologicalSpace.Closeds.{u1} α _inst_1) (ConditionallyCompleteLattice.toInfSet.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (TopologicalSpace.Closeds.instCompleteLatticeCloseds.{u1} α _inst_1))) ι (fun (i : ι) => s i))) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => SetLike.coe.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.instSetLikeCloseds.{u1} α _inst_1) (s i)))
Case conversion may be inaccurate. Consider using '#align topological_space.closeds.coe_infi TopologicalSpace.Closeds.coe_infᵢₓ'. -/
@[simp, norm_cast]
theorem coe_infᵢ {ι} (s : ι → Closeds α) : ((⨅ i, s i : Closeds α) : Set α) = ⋂ i, s i := by
  simp [infi_def]
#align topological_space.closeds.coe_infi TopologicalSpace.Closeds.coe_infᵢ

/- warning: topological_space.closeds.mem_infi -> TopologicalSpace.Closeds.mem_infᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Sort.{u2}} {x : α} {s : ι -> (TopologicalSpace.Closeds.{u1} α _inst_1)}, Iff (Membership.Mem.{u1, u1} α (TopologicalSpace.Closeds.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.setLike.{u1} α _inst_1)) x (infᵢ.{u1, u2} (TopologicalSpace.Closeds.{u1} α _inst_1) (ConditionallyCompleteLattice.toHasInf.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (TopologicalSpace.Closeds.completeLattice.{u1} α _inst_1))) ι s)) (forall (i : ι), Membership.Mem.{u1, u1} α (TopologicalSpace.Closeds.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.setLike.{u1} α _inst_1)) x (s i))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Sort.{u2}} {x : α} {s : ι -> (TopologicalSpace.Closeds.{u1} α _inst_1)}, Iff (Membership.mem.{u1, u1} α (TopologicalSpace.Closeds.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.instSetLikeCloseds.{u1} α _inst_1)) x (infᵢ.{u1, u2} (TopologicalSpace.Closeds.{u1} α _inst_1) (ConditionallyCompleteLattice.toInfSet.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (TopologicalSpace.Closeds.instCompleteLatticeCloseds.{u1} α _inst_1))) ι s)) (forall (i : ι), Membership.mem.{u1, u1} α (TopologicalSpace.Closeds.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.instSetLikeCloseds.{u1} α _inst_1)) x (s i))
Case conversion may be inaccurate. Consider using '#align topological_space.closeds.mem_infi TopologicalSpace.Closeds.mem_infᵢₓ'. -/
@[simp]
theorem mem_infᵢ {ι} {x : α} {s : ι → Closeds α} : x ∈ infᵢ s ↔ ∀ i, x ∈ s i := by
  simp [← SetLike.mem_coe]
#align topological_space.closeds.mem_infi TopologicalSpace.Closeds.mem_infᵢ

/- warning: topological_space.closeds.mem_Inf -> TopologicalSpace.Closeds.mem_infₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {S : Set.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1)} {x : α}, Iff (Membership.Mem.{u1, u1} α (TopologicalSpace.Closeds.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.setLike.{u1} α _inst_1)) x (InfSet.infₛ.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (ConditionallyCompleteLattice.toHasInf.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (TopologicalSpace.Closeds.completeLattice.{u1} α _inst_1))) S)) (forall (s : TopologicalSpace.Closeds.{u1} α _inst_1), (Membership.Mem.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1)) (Set.hasMem.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1)) s S) -> (Membership.Mem.{u1, u1} α (TopologicalSpace.Closeds.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.setLike.{u1} α _inst_1)) x s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {S : Set.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1)} {x : α}, Iff (Membership.mem.{u1, u1} α (TopologicalSpace.Closeds.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.instSetLikeCloseds.{u1} α _inst_1)) x (InfSet.infₛ.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (ConditionallyCompleteLattice.toInfSet.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (TopologicalSpace.Closeds.instCompleteLatticeCloseds.{u1} α _inst_1))) S)) (forall (s : TopologicalSpace.Closeds.{u1} α _inst_1), (Membership.mem.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Set.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1)) (Set.instMembershipSet.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1)) s S) -> (Membership.mem.{u1, u1} α (TopologicalSpace.Closeds.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.instSetLikeCloseds.{u1} α _inst_1)) x s))
Case conversion may be inaccurate. Consider using '#align topological_space.closeds.mem_Inf TopologicalSpace.Closeds.mem_infₛₓ'. -/
@[simp]
theorem mem_infₛ {S : Set (Closeds α)} {x : α} : x ∈ infₛ S ↔ ∀ s ∈ S, x ∈ s := by
  simp_rw [infₛ_eq_infᵢ, mem_infi]
#align topological_space.closeds.mem_Inf TopologicalSpace.Closeds.mem_infₛ

instance : Coframe (Closeds α) :=
  { Closeds.completeLattice with
    infₛ := infₛ
    infᵢ_sup_le_sup_inf := fun a s =>
      (SetLike.coe_injective <| by simp only [coe_sup, coe_infi, coe_Inf, Set.union_interᵢ₂]).le }

#print TopologicalSpace.Closeds.singleton /-
/-- The term of `closeds α` corresponding to a singleton. -/
@[simps]
def singleton [T1Space α] (x : α) : Closeds α :=
  ⟨{x}, isClosed_singleton⟩
#align topological_space.closeds.singleton TopologicalSpace.Closeds.singleton
-/

end Closeds

#print TopologicalSpace.Closeds.compl /-
/-- The complement of a closed set as an open set. -/
@[simps]
def Closeds.compl (s : Closeds α) : Opens α :=
  ⟨sᶜ, s.2.isOpen_compl⟩
#align topological_space.closeds.compl TopologicalSpace.Closeds.compl
-/

#print TopologicalSpace.Opens.compl /-
/-- The complement of an open set as a closed set. -/
@[simps]
def Opens.compl (s : Opens α) : Closeds α :=
  ⟨sᶜ, s.2.isClosed_compl⟩
#align topological_space.opens.compl TopologicalSpace.Opens.compl
-/

#print TopologicalSpace.Closeds.compl_compl /-
theorem Closeds.compl_compl (s : Closeds α) : s.compl.compl = s :=
  Closeds.ext (compl_compl s)
#align topological_space.closeds.compl_compl TopologicalSpace.Closeds.compl_compl
-/

#print TopologicalSpace.Opens.compl_compl /-
theorem Opens.compl_compl (s : Opens α) : s.compl.compl = s :=
  Opens.ext (compl_compl s)
#align topological_space.opens.compl_compl TopologicalSpace.Opens.compl_compl
-/

#print TopologicalSpace.Closeds.compl_bijective /-
theorem Closeds.compl_bijective : Function.Bijective (@Closeds.compl α _) :=
  Function.bijective_iff_has_inverse.mpr ⟨Opens.compl, Closeds.compl_compl, Opens.compl_compl⟩
#align topological_space.closeds.compl_bijective TopologicalSpace.Closeds.compl_bijective
-/

#print TopologicalSpace.Opens.compl_bijective /-
theorem Opens.compl_bijective : Function.Bijective (@Opens.compl α _) :=
  Function.bijective_iff_has_inverse.mpr ⟨Closeds.compl, Opens.compl_compl, Closeds.compl_compl⟩
#align topological_space.opens.compl_bijective TopologicalSpace.Opens.compl_bijective
-/

variable (α)

/- warning: topological_space.closeds.compl_order_iso -> TopologicalSpace.Closeds.complOrderIso is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} α], OrderIso.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (OrderDual.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)) (Preorder.toLE.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (SetLike.partialOrder.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.setLike.{u1} α _inst_1)))) (OrderDual.hasLe.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Preorder.toLE.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (SetLike.partialOrder.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)))))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} α], OrderIso.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (OrderDual.{u1} (TopologicalSpace.Opens.{u1} α _inst_1)) (Preorder.toLE.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (TopologicalSpace.Closeds.instCompleteLatticeCloseds.{u1} α _inst_1))))) (OrderDual.instLEOrderDual.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Preorder.toLE.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1))))))
Case conversion may be inaccurate. Consider using '#align topological_space.closeds.compl_order_iso TopologicalSpace.Closeds.complOrderIsoₓ'. -/
/-- `closeds.compl` as an `order_iso` to the order dual of `opens α`. -/
@[simps]
def Closeds.complOrderIso : Closeds α ≃o (Opens α)ᵒᵈ
    where
  toFun := OrderDual.toDual ∘ Closeds.compl
  invFun := Opens.compl ∘ OrderDual.ofDual
  left_inv s := by simp [closeds.compl_compl]
  right_inv s := by simp [opens.compl_compl]
  map_rel_iff' s t := by
    simpa only [Equiv.coe_fn_mk, Function.comp_apply, OrderDual.toDual_le_toDual] using
      compl_subset_compl
#align topological_space.closeds.compl_order_iso TopologicalSpace.Closeds.complOrderIso

/- warning: topological_space.opens.compl_order_iso -> TopologicalSpace.Opens.complOrderIso is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} α], OrderIso.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) (OrderDual.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1)) (Preorder.toLE.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (SetLike.partialOrder.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)))) (OrderDual.hasLe.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Preorder.toLE.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (SetLike.partialOrder.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.setLike.{u1} α _inst_1)))))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} α], OrderIso.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) (OrderDual.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1)) (Preorder.toLE.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1))))) (OrderDual.instLEOrderDual.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Preorder.toLE.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (TopologicalSpace.Closeds.instCompleteLatticeCloseds.{u1} α _inst_1))))))
Case conversion may be inaccurate. Consider using '#align topological_space.opens.compl_order_iso TopologicalSpace.Opens.complOrderIsoₓ'. -/
/-- `opens.compl` as an `order_iso` to the order dual of `closeds α`. -/
@[simps]
def Opens.complOrderIso : Opens α ≃o (Closeds α)ᵒᵈ
    where
  toFun := OrderDual.toDual ∘ Opens.compl
  invFun := Closeds.compl ∘ OrderDual.ofDual
  left_inv s := by simp [opens.compl_compl]
  right_inv s := by simp [closeds.compl_compl]
  map_rel_iff' s t := by
    simpa only [Equiv.coe_fn_mk, Function.comp_apply, OrderDual.toDual_le_toDual] using
      compl_subset_compl
#align topological_space.opens.compl_order_iso TopologicalSpace.Opens.complOrderIso

variable {α}

/- warning: topological_space.closeds.is_atom_iff -> TopologicalSpace.Closeds.isAtom_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_3 : T1Space.{u1} α _inst_1] {s : TopologicalSpace.Closeds.{u1} α _inst_1}, Iff (IsAtom.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (SetLike.partialOrder.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.setLike.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Preorder.toLE.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (SetLike.partialOrder.{u1, u1} (TopologicalSpace.Closeds.{u1} α _inst_1) α (TopologicalSpace.Closeds.setLike.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (TopologicalSpace.Closeds.completeLattice.{u1} α _inst_1))) s) (Exists.{succ u1} α (fun (x : α) => Eq.{succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) s (TopologicalSpace.Closeds.singleton.{u1} α _inst_1 _inst_3 x)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_3 : T1Space.{u1} α _inst_1] {s : TopologicalSpace.Closeds.{u1} α _inst_1}, Iff (IsAtom.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (TopologicalSpace.Closeds.instCompleteLatticeCloseds.{u1} α _inst_1)))) (BoundedOrder.toOrderBot.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (Preorder.toLE.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (TopologicalSpace.Closeds.instCompleteLatticeCloseds.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} (TopologicalSpace.Closeds.{u1} α _inst_1) (TopologicalSpace.Closeds.instCompleteLatticeCloseds.{u1} α _inst_1))) s) (Exists.{succ u1} α (fun (x : α) => Eq.{succ u1} (TopologicalSpace.Closeds.{u1} α _inst_1) s (TopologicalSpace.Closeds.singleton.{u1} α _inst_1 _inst_3 x)))
Case conversion may be inaccurate. Consider using '#align topological_space.closeds.is_atom_iff TopologicalSpace.Closeds.isAtom_iffₓ'. -/
/-- in a `t1_space`, atoms of `closeds α` are precisely the `closeds.singleton`s. -/
theorem Closeds.isAtom_iff [T1Space α] {s : Closeds α} : IsAtom s ↔ ∃ x, s = Closeds.singleton x :=
  by
  have : IsAtom (s : Set α) ↔ IsAtom s :=
    by
    refine' closeds.gi.is_atom_iff' rfl (fun t ht => _) s
    obtain ⟨x, rfl⟩ := t.is_atom_iff.mp ht
    exact closure_singleton
  simpa only [← this, (s : Set α).isAtom_iff, SetLike.ext_iff, Set.ext_iff]
#align topological_space.closeds.is_atom_iff TopologicalSpace.Closeds.isAtom_iff

/- warning: topological_space.opens.is_coatom_iff -> TopologicalSpace.Opens.isCoatom_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_3 : T1Space.{u1} α _inst_1] {s : TopologicalSpace.Opens.{u1} α _inst_1}, Iff (IsCoatom.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (SetLike.partialOrder.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1))) (BoundedOrder.toOrderTop.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Preorder.toLE.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (SetLike.partialOrder.{u1, u1} (TopologicalSpace.Opens.{u1} α _inst_1) α (TopologicalSpace.Opens.setLike.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.completeLattice.{u1} α _inst_1))) s) (Exists.{succ u1} α (fun (x : α) => Eq.{succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) s (TopologicalSpace.Closeds.compl.{u1} α _inst_1 (TopologicalSpace.Closeds.singleton.{u1} α _inst_1 _inst_3 x))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_3 : T1Space.{u1} α _inst_1] {s : TopologicalSpace.Opens.{u1} α _inst_1}, Iff (IsCoatom.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1)))) (BoundedOrder.toOrderTop.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (Preorder.toLE.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} (TopologicalSpace.Opens.{u1} α _inst_1) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} α _inst_1))) s) (Exists.{succ u1} α (fun (x : α) => Eq.{succ u1} (TopologicalSpace.Opens.{u1} α _inst_1) s (TopologicalSpace.Closeds.compl.{u1} α _inst_1 (TopologicalSpace.Closeds.singleton.{u1} α _inst_1 _inst_3 x))))
Case conversion may be inaccurate. Consider using '#align topological_space.opens.is_coatom_iff TopologicalSpace.Opens.isCoatom_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr∃ , »((x), _)]] -/
/-- in a `t1_space`, coatoms of `opens α` are precisely complements of singletons:
`(closeds.singleton x).compl`. -/
theorem Opens.isCoatom_iff [T1Space α] {s : Opens α} :
    IsCoatom s ↔ ∃ x, s = (Closeds.singleton x).compl :=
  by
  rw [← s.compl_compl, ← isAtom_dual_iff_isCoatom]
  change IsAtom (closeds.compl_order_iso α s.compl) ↔ _
  rw [(closeds.compl_order_iso α).isAtom_iff, closeds.is_atom_iff]
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr «expr∃ , »((x), _)]]"
  exact closeds.compl_bijective.injective.eq_iff.symm
#align topological_space.opens.is_coatom_iff TopologicalSpace.Opens.isCoatom_iff

/-! ### Clopen sets -/


#print TopologicalSpace.Clopens /-
/-- The type of clopen sets of a topological space. -/
structure Clopens (α : Type _) [TopologicalSpace α] where
  carrier : Set α
  clopen' : IsClopen carrier
#align topological_space.clopens TopologicalSpace.Clopens
-/

namespace Clopens

instance : SetLike (Clopens α) α where
  coe s := s.carrier
  coe_injective' s t h := by
    cases s
    cases t
    congr

#print TopologicalSpace.Clopens.clopen /-
theorem clopen (s : Clopens α) : IsClopen (s : Set α) :=
  s.clopen'
#align topological_space.clopens.clopen TopologicalSpace.Clopens.clopen
-/

#print TopologicalSpace.Clopens.toOpens /-
/-- Reinterpret a compact open as an open. -/
@[simps]
def toOpens (s : Clopens α) : Opens α :=
  ⟨s, s.clopen.IsOpen⟩
#align topological_space.clopens.to_opens TopologicalSpace.Clopens.toOpens
-/

#print TopologicalSpace.Clopens.ext /-
@[ext]
protected theorem ext {s t : Clopens α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h
#align topological_space.clopens.ext TopologicalSpace.Clopens.ext
-/

#print TopologicalSpace.Clopens.coe_mk /-
@[simp]
theorem coe_mk (s : Set α) (h) : (mk s h : Set α) = s :=
  rfl
#align topological_space.clopens.coe_mk TopologicalSpace.Clopens.coe_mk
-/

instance : HasSup (Clopens α) :=
  ⟨fun s t => ⟨s ∪ t, s.clopen.union t.clopen⟩⟩

instance : HasInf (Clopens α) :=
  ⟨fun s t => ⟨s ∩ t, s.clopen.inter t.clopen⟩⟩

instance : Top (Clopens α) :=
  ⟨⟨⊤, isClopen_univ⟩⟩

instance : Bot (Clopens α) :=
  ⟨⟨⊥, isClopen_empty⟩⟩

instance : SDiff (Clopens α) :=
  ⟨fun s t => ⟨s \ t, s.clopen.diffₓ t.clopen⟩⟩

instance : HasCompl (Clopens α) :=
  ⟨fun s => ⟨sᶜ, s.clopen.compl⟩⟩

instance : BooleanAlgebra (Clopens α) :=
  SetLike.coe_injective.BooleanAlgebra _ (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl (fun _ => rfl)
    fun _ _ => rfl

/- warning: topological_space.clopens.coe_sup -> TopologicalSpace.Clopens.coe_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : TopologicalSpace.Clopens.{u1} α _inst_1) (t : TopologicalSpace.Clopens.{u1} α _inst_1), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Clopens.{u1} α _inst_1) α (TopologicalSpace.Clopens.setLike.{u1} α _inst_1)))) (HasSup.sup.{u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (TopologicalSpace.Clopens.hasSup.{u1} α _inst_1) s t)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Clopens.{u1} α _inst_1) α (TopologicalSpace.Clopens.setLike.{u1} α _inst_1)))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Clopens.{u1} α _inst_1) α (TopologicalSpace.Clopens.setLike.{u1} α _inst_1)))) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : TopologicalSpace.Clopens.{u1} α _inst_1) (t : TopologicalSpace.Clopens.{u1} α _inst_1), Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.Clopens.{u1} α _inst_1) α (TopologicalSpace.Clopens.instSetLikeClopens.{u1} α _inst_1) (HasSup.sup.{u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (TopologicalSpace.Clopens.instHasSupClopens.{u1} α _inst_1) s t)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.Clopens.{u1} α _inst_1) α (TopologicalSpace.Clopens.instSetLikeClopens.{u1} α _inst_1) s) (SetLike.coe.{u1, u1} (TopologicalSpace.Clopens.{u1} α _inst_1) α (TopologicalSpace.Clopens.instSetLikeClopens.{u1} α _inst_1) t))
Case conversion may be inaccurate. Consider using '#align topological_space.clopens.coe_sup TopologicalSpace.Clopens.coe_supₓ'. -/
@[simp]
theorem coe_sup (s t : Clopens α) : (↑(s ⊔ t) : Set α) = s ∪ t :=
  rfl
#align topological_space.clopens.coe_sup TopologicalSpace.Clopens.coe_sup

/- warning: topological_space.clopens.coe_inf -> TopologicalSpace.Clopens.coe_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : TopologicalSpace.Clopens.{u1} α _inst_1) (t : TopologicalSpace.Clopens.{u1} α _inst_1), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Clopens.{u1} α _inst_1) α (TopologicalSpace.Clopens.setLike.{u1} α _inst_1)))) (HasInf.inf.{u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (TopologicalSpace.Clopens.hasInf.{u1} α _inst_1) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Clopens.{u1} α _inst_1) α (TopologicalSpace.Clopens.setLike.{u1} α _inst_1)))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Clopens.{u1} α _inst_1) α (TopologicalSpace.Clopens.setLike.{u1} α _inst_1)))) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : TopologicalSpace.Clopens.{u1} α _inst_1) (t : TopologicalSpace.Clopens.{u1} α _inst_1), Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.Clopens.{u1} α _inst_1) α (TopologicalSpace.Clopens.instSetLikeClopens.{u1} α _inst_1) (HasInf.inf.{u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (TopologicalSpace.Clopens.instHasInfClopens.{u1} α _inst_1) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.Clopens.{u1} α _inst_1) α (TopologicalSpace.Clopens.instSetLikeClopens.{u1} α _inst_1) s) (SetLike.coe.{u1, u1} (TopologicalSpace.Clopens.{u1} α _inst_1) α (TopologicalSpace.Clopens.instSetLikeClopens.{u1} α _inst_1) t))
Case conversion may be inaccurate. Consider using '#align topological_space.clopens.coe_inf TopologicalSpace.Clopens.coe_infₓ'. -/
@[simp]
theorem coe_inf (s t : Clopens α) : (↑(s ⊓ t) : Set α) = s ∩ t :=
  rfl
#align topological_space.clopens.coe_inf TopologicalSpace.Clopens.coe_inf

/- warning: topological_space.clopens.coe_top -> TopologicalSpace.Clopens.coe_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α], Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Clopens.{u1} α _inst_1) α (TopologicalSpace.Clopens.setLike.{u1} α _inst_1)))) (Top.top.{u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (TopologicalSpace.Clopens.hasTop.{u1} α _inst_1))) (Set.univ.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α], Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.Clopens.{u1} α _inst_1) α (TopologicalSpace.Clopens.instSetLikeClopens.{u1} α _inst_1) (Top.top.{u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (TopologicalSpace.Clopens.instTopClopens.{u1} α _inst_1))) (Set.univ.{u1} α)
Case conversion may be inaccurate. Consider using '#align topological_space.clopens.coe_top TopologicalSpace.Clopens.coe_topₓ'. -/
@[simp]
theorem coe_top : (↑(⊤ : Clopens α) : Set α) = univ :=
  rfl
#align topological_space.clopens.coe_top TopologicalSpace.Clopens.coe_top

/- warning: topological_space.clopens.coe_bot -> TopologicalSpace.Clopens.coe_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α], Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Clopens.{u1} α _inst_1) α (TopologicalSpace.Clopens.setLike.{u1} α _inst_1)))) (Bot.bot.{u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (TopologicalSpace.Clopens.hasBot.{u1} α _inst_1))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α], Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.Clopens.{u1} α _inst_1) α (TopologicalSpace.Clopens.instSetLikeClopens.{u1} α _inst_1) (Bot.bot.{u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (TopologicalSpace.Clopens.instBotClopens.{u1} α _inst_1))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))
Case conversion may be inaccurate. Consider using '#align topological_space.clopens.coe_bot TopologicalSpace.Clopens.coe_botₓ'. -/
@[simp]
theorem coe_bot : (↑(⊥ : Clopens α) : Set α) = ∅ :=
  rfl
#align topological_space.clopens.coe_bot TopologicalSpace.Clopens.coe_bot

/- warning: topological_space.clopens.coe_sdiff -> TopologicalSpace.Clopens.coe_sdiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : TopologicalSpace.Clopens.{u1} α _inst_1) (t : TopologicalSpace.Clopens.{u1} α _inst_1), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Clopens.{u1} α _inst_1) α (TopologicalSpace.Clopens.setLike.{u1} α _inst_1)))) (SDiff.sdiff.{u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (TopologicalSpace.Clopens.hasSdiff.{u1} α _inst_1) s t)) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Clopens.{u1} α _inst_1) α (TopologicalSpace.Clopens.setLike.{u1} α _inst_1)))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Clopens.{u1} α _inst_1) α (TopologicalSpace.Clopens.setLike.{u1} α _inst_1)))) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : TopologicalSpace.Clopens.{u1} α _inst_1) (t : TopologicalSpace.Clopens.{u1} α _inst_1), Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.Clopens.{u1} α _inst_1) α (TopologicalSpace.Clopens.instSetLikeClopens.{u1} α _inst_1) (SDiff.sdiff.{u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (TopologicalSpace.Clopens.instSDiffClopens.{u1} α _inst_1) s t)) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.Clopens.{u1} α _inst_1) α (TopologicalSpace.Clopens.instSetLikeClopens.{u1} α _inst_1) s) (SetLike.coe.{u1, u1} (TopologicalSpace.Clopens.{u1} α _inst_1) α (TopologicalSpace.Clopens.instSetLikeClopens.{u1} α _inst_1) t))
Case conversion may be inaccurate. Consider using '#align topological_space.clopens.coe_sdiff TopologicalSpace.Clopens.coe_sdiffₓ'. -/
@[simp]
theorem coe_sdiff (s t : Clopens α) : (↑(s \ t) : Set α) = s \ t :=
  rfl
#align topological_space.clopens.coe_sdiff TopologicalSpace.Clopens.coe_sdiff

/- warning: topological_space.clopens.coe_compl -> TopologicalSpace.Clopens.coe_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : TopologicalSpace.Clopens.{u1} α _inst_1), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Clopens.{u1} α _inst_1) α (TopologicalSpace.Clopens.setLike.{u1} α _inst_1)))) (HasCompl.compl.{u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (TopologicalSpace.Clopens.hasCompl.{u1} α _inst_1) s)) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Clopens.{u1} α _inst_1) α (TopologicalSpace.Clopens.setLike.{u1} α _inst_1)))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : TopologicalSpace.Clopens.{u1} α _inst_1), Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.Clopens.{u1} α _inst_1) α (TopologicalSpace.Clopens.instSetLikeClopens.{u1} α _inst_1) (HasCompl.compl.{u1} (TopologicalSpace.Clopens.{u1} α _inst_1) (TopologicalSpace.Clopens.instHasComplClopens.{u1} α _inst_1) s)) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (SetLike.coe.{u1, u1} (TopologicalSpace.Clopens.{u1} α _inst_1) α (TopologicalSpace.Clopens.instSetLikeClopens.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align topological_space.clopens.coe_compl TopologicalSpace.Clopens.coe_complₓ'. -/
@[simp]
theorem coe_compl (s : Clopens α) : (↑(sᶜ) : Set α) = sᶜ :=
  rfl
#align topological_space.clopens.coe_compl TopologicalSpace.Clopens.coe_compl

instance : Inhabited (Clopens α) :=
  ⟨⊥⟩

end Clopens

end TopologicalSpace

