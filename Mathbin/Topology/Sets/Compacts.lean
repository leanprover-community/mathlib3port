/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies

! This file was ported from Lean 3 source module topology.sets.compacts
! leanprover-community/mathlib commit 1ead22342e1a078bd44744ace999f85756555d35
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Sets.Closeds
import Mathbin.Topology.QuasiSeparated

/-!
# Compact sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define a few types of compact sets in a topological space.

## Main Definitions

For a topological space `α`,
* `compacts α`: The type of compact sets.
* `nonempty_compacts α`: The type of non-empty compact sets.
* `positive_compacts α`: The type of compact sets with non-empty interior.
* `compact_opens α`: The type of compact open sets. This is a central object in the study of
  spectral spaces.
-/


open Set

variable {α β : Type _} [TopologicalSpace α] [TopologicalSpace β]

namespace TopologicalSpace

/-! ### Compact sets -/


#print TopologicalSpace.Compacts /-
/-- The type of compact sets of a topological space. -/
structure Compacts (α : Type _) [TopologicalSpace α] where
  carrier : Set α
  is_compact' : IsCompact carrier
#align topological_space.compacts TopologicalSpace.Compacts
-/

namespace Compacts

variable {α}

instance : SetLike (Compacts α) α where
  coe := Compacts.carrier
  coe_injective' s t h := by
    cases s
    cases t
    congr

#print TopologicalSpace.Compacts.isCompact /-
protected theorem isCompact (s : Compacts α) : IsCompact (s : Set α) :=
  s.is_compact'
#align topological_space.compacts.is_compact TopologicalSpace.Compacts.isCompact
-/

instance (K : Compacts α) : CompactSpace K :=
  isCompact_iff_compactSpace.1 K.IsCompact

instance : CanLift (Set α) (Compacts α) coe IsCompact where prf K hK := ⟨⟨K, hK⟩, rfl⟩

#print TopologicalSpace.Compacts.ext /-
@[ext]
protected theorem ext {s t : Compacts α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h
#align topological_space.compacts.ext TopologicalSpace.Compacts.ext
-/

#print TopologicalSpace.Compacts.coe_mk /-
@[simp]
theorem coe_mk (s : Set α) (h) : (mk s h : Set α) = s :=
  rfl
#align topological_space.compacts.coe_mk TopologicalSpace.Compacts.coe_mk
-/

#print TopologicalSpace.Compacts.carrier_eq_coe /-
@[simp]
theorem carrier_eq_coe (s : Compacts α) : s.carrier = s :=
  rfl
#align topological_space.compacts.carrier_eq_coe TopologicalSpace.Compacts.carrier_eq_coe
-/

instance : HasSup (Compacts α) :=
  ⟨fun s t => ⟨s ∪ t, s.IsCompact.union t.IsCompact⟩⟩

instance [T2Space α] : HasInf (Compacts α) :=
  ⟨fun s t => ⟨s ∩ t, s.IsCompact.inter t.IsCompact⟩⟩

instance [CompactSpace α] : Top (Compacts α) :=
  ⟨⟨univ, isCompact_univ⟩⟩

instance : Bot (Compacts α) :=
  ⟨⟨∅, isCompact_empty⟩⟩

instance : SemilatticeSup (Compacts α) :=
  SetLike.coe_injective.SemilatticeSup _ fun _ _ => rfl

instance [T2Space α] : DistribLattice (Compacts α) :=
  SetLike.coe_injective.DistribLattice _ (fun _ _ => rfl) fun _ _ => rfl

instance : OrderBot (Compacts α) :=
  OrderBot.lift (coe : _ → Set α) (fun _ _ => id) rfl

instance [CompactSpace α] : BoundedOrder (Compacts α) :=
  BoundedOrder.lift (coe : _ → Set α) (fun _ _ => id) rfl rfl

/-- The type of compact sets is inhabited, with default element the empty set. -/
instance : Inhabited (Compacts α) :=
  ⟨⊥⟩

/- warning: topological_space.compacts.coe_sup -> TopologicalSpace.Compacts.coe_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : TopologicalSpace.Compacts.{u1} α _inst_1) (t : TopologicalSpace.Compacts.{u1} α _inst_1), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Compacts.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Compacts.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Compacts.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Compacts.{u1} α _inst_1) α (TopologicalSpace.Compacts.setLike.{u1} α _inst_1)))) (HasSup.sup.{u1} (TopologicalSpace.Compacts.{u1} α _inst_1) (TopologicalSpace.Compacts.hasSup.{u1} α _inst_1) s t)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Compacts.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Compacts.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Compacts.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Compacts.{u1} α _inst_1) α (TopologicalSpace.Compacts.setLike.{u1} α _inst_1)))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Compacts.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Compacts.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Compacts.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Compacts.{u1} α _inst_1) α (TopologicalSpace.Compacts.setLike.{u1} α _inst_1)))) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : TopologicalSpace.Compacts.{u1} α _inst_1) (t : TopologicalSpace.Compacts.{u1} α _inst_1), Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.Compacts.{u1} α _inst_1) α (TopologicalSpace.Compacts.instSetLikeCompacts.{u1} α _inst_1) (HasSup.sup.{u1} (TopologicalSpace.Compacts.{u1} α _inst_1) (TopologicalSpace.Compacts.instHasSupCompacts.{u1} α _inst_1) s t)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.Compacts.{u1} α _inst_1) α (TopologicalSpace.Compacts.instSetLikeCompacts.{u1} α _inst_1) s) (SetLike.coe.{u1, u1} (TopologicalSpace.Compacts.{u1} α _inst_1) α (TopologicalSpace.Compacts.instSetLikeCompacts.{u1} α _inst_1) t))
Case conversion may be inaccurate. Consider using '#align topological_space.compacts.coe_sup TopologicalSpace.Compacts.coe_supₓ'. -/
@[simp]
theorem coe_sup (s t : Compacts α) : (↑(s ⊔ t) : Set α) = s ∪ t :=
  rfl
#align topological_space.compacts.coe_sup TopologicalSpace.Compacts.coe_sup

/- warning: topological_space.compacts.coe_inf -> TopologicalSpace.Compacts.coe_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_1] (s : TopologicalSpace.Compacts.{u1} α _inst_1) (t : TopologicalSpace.Compacts.{u1} α _inst_1), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Compacts.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Compacts.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Compacts.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Compacts.{u1} α _inst_1) α (TopologicalSpace.Compacts.setLike.{u1} α _inst_1)))) (HasInf.inf.{u1} (TopologicalSpace.Compacts.{u1} α _inst_1) (TopologicalSpace.Compacts.hasInf.{u1} α _inst_1 _inst_3) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Compacts.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Compacts.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Compacts.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Compacts.{u1} α _inst_1) α (TopologicalSpace.Compacts.setLike.{u1} α _inst_1)))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Compacts.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Compacts.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Compacts.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Compacts.{u1} α _inst_1) α (TopologicalSpace.Compacts.setLike.{u1} α _inst_1)))) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_1] (s : TopologicalSpace.Compacts.{u1} α _inst_1) (t : TopologicalSpace.Compacts.{u1} α _inst_1), Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.Compacts.{u1} α _inst_1) α (TopologicalSpace.Compacts.instSetLikeCompacts.{u1} α _inst_1) (HasInf.inf.{u1} (TopologicalSpace.Compacts.{u1} α _inst_1) (TopologicalSpace.Compacts.instHasInfCompacts.{u1} α _inst_1 _inst_3) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.Compacts.{u1} α _inst_1) α (TopologicalSpace.Compacts.instSetLikeCompacts.{u1} α _inst_1) s) (SetLike.coe.{u1, u1} (TopologicalSpace.Compacts.{u1} α _inst_1) α (TopologicalSpace.Compacts.instSetLikeCompacts.{u1} α _inst_1) t))
Case conversion may be inaccurate. Consider using '#align topological_space.compacts.coe_inf TopologicalSpace.Compacts.coe_infₓ'. -/
@[simp]
theorem coe_inf [T2Space α] (s t : Compacts α) : (↑(s ⊓ t) : Set α) = s ∩ t :=
  rfl
#align topological_space.compacts.coe_inf TopologicalSpace.Compacts.coe_inf

#print TopologicalSpace.Compacts.coe_top /-
@[simp]
theorem coe_top [CompactSpace α] : (↑(⊤ : Compacts α) : Set α) = univ :=
  rfl
#align topological_space.compacts.coe_top TopologicalSpace.Compacts.coe_top
-/

#print TopologicalSpace.Compacts.coe_bot /-
@[simp]
theorem coe_bot : (↑(⊥ : Compacts α) : Set α) = ∅ :=
  rfl
#align topological_space.compacts.coe_bot TopologicalSpace.Compacts.coe_bot
-/

/- warning: topological_space.compacts.coe_finset_sup -> TopologicalSpace.Compacts.coe_finset_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Type.{u2}} {s : Finset.{u2} ι} {f : ι -> (TopologicalSpace.Compacts.{u1} α _inst_1)}, Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Compacts.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Compacts.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Compacts.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Compacts.{u1} α _inst_1) α (TopologicalSpace.Compacts.setLike.{u1} α _inst_1)))) (Finset.sup.{u1, u2} (TopologicalSpace.Compacts.{u1} α _inst_1) ι (TopologicalSpace.Compacts.semilatticeSup.{u1} α _inst_1) (TopologicalSpace.Compacts.orderBot.{u1} α _inst_1) s f)) (Finset.sup.{u1, u2} (Set.{u1} α) ι (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Set.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s (fun (i : ι) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Compacts.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Compacts.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Compacts.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Compacts.{u1} α _inst_1) α (TopologicalSpace.Compacts.setLike.{u1} α _inst_1)))) (f i)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Type.{u2}} {s : Finset.{u2} ι} {f : ι -> (TopologicalSpace.Compacts.{u1} α _inst_1)}, Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.Compacts.{u1} α _inst_1) α (TopologicalSpace.Compacts.instSetLikeCompacts.{u1} α _inst_1) (Finset.sup.{u1, u2} (TopologicalSpace.Compacts.{u1} α _inst_1) ι (TopologicalSpace.Compacts.instSemilatticeSupCompacts.{u1} α _inst_1) (TopologicalSpace.Compacts.instOrderBotCompactsToLEToPreorderToPartialOrderInstSemilatticeSupCompacts.{u1} α _inst_1) s f)) (Finset.sup.{u1, u2} (Set.{u1} α) ι (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Set.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeSup.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Set.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) s (fun (i : ι) => SetLike.coe.{u1, u1} (TopologicalSpace.Compacts.{u1} α _inst_1) α (TopologicalSpace.Compacts.instSetLikeCompacts.{u1} α _inst_1) (f i)))
Case conversion may be inaccurate. Consider using '#align topological_space.compacts.coe_finset_sup TopologicalSpace.Compacts.coe_finset_supₓ'. -/
@[simp]
theorem coe_finset_sup {ι : Type _} {s : Finset ι} {f : ι → Compacts α} :
    (↑(s.sup f) : Set α) = s.sup fun i => f i := by
  classical
    refine' Finset.induction_on s rfl fun a s _ h => _
    simp_rw [Finset.sup_insert, coe_sup, sup_eq_union]
    congr
#align topological_space.compacts.coe_finset_sup TopologicalSpace.Compacts.coe_finset_sup

#print TopologicalSpace.Compacts.map /-
/-- The image of a compact set under a continuous function. -/
protected def map (f : α → β) (hf : Continuous f) (K : Compacts α) : Compacts β :=
  ⟨f '' K.1, K.2.image hf⟩
#align topological_space.compacts.map TopologicalSpace.Compacts.map
-/

/- warning: topological_space.compacts.coe_map -> TopologicalSpace.Compacts.coe_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} (hf : Continuous.{u1, u2} α β _inst_1 _inst_2 f) (s : TopologicalSpace.Compacts.{u1} α _inst_1), Eq.{succ u2} (Set.{u2} β) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (TopologicalSpace.Compacts.{u2} β _inst_2) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (TopologicalSpace.Compacts.{u2} β _inst_2) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (TopologicalSpace.Compacts.{u2} β _inst_2) (Set.{u2} β) (SetLike.Set.hasCoeT.{u2, u2} (TopologicalSpace.Compacts.{u2} β _inst_2) β (TopologicalSpace.Compacts.setLike.{u2} β _inst_2)))) (TopologicalSpace.Compacts.map.{u1, u2} α β _inst_1 _inst_2 f hf s)) (Set.image.{u1, u2} α β f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Compacts.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Compacts.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Compacts.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Compacts.{u1} α _inst_1) α (TopologicalSpace.Compacts.setLike.{u1} α _inst_1)))) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} (hf : Continuous.{u2, u1} α β _inst_1 _inst_2 f) (s : TopologicalSpace.Compacts.{u2} α _inst_1), Eq.{succ u1} (Set.{u1} β) (SetLike.coe.{u1, u1} (TopologicalSpace.Compacts.{u1} β _inst_2) β (TopologicalSpace.Compacts.instSetLikeCompacts.{u1} β _inst_2) (TopologicalSpace.Compacts.map.{u2, u1} α β _inst_1 _inst_2 f hf s)) (Set.image.{u2, u1} α β f (SetLike.coe.{u2, u2} (TopologicalSpace.Compacts.{u2} α _inst_1) α (TopologicalSpace.Compacts.instSetLikeCompacts.{u2} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align topological_space.compacts.coe_map TopologicalSpace.Compacts.coe_mapₓ'. -/
@[simp]
theorem coe_map {f : α → β} (hf : Continuous f) (s : Compacts α) : (s.map f hf : Set β) = f '' s :=
  rfl
#align topological_space.compacts.coe_map TopologicalSpace.Compacts.coe_map

#print TopologicalSpace.Compacts.equiv /-
/-- A homeomorphism induces an equivalence on compact sets, by taking the image. -/
@[simp]
protected def equiv (f : α ≃ₜ β) : Compacts α ≃ Compacts β
    where
  toFun := Compacts.map f f.Continuous
  invFun := Compacts.map _ f.symm.Continuous
  left_inv s := by
    ext1
    simp only [coe_map, ← image_comp, f.symm_comp_self, image_id]
  right_inv s := by
    ext1
    simp only [coe_map, ← image_comp, f.self_comp_symm, image_id]
#align topological_space.compacts.equiv TopologicalSpace.Compacts.equiv
-/

/- warning: topological_space.compacts.equiv_to_fun_val -> TopologicalSpace.Compacts.equiv_to_fun_val is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : Homeomorph.{u1, u2} α β _inst_1 _inst_2) (K : TopologicalSpace.Compacts.{u1} α _inst_1), Eq.{succ u2} (Set.{u2} β) (TopologicalSpace.Compacts.carrier.{u2} β _inst_2 (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} (TopologicalSpace.Compacts.{u1} α _inst_1) (TopologicalSpace.Compacts.{u2} β _inst_2)) (fun (_x : Equiv.{succ u1, succ u2} (TopologicalSpace.Compacts.{u1} α _inst_1) (TopologicalSpace.Compacts.{u2} β _inst_2)) => (TopologicalSpace.Compacts.{u1} α _inst_1) -> (TopologicalSpace.Compacts.{u2} β _inst_2)) (Equiv.hasCoeToFun.{succ u1, succ u2} (TopologicalSpace.Compacts.{u1} α _inst_1) (TopologicalSpace.Compacts.{u2} β _inst_2)) (TopologicalSpace.Compacts.equiv.{u1, u2} α β _inst_1 _inst_2 f) K)) (Set.preimage.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (Homeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : Homeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (Homeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (Homeomorph.symm.{u1, u2} α β _inst_1 _inst_2 f)) (TopologicalSpace.Compacts.carrier.{u1} α _inst_1 K))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (f : Homeomorph.{u2, u1} α β _inst_1 _inst_2) (K : TopologicalSpace.Compacts.{u2} α _inst_1), Eq.{succ u1} (Set.{u1} β) (TopologicalSpace.Compacts.carrier.{u1} β _inst_2 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} (TopologicalSpace.Compacts.{u2} α _inst_1) (TopologicalSpace.Compacts.{u1} β _inst_2)) (TopologicalSpace.Compacts.{u2} α _inst_1) (fun (_x : TopologicalSpace.Compacts.{u2} α _inst_1) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : TopologicalSpace.Compacts.{u2} α _inst_1) => TopologicalSpace.Compacts.{u1} β _inst_2) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u1} (TopologicalSpace.Compacts.{u2} α _inst_1) (TopologicalSpace.Compacts.{u1} β _inst_2)) (TopologicalSpace.Compacts.equiv.{u2, u1} α β _inst_1 _inst_2 f) K)) (Set.preimage.{u1, u2} β α (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (Homeomorph.{u1, u2} β α _inst_2 _inst_1) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (Homeomorph.{u1, u2} β α _inst_2 _inst_1) β α (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (Homeomorph.{u1, u2} β α _inst_2 _inst_1) β α (Homeomorph.instEquivLikeHomeomorph.{u1, u2} β α _inst_2 _inst_1))) (Homeomorph.symm.{u2, u1} α β _inst_1 _inst_2 f)) (TopologicalSpace.Compacts.carrier.{u2} α _inst_1 K))
Case conversion may be inaccurate. Consider using '#align topological_space.compacts.equiv_to_fun_val TopologicalSpace.Compacts.equiv_to_fun_valₓ'. -/
/-- The image of a compact set under a homeomorphism can also be expressed as a preimage. -/
theorem equiv_to_fun_val (f : α ≃ₜ β) (K : Compacts α) : (Compacts.equiv f K).1 = f.symm ⁻¹' K.1 :=
  congr_fun (image_eq_preimage_of_inverse f.left_inv f.right_inv) K.1
#align topological_space.compacts.equiv_to_fun_val TopologicalSpace.Compacts.equiv_to_fun_val

/- warning: topological_space.compacts.prod -> TopologicalSpace.Compacts.prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], (TopologicalSpace.Compacts.{u1} α _inst_1) -> (TopologicalSpace.Compacts.{u2} β _inst_2) -> (TopologicalSpace.Compacts.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], (TopologicalSpace.Compacts.{u1} α _inst_1) -> (TopologicalSpace.Compacts.{u2} β _inst_2) -> (TopologicalSpace.Compacts.{max u2 u1} (Prod.{u1, u2} α β) (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2))
Case conversion may be inaccurate. Consider using '#align topological_space.compacts.prod TopologicalSpace.Compacts.prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The product of two `compacts`, as a `compacts` in the product space. -/
protected def prod (K : Compacts α) (L : Compacts β) : Compacts (α × β)
    where
  carrier := K ×ˢ L
  is_compact' := IsCompact.prod K.2 L.2
#align topological_space.compacts.prod TopologicalSpace.Compacts.prod

/- warning: topological_space.compacts.coe_prod -> TopologicalSpace.Compacts.coe_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (K : TopologicalSpace.Compacts.{u1} α _inst_1) (L : TopologicalSpace.Compacts.{u2} β _inst_2), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) ((fun (a : Type.{max u1 u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ (max u1 u2), succ (max u1 u2)} a b] => self.0) (TopologicalSpace.Compacts.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2)) (Set.{max u1 u2} (Prod.{u1, u2} α β)) (HasLiftT.mk.{succ (max u1 u2), succ (max u1 u2)} (TopologicalSpace.Compacts.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2)) (Set.{max u1 u2} (Prod.{u1, u2} α β)) (CoeTCₓ.coe.{succ (max u1 u2), succ (max u1 u2)} (TopologicalSpace.Compacts.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2)) (Set.{max u1 u2} (Prod.{u1, u2} α β)) (SetLike.Set.hasCoeT.{max u1 u2, max u1 u2} (TopologicalSpace.Compacts.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2)) (Prod.{u1, u2} α β) (TopologicalSpace.Compacts.setLike.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2))))) (TopologicalSpace.Compacts.prod.{u1, u2} α β _inst_1 _inst_2 K L)) (Set.prod.{u1, u2} α β ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Compacts.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Compacts.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Compacts.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Compacts.{u1} α _inst_1) α (TopologicalSpace.Compacts.setLike.{u1} α _inst_1)))) K) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (TopologicalSpace.Compacts.{u2} β _inst_2) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (TopologicalSpace.Compacts.{u2} β _inst_2) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (TopologicalSpace.Compacts.{u2} β _inst_2) (Set.{u2} β) (SetLike.Set.hasCoeT.{u2, u2} (TopologicalSpace.Compacts.{u2} β _inst_2) β (TopologicalSpace.Compacts.setLike.{u2} β _inst_2)))) L))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (K : TopologicalSpace.Compacts.{u2} α _inst_1) (L : TopologicalSpace.Compacts.{u1} β _inst_2), Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (Prod.{u2, u1} α β)) (SetLike.coe.{max u2 u1, max u2 u1} (TopologicalSpace.Compacts.{max u1 u2} (Prod.{u2, u1} α β) (instTopologicalSpaceProd.{u2, u1} α β _inst_1 _inst_2)) (Prod.{u2, u1} α β) (TopologicalSpace.Compacts.instSetLikeCompacts.{max u2 u1} (Prod.{u2, u1} α β) (instTopologicalSpaceProd.{u2, u1} α β _inst_1 _inst_2)) (TopologicalSpace.Compacts.prod.{u2, u1} α β _inst_1 _inst_2 K L)) (Set.prod.{u2, u1} α β (SetLike.coe.{u2, u2} (TopologicalSpace.Compacts.{u2} α _inst_1) α (TopologicalSpace.Compacts.instSetLikeCompacts.{u2} α _inst_1) K) (SetLike.coe.{u1, u1} (TopologicalSpace.Compacts.{u1} β _inst_2) β (TopologicalSpace.Compacts.instSetLikeCompacts.{u1} β _inst_2) L))
Case conversion may be inaccurate. Consider using '#align topological_space.compacts.coe_prod TopologicalSpace.Compacts.coe_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem coe_prod (K : Compacts α) (L : Compacts β) : (K.Prod L : Set (α × β)) = K ×ˢ L :=
  rfl
#align topological_space.compacts.coe_prod TopologicalSpace.Compacts.coe_prod

end Compacts

/-! ### Nonempty compact sets -/


#print TopologicalSpace.NonemptyCompacts /-
/-- The type of nonempty compact sets of a topological space. -/
structure NonemptyCompacts (α : Type _) [TopologicalSpace α] extends Compacts α where
  nonempty' : carrier.Nonempty
#align topological_space.nonempty_compacts TopologicalSpace.NonemptyCompacts
-/

namespace NonemptyCompacts

instance : SetLike (NonemptyCompacts α) α
    where
  coe s := s.carrier
  coe_injective' s t h := by
    obtain ⟨⟨_, _⟩, _⟩ := s
    obtain ⟨⟨_, _⟩, _⟩ := t
    congr

#print TopologicalSpace.NonemptyCompacts.isCompact /-
protected theorem isCompact (s : NonemptyCompacts α) : IsCompact (s : Set α) :=
  s.is_compact'
#align topological_space.nonempty_compacts.is_compact TopologicalSpace.NonemptyCompacts.isCompact
-/

#print TopologicalSpace.NonemptyCompacts.nonempty /-
protected theorem nonempty (s : NonemptyCompacts α) : (s : Set α).Nonempty :=
  s.nonempty'
#align topological_space.nonempty_compacts.nonempty TopologicalSpace.NonemptyCompacts.nonempty
-/

#print TopologicalSpace.NonemptyCompacts.toCloseds /-
/-- Reinterpret a nonempty compact as a closed set. -/
def toCloseds [T2Space α] (s : NonemptyCompacts α) : Closeds α :=
  ⟨s, s.IsCompact.IsClosed⟩
#align topological_space.nonempty_compacts.to_closeds TopologicalSpace.NonemptyCompacts.toCloseds
-/

#print TopologicalSpace.NonemptyCompacts.ext /-
@[ext]
protected theorem ext {s t : NonemptyCompacts α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h
#align topological_space.nonempty_compacts.ext TopologicalSpace.NonemptyCompacts.ext
-/

#print TopologicalSpace.NonemptyCompacts.coe_mk /-
@[simp]
theorem coe_mk (s : Compacts α) (h) : (mk s h : Set α) = s :=
  rfl
#align topological_space.nonempty_compacts.coe_mk TopologicalSpace.NonemptyCompacts.coe_mk
-/

#print TopologicalSpace.NonemptyCompacts.carrier_eq_coe /-
@[simp]
theorem carrier_eq_coe (s : NonemptyCompacts α) : s.carrier = s :=
  rfl
#align topological_space.nonempty_compacts.carrier_eq_coe TopologicalSpace.NonemptyCompacts.carrier_eq_coe
-/

instance : HasSup (NonemptyCompacts α) :=
  ⟨fun s t => ⟨s.toCompacts ⊔ t.toCompacts, s.Nonempty.mono <| subset_union_left _ _⟩⟩

instance [CompactSpace α] [Nonempty α] : Top (NonemptyCompacts α) :=
  ⟨⟨⊤, univ_nonempty⟩⟩

instance : SemilatticeSup (NonemptyCompacts α) :=
  SetLike.coe_injective.SemilatticeSup _ fun _ _ => rfl

instance [CompactSpace α] [Nonempty α] : OrderTop (NonemptyCompacts α) :=
  OrderTop.lift (coe : _ → Set α) (fun _ _ => id) rfl

/- warning: topological_space.nonempty_compacts.coe_sup -> TopologicalSpace.NonemptyCompacts.coe_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : TopologicalSpace.NonemptyCompacts.{u1} α _inst_1) (t : TopologicalSpace.NonemptyCompacts.{u1} α _inst_1), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.NonemptyCompacts.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.NonemptyCompacts.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.NonemptyCompacts.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.NonemptyCompacts.{u1} α _inst_1) α (TopologicalSpace.NonemptyCompacts.setLike.{u1} α _inst_1)))) (HasSup.sup.{u1} (TopologicalSpace.NonemptyCompacts.{u1} α _inst_1) (TopologicalSpace.NonemptyCompacts.hasSup.{u1} α _inst_1) s t)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.NonemptyCompacts.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.NonemptyCompacts.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.NonemptyCompacts.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.NonemptyCompacts.{u1} α _inst_1) α (TopologicalSpace.NonemptyCompacts.setLike.{u1} α _inst_1)))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.NonemptyCompacts.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.NonemptyCompacts.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.NonemptyCompacts.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.NonemptyCompacts.{u1} α _inst_1) α (TopologicalSpace.NonemptyCompacts.setLike.{u1} α _inst_1)))) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : TopologicalSpace.NonemptyCompacts.{u1} α _inst_1) (t : TopologicalSpace.NonemptyCompacts.{u1} α _inst_1), Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.NonemptyCompacts.{u1} α _inst_1) α (TopologicalSpace.NonemptyCompacts.instSetLikeNonemptyCompacts.{u1} α _inst_1) (HasSup.sup.{u1} (TopologicalSpace.NonemptyCompacts.{u1} α _inst_1) (TopologicalSpace.NonemptyCompacts.instHasSupNonemptyCompacts.{u1} α _inst_1) s t)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.NonemptyCompacts.{u1} α _inst_1) α (TopologicalSpace.NonemptyCompacts.instSetLikeNonemptyCompacts.{u1} α _inst_1) s) (SetLike.coe.{u1, u1} (TopologicalSpace.NonemptyCompacts.{u1} α _inst_1) α (TopologicalSpace.NonemptyCompacts.instSetLikeNonemptyCompacts.{u1} α _inst_1) t))
Case conversion may be inaccurate. Consider using '#align topological_space.nonempty_compacts.coe_sup TopologicalSpace.NonemptyCompacts.coe_supₓ'. -/
@[simp]
theorem coe_sup (s t : NonemptyCompacts α) : (↑(s ⊔ t) : Set α) = s ∪ t :=
  rfl
#align topological_space.nonempty_compacts.coe_sup TopologicalSpace.NonemptyCompacts.coe_sup

#print TopologicalSpace.NonemptyCompacts.coe_top /-
@[simp]
theorem coe_top [CompactSpace α] [Nonempty α] : (↑(⊤ : NonemptyCompacts α) : Set α) = univ :=
  rfl
#align topological_space.nonempty_compacts.coe_top TopologicalSpace.NonemptyCompacts.coe_top
-/

/-- In an inhabited space, the type of nonempty compact subsets is also inhabited, with
default element the singleton set containing the default element. -/
instance [Inhabited α] : Inhabited (NonemptyCompacts α) :=
  ⟨{  carrier := {default}
      is_compact' := isCompact_singleton
      nonempty' := singleton_nonempty _ }⟩

#print TopologicalSpace.NonemptyCompacts.toCompactSpace /-
instance toCompactSpace {s : NonemptyCompacts α} : CompactSpace s :=
  isCompact_iff_compactSpace.1 s.IsCompact
#align topological_space.nonempty_compacts.to_compact_space TopologicalSpace.NonemptyCompacts.toCompactSpace
-/

#print TopologicalSpace.NonemptyCompacts.toNonempty /-
instance toNonempty {s : NonemptyCompacts α} : Nonempty s :=
  s.Nonempty.to_subtype
#align topological_space.nonempty_compacts.to_nonempty TopologicalSpace.NonemptyCompacts.toNonempty
-/

/- warning: topological_space.nonempty_compacts.prod -> TopologicalSpace.NonemptyCompacts.prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], (TopologicalSpace.NonemptyCompacts.{u1} α _inst_1) -> (TopologicalSpace.NonemptyCompacts.{u2} β _inst_2) -> (TopologicalSpace.NonemptyCompacts.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], (TopologicalSpace.NonemptyCompacts.{u1} α _inst_1) -> (TopologicalSpace.NonemptyCompacts.{u2} β _inst_2) -> (TopologicalSpace.NonemptyCompacts.{max u2 u1} (Prod.{u1, u2} α β) (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2))
Case conversion may be inaccurate. Consider using '#align topological_space.nonempty_compacts.prod TopologicalSpace.NonemptyCompacts.prodₓ'. -/
/-- The product of two `nonempty_compacts`, as a `nonempty_compacts` in the product space. -/
protected def prod (K : NonemptyCompacts α) (L : NonemptyCompacts β) : NonemptyCompacts (α × β) :=
  { K.toCompacts.Prod L.toCompacts with nonempty' := K.Nonempty.Prod L.Nonempty }
#align topological_space.nonempty_compacts.prod TopologicalSpace.NonemptyCompacts.prod

/- warning: topological_space.nonempty_compacts.coe_prod -> TopologicalSpace.NonemptyCompacts.coe_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (K : TopologicalSpace.NonemptyCompacts.{u1} α _inst_1) (L : TopologicalSpace.NonemptyCompacts.{u2} β _inst_2), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) ((fun (a : Type.{max u1 u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ (max u1 u2), succ (max u1 u2)} a b] => self.0) (TopologicalSpace.NonemptyCompacts.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2)) (Set.{max u1 u2} (Prod.{u1, u2} α β)) (HasLiftT.mk.{succ (max u1 u2), succ (max u1 u2)} (TopologicalSpace.NonemptyCompacts.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2)) (Set.{max u1 u2} (Prod.{u1, u2} α β)) (CoeTCₓ.coe.{succ (max u1 u2), succ (max u1 u2)} (TopologicalSpace.NonemptyCompacts.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2)) (Set.{max u1 u2} (Prod.{u1, u2} α β)) (SetLike.Set.hasCoeT.{max u1 u2, max u1 u2} (TopologicalSpace.NonemptyCompacts.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2)) (Prod.{u1, u2} α β) (TopologicalSpace.NonemptyCompacts.setLike.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2))))) (TopologicalSpace.NonemptyCompacts.prod.{u1, u2} α β _inst_1 _inst_2 K L)) (Set.prod.{u1, u2} α β ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.NonemptyCompacts.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.NonemptyCompacts.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.NonemptyCompacts.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.NonemptyCompacts.{u1} α _inst_1) α (TopologicalSpace.NonemptyCompacts.setLike.{u1} α _inst_1)))) K) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (TopologicalSpace.NonemptyCompacts.{u2} β _inst_2) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (TopologicalSpace.NonemptyCompacts.{u2} β _inst_2) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (TopologicalSpace.NonemptyCompacts.{u2} β _inst_2) (Set.{u2} β) (SetLike.Set.hasCoeT.{u2, u2} (TopologicalSpace.NonemptyCompacts.{u2} β _inst_2) β (TopologicalSpace.NonemptyCompacts.setLike.{u2} β _inst_2)))) L))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (K : TopologicalSpace.NonemptyCompacts.{u2} α _inst_1) (L : TopologicalSpace.NonemptyCompacts.{u1} β _inst_2), Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (Prod.{u2, u1} α β)) (SetLike.coe.{max u2 u1, max u2 u1} (TopologicalSpace.NonemptyCompacts.{max u1 u2} (Prod.{u2, u1} α β) (instTopologicalSpaceProd.{u2, u1} α β _inst_1 _inst_2)) (Prod.{u2, u1} α β) (TopologicalSpace.NonemptyCompacts.instSetLikeNonemptyCompacts.{max u2 u1} (Prod.{u2, u1} α β) (instTopologicalSpaceProd.{u2, u1} α β _inst_1 _inst_2)) (TopologicalSpace.NonemptyCompacts.prod.{u2, u1} α β _inst_1 _inst_2 K L)) (Set.prod.{u2, u1} α β (SetLike.coe.{u2, u2} (TopologicalSpace.NonemptyCompacts.{u2} α _inst_1) α (TopologicalSpace.NonemptyCompacts.instSetLikeNonemptyCompacts.{u2} α _inst_1) K) (SetLike.coe.{u1, u1} (TopologicalSpace.NonemptyCompacts.{u1} β _inst_2) β (TopologicalSpace.NonemptyCompacts.instSetLikeNonemptyCompacts.{u1} β _inst_2) L))
Case conversion may be inaccurate. Consider using '#align topological_space.nonempty_compacts.coe_prod TopologicalSpace.NonemptyCompacts.coe_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem coe_prod (K : NonemptyCompacts α) (L : NonemptyCompacts β) :
    (K.Prod L : Set (α × β)) = K ×ˢ L :=
  rfl
#align topological_space.nonempty_compacts.coe_prod TopologicalSpace.NonemptyCompacts.coe_prod

end NonemptyCompacts

/-! ### Positive compact sets -/


#print TopologicalSpace.PositiveCompacts /-
/-- The type of compact sets with nonempty interior of a topological space.
See also `compacts` and `nonempty_compacts`. -/
structure PositiveCompacts (α : Type _) [TopologicalSpace α] extends Compacts α where
  interior_nonempty' : (interior carrier).Nonempty
#align topological_space.positive_compacts TopologicalSpace.PositiveCompacts
-/

namespace PositiveCompacts

instance : SetLike (PositiveCompacts α) α
    where
  coe s := s.carrier
  coe_injective' s t h := by
    obtain ⟨⟨_, _⟩, _⟩ := s
    obtain ⟨⟨_, _⟩, _⟩ := t
    congr

#print TopologicalSpace.PositiveCompacts.isCompact /-
protected theorem isCompact (s : PositiveCompacts α) : IsCompact (s : Set α) :=
  s.is_compact'
#align topological_space.positive_compacts.is_compact TopologicalSpace.PositiveCompacts.isCompact
-/

#print TopologicalSpace.PositiveCompacts.interior_nonempty /-
theorem interior_nonempty (s : PositiveCompacts α) : (interior (s : Set α)).Nonempty :=
  s.interior_nonempty'
#align topological_space.positive_compacts.interior_nonempty TopologicalSpace.PositiveCompacts.interior_nonempty
-/

#print TopologicalSpace.PositiveCompacts.nonempty /-
protected theorem nonempty (s : PositiveCompacts α) : (s : Set α).Nonempty :=
  s.interior_nonempty.mono interior_subset
#align topological_space.positive_compacts.nonempty TopologicalSpace.PositiveCompacts.nonempty
-/

#print TopologicalSpace.PositiveCompacts.toNonemptyCompacts /-
/-- Reinterpret a positive compact as a nonempty compact. -/
def toNonemptyCompacts (s : PositiveCompacts α) : NonemptyCompacts α :=
  ⟨s.toCompacts, s.Nonempty⟩
#align topological_space.positive_compacts.to_nonempty_compacts TopologicalSpace.PositiveCompacts.toNonemptyCompacts
-/

#print TopologicalSpace.PositiveCompacts.ext /-
@[ext]
protected theorem ext {s t : PositiveCompacts α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h
#align topological_space.positive_compacts.ext TopologicalSpace.PositiveCompacts.ext
-/

#print TopologicalSpace.PositiveCompacts.coe_mk /-
@[simp]
theorem coe_mk (s : Compacts α) (h) : (mk s h : Set α) = s :=
  rfl
#align topological_space.positive_compacts.coe_mk TopologicalSpace.PositiveCompacts.coe_mk
-/

#print TopologicalSpace.PositiveCompacts.carrier_eq_coe /-
@[simp]
theorem carrier_eq_coe (s : PositiveCompacts α) : s.carrier = s :=
  rfl
#align topological_space.positive_compacts.carrier_eq_coe TopologicalSpace.PositiveCompacts.carrier_eq_coe
-/

instance : HasSup (PositiveCompacts α) :=
  ⟨fun s t =>
    ⟨s.toCompacts ⊔ t.toCompacts,
      s.interior_nonempty.mono <| interior_mono <| subset_union_left _ _⟩⟩

instance [CompactSpace α] [Nonempty α] : Top (PositiveCompacts α) :=
  ⟨⟨⊤, interior_univ.symm.subst univ_nonempty⟩⟩

instance : SemilatticeSup (PositiveCompacts α) :=
  SetLike.coe_injective.SemilatticeSup _ fun _ _ => rfl

instance [CompactSpace α] [Nonempty α] : OrderTop (PositiveCompacts α) :=
  OrderTop.lift (coe : _ → Set α) (fun _ _ => id) rfl

/- warning: topological_space.positive_compacts.coe_sup -> TopologicalSpace.PositiveCompacts.coe_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : TopologicalSpace.PositiveCompacts.{u1} α _inst_1) (t : TopologicalSpace.PositiveCompacts.{u1} α _inst_1), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.PositiveCompacts.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.PositiveCompacts.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.PositiveCompacts.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.PositiveCompacts.{u1} α _inst_1) α (TopologicalSpace.PositiveCompacts.setLike.{u1} α _inst_1)))) (HasSup.sup.{u1} (TopologicalSpace.PositiveCompacts.{u1} α _inst_1) (TopologicalSpace.PositiveCompacts.hasSup.{u1} α _inst_1) s t)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.PositiveCompacts.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.PositiveCompacts.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.PositiveCompacts.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.PositiveCompacts.{u1} α _inst_1) α (TopologicalSpace.PositiveCompacts.setLike.{u1} α _inst_1)))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.PositiveCompacts.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.PositiveCompacts.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.PositiveCompacts.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.PositiveCompacts.{u1} α _inst_1) α (TopologicalSpace.PositiveCompacts.setLike.{u1} α _inst_1)))) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : TopologicalSpace.PositiveCompacts.{u1} α _inst_1) (t : TopologicalSpace.PositiveCompacts.{u1} α _inst_1), Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.PositiveCompacts.{u1} α _inst_1) α (TopologicalSpace.PositiveCompacts.instSetLikePositiveCompacts.{u1} α _inst_1) (HasSup.sup.{u1} (TopologicalSpace.PositiveCompacts.{u1} α _inst_1) (TopologicalSpace.PositiveCompacts.instHasSupPositiveCompacts.{u1} α _inst_1) s t)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.PositiveCompacts.{u1} α _inst_1) α (TopologicalSpace.PositiveCompacts.instSetLikePositiveCompacts.{u1} α _inst_1) s) (SetLike.coe.{u1, u1} (TopologicalSpace.PositiveCompacts.{u1} α _inst_1) α (TopologicalSpace.PositiveCompacts.instSetLikePositiveCompacts.{u1} α _inst_1) t))
Case conversion may be inaccurate. Consider using '#align topological_space.positive_compacts.coe_sup TopologicalSpace.PositiveCompacts.coe_supₓ'. -/
@[simp]
theorem coe_sup (s t : PositiveCompacts α) : (↑(s ⊔ t) : Set α) = s ∪ t :=
  rfl
#align topological_space.positive_compacts.coe_sup TopologicalSpace.PositiveCompacts.coe_sup

#print TopologicalSpace.PositiveCompacts.coe_top /-
@[simp]
theorem coe_top [CompactSpace α] [Nonempty α] : (↑(⊤ : PositiveCompacts α) : Set α) = univ :=
  rfl
#align topological_space.positive_compacts.coe_top TopologicalSpace.PositiveCompacts.coe_top
-/

#print exists_positiveCompacts_subset /-
theorem exists_positiveCompacts_subset [LocallyCompactSpace α] {U : Set α} (ho : IsOpen U)
    (hn : U.Nonempty) : ∃ K : PositiveCompacts α, ↑K ⊆ U :=
  let ⟨x, hx⟩ := hn
  let ⟨K, hKc, hxK, hKU⟩ := exists_compact_subset ho hx
  ⟨⟨⟨K, hKc⟩, ⟨x, hxK⟩⟩, hKU⟩
#align exists_positive_compacts_subset exists_positiveCompacts_subset
-/

instance [CompactSpace α] [Nonempty α] : Inhabited (PositiveCompacts α) :=
  ⟨⊤⟩

#print TopologicalSpace.PositiveCompacts.nonempty' /-
/-- In a nonempty locally compact space, there exists a compact set with nonempty interior. -/
instance nonempty' [LocallyCompactSpace α] [Nonempty α] : Nonempty (PositiveCompacts α) :=
  nonempty_of_exists <| exists_positiveCompacts_subset isOpen_univ univ_nonempty
#align topological_space.positive_compacts.nonempty' TopologicalSpace.PositiveCompacts.nonempty'
-/

/- warning: topological_space.positive_compacts.prod -> TopologicalSpace.PositiveCompacts.prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], (TopologicalSpace.PositiveCompacts.{u1} α _inst_1) -> (TopologicalSpace.PositiveCompacts.{u2} β _inst_2) -> (TopologicalSpace.PositiveCompacts.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], (TopologicalSpace.PositiveCompacts.{u1} α _inst_1) -> (TopologicalSpace.PositiveCompacts.{u2} β _inst_2) -> (TopologicalSpace.PositiveCompacts.{max u2 u1} (Prod.{u1, u2} α β) (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2))
Case conversion may be inaccurate. Consider using '#align topological_space.positive_compacts.prod TopologicalSpace.PositiveCompacts.prodₓ'. -/
/-- The product of two `positive_compacts`, as a `positive_compacts` in the product space. -/
protected def prod (K : PositiveCompacts α) (L : PositiveCompacts β) : PositiveCompacts (α × β) :=
  { K.toCompacts.Prod L.toCompacts with
    interior_nonempty' :=
      by
      simp only [compacts.carrier_eq_coe, compacts.coe_prod, interior_prod_eq]
      exact K.interior_nonempty.prod L.interior_nonempty }
#align topological_space.positive_compacts.prod TopologicalSpace.PositiveCompacts.prod

/- warning: topological_space.positive_compacts.coe_prod -> TopologicalSpace.PositiveCompacts.coe_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (K : TopologicalSpace.PositiveCompacts.{u1} α _inst_1) (L : TopologicalSpace.PositiveCompacts.{u2} β _inst_2), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) ((fun (a : Type.{max u1 u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ (max u1 u2), succ (max u1 u2)} a b] => self.0) (TopologicalSpace.PositiveCompacts.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2)) (Set.{max u1 u2} (Prod.{u1, u2} α β)) (HasLiftT.mk.{succ (max u1 u2), succ (max u1 u2)} (TopologicalSpace.PositiveCompacts.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2)) (Set.{max u1 u2} (Prod.{u1, u2} α β)) (CoeTCₓ.coe.{succ (max u1 u2), succ (max u1 u2)} (TopologicalSpace.PositiveCompacts.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2)) (Set.{max u1 u2} (Prod.{u1, u2} α β)) (SetLike.Set.hasCoeT.{max u1 u2, max u1 u2} (TopologicalSpace.PositiveCompacts.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2)) (Prod.{u1, u2} α β) (TopologicalSpace.PositiveCompacts.setLike.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2))))) (TopologicalSpace.PositiveCompacts.prod.{u1, u2} α β _inst_1 _inst_2 K L)) (Set.prod.{u1, u2} α β ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.PositiveCompacts.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.PositiveCompacts.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.PositiveCompacts.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.PositiveCompacts.{u1} α _inst_1) α (TopologicalSpace.PositiveCompacts.setLike.{u1} α _inst_1)))) K) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (TopologicalSpace.PositiveCompacts.{u2} β _inst_2) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (TopologicalSpace.PositiveCompacts.{u2} β _inst_2) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (TopologicalSpace.PositiveCompacts.{u2} β _inst_2) (Set.{u2} β) (SetLike.Set.hasCoeT.{u2, u2} (TopologicalSpace.PositiveCompacts.{u2} β _inst_2) β (TopologicalSpace.PositiveCompacts.setLike.{u2} β _inst_2)))) L))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (K : TopologicalSpace.PositiveCompacts.{u2} α _inst_1) (L : TopologicalSpace.PositiveCompacts.{u1} β _inst_2), Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (Prod.{u2, u1} α β)) (SetLike.coe.{max u2 u1, max u2 u1} (TopologicalSpace.PositiveCompacts.{max u1 u2} (Prod.{u2, u1} α β) (instTopologicalSpaceProd.{u2, u1} α β _inst_1 _inst_2)) (Prod.{u2, u1} α β) (TopologicalSpace.PositiveCompacts.instSetLikePositiveCompacts.{max u2 u1} (Prod.{u2, u1} α β) (instTopologicalSpaceProd.{u2, u1} α β _inst_1 _inst_2)) (TopologicalSpace.PositiveCompacts.prod.{u2, u1} α β _inst_1 _inst_2 K L)) (Set.prod.{u2, u1} α β (SetLike.coe.{u2, u2} (TopologicalSpace.PositiveCompacts.{u2} α _inst_1) α (TopologicalSpace.PositiveCompacts.instSetLikePositiveCompacts.{u2} α _inst_1) K) (SetLike.coe.{u1, u1} (TopologicalSpace.PositiveCompacts.{u1} β _inst_2) β (TopologicalSpace.PositiveCompacts.instSetLikePositiveCompacts.{u1} β _inst_2) L))
Case conversion may be inaccurate. Consider using '#align topological_space.positive_compacts.coe_prod TopologicalSpace.PositiveCompacts.coe_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem coe_prod (K : PositiveCompacts α) (L : PositiveCompacts β) :
    (K.Prod L : Set (α × β)) = K ×ˢ L :=
  rfl
#align topological_space.positive_compacts.coe_prod TopologicalSpace.PositiveCompacts.coe_prod

end PositiveCompacts

/-! ### Compact open sets -/


#print TopologicalSpace.CompactOpens /-
/-- The type of compact open sets of a topological space. This is useful in non Hausdorff contexts,
in particular spectral spaces. -/
structure CompactOpens (α : Type _) [TopologicalSpace α] extends Compacts α where
  is_open' : IsOpen carrier
#align topological_space.compact_opens TopologicalSpace.CompactOpens
-/

namespace CompactOpens

instance : SetLike (CompactOpens α) α
    where
  coe s := s.carrier
  coe_injective' s t h := by
    obtain ⟨⟨_, _⟩, _⟩ := s
    obtain ⟨⟨_, _⟩, _⟩ := t
    congr

#print TopologicalSpace.CompactOpens.isCompact /-
protected theorem isCompact (s : CompactOpens α) : IsCompact (s : Set α) :=
  s.is_compact'
#align topological_space.compact_opens.is_compact TopologicalSpace.CompactOpens.isCompact
-/

#print TopologicalSpace.CompactOpens.isOpen /-
protected theorem isOpen (s : CompactOpens α) : IsOpen (s : Set α) :=
  s.is_open'
#align topological_space.compact_opens.is_open TopologicalSpace.CompactOpens.isOpen
-/

#print TopologicalSpace.CompactOpens.toOpens /-
/-- Reinterpret a compact open as an open. -/
@[simps]
def toOpens (s : CompactOpens α) : Opens α :=
  ⟨s, s.IsOpen⟩
#align topological_space.compact_opens.to_opens TopologicalSpace.CompactOpens.toOpens
-/

#print TopologicalSpace.CompactOpens.toClopens /-
/-- Reinterpret a compact open as a clopen. -/
@[simps]
def toClopens [T2Space α] (s : CompactOpens α) : Clopens α :=
  ⟨s, s.IsOpen, s.IsCompact.IsClosed⟩
#align topological_space.compact_opens.to_clopens TopologicalSpace.CompactOpens.toClopens
-/

#print TopologicalSpace.CompactOpens.ext /-
@[ext]
protected theorem ext {s t : CompactOpens α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h
#align topological_space.compact_opens.ext TopologicalSpace.CompactOpens.ext
-/

#print TopologicalSpace.CompactOpens.coe_mk /-
@[simp]
theorem coe_mk (s : Compacts α) (h) : (mk s h : Set α) = s :=
  rfl
#align topological_space.compact_opens.coe_mk TopologicalSpace.CompactOpens.coe_mk
-/

instance : HasSup (CompactOpens α) :=
  ⟨fun s t => ⟨s.toCompacts ⊔ t.toCompacts, s.IsOpen.union t.IsOpen⟩⟩

instance [QuasiSeparatedSpace α] : HasInf (CompactOpens α) :=
  ⟨fun U V =>
    ⟨⟨(U : Set α) ∩ (V : Set α),
        QuasiSeparatedSpace.inter_isCompact U.1.1 V.1.1 U.2 U.1.2 V.2 V.1.2⟩,
      U.2.inter V.2⟩⟩

instance [QuasiSeparatedSpace α] : SemilatticeInf (CompactOpens α) :=
  SetLike.coe_injective.SemilatticeInf _ fun _ _ => rfl

instance [CompactSpace α] : Top (CompactOpens α) :=
  ⟨⟨⊤, isOpen_univ⟩⟩

instance : Bot (CompactOpens α) :=
  ⟨⟨⊥, isOpen_empty⟩⟩

instance [T2Space α] : SDiff (CompactOpens α) :=
  ⟨fun s t => ⟨⟨s \ t, s.IsCompact.diffₓ t.IsOpen⟩, s.IsOpen.sdiff t.IsCompact.IsClosed⟩⟩

instance [T2Space α] [CompactSpace α] : HasCompl (CompactOpens α) :=
  ⟨fun s => ⟨⟨sᶜ, s.IsOpen.isClosed_compl.IsCompact⟩, s.IsCompact.IsClosed.isOpen_compl⟩⟩

instance : SemilatticeSup (CompactOpens α) :=
  SetLike.coe_injective.SemilatticeSup _ fun _ _ => rfl

instance : OrderBot (CompactOpens α) :=
  OrderBot.lift (coe : _ → Set α) (fun _ _ => id) rfl

instance [T2Space α] : GeneralizedBooleanAlgebra (CompactOpens α) :=
  SetLike.coe_injective.GeneralizedBooleanAlgebra _ (fun _ _ => rfl) (fun _ _ => rfl) rfl fun _ _ =>
    rfl

instance [CompactSpace α] : BoundedOrder (CompactOpens α) :=
  BoundedOrder.lift (coe : _ → Set α) (fun _ _ => id) rfl rfl

instance [T2Space α] [CompactSpace α] : BooleanAlgebra (CompactOpens α) :=
  SetLike.coe_injective.BooleanAlgebra _ (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl (fun _ => rfl)
    fun _ _ => rfl

/- warning: topological_space.compact_opens.coe_sup -> TopologicalSpace.CompactOpens.coe_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : TopologicalSpace.CompactOpens.{u1} α _inst_1) (t : TopologicalSpace.CompactOpens.{u1} α _inst_1), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) α (TopologicalSpace.CompactOpens.setLike.{u1} α _inst_1)))) (HasSup.sup.{u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) (TopologicalSpace.CompactOpens.hasSup.{u1} α _inst_1) s t)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) α (TopologicalSpace.CompactOpens.setLike.{u1} α _inst_1)))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) α (TopologicalSpace.CompactOpens.setLike.{u1} α _inst_1)))) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (s : TopologicalSpace.CompactOpens.{u1} α _inst_1) (t : TopologicalSpace.CompactOpens.{u1} α _inst_1), Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) α (TopologicalSpace.CompactOpens.instSetLikeCompactOpens.{u1} α _inst_1) (HasSup.sup.{u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) (TopologicalSpace.CompactOpens.instHasSupCompactOpens.{u1} α _inst_1) s t)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) α (TopologicalSpace.CompactOpens.instSetLikeCompactOpens.{u1} α _inst_1) s) (SetLike.coe.{u1, u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) α (TopologicalSpace.CompactOpens.instSetLikeCompactOpens.{u1} α _inst_1) t))
Case conversion may be inaccurate. Consider using '#align topological_space.compact_opens.coe_sup TopologicalSpace.CompactOpens.coe_supₓ'. -/
@[simp]
theorem coe_sup (s t : CompactOpens α) : (↑(s ⊔ t) : Set α) = s ∪ t :=
  rfl
#align topological_space.compact_opens.coe_sup TopologicalSpace.CompactOpens.coe_sup

/- warning: topological_space.compact_opens.coe_inf -> TopologicalSpace.CompactOpens.coe_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_1] (s : TopologicalSpace.CompactOpens.{u1} α _inst_1) (t : TopologicalSpace.CompactOpens.{u1} α _inst_1), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) α (TopologicalSpace.CompactOpens.setLike.{u1} α _inst_1)))) (HasInf.inf.{u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) (TopologicalSpace.CompactOpens.hasInf.{u1} α _inst_1 (T2Space.to_quasiSeparatedSpace.{u1} α _inst_1 _inst_3)) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) α (TopologicalSpace.CompactOpens.setLike.{u1} α _inst_1)))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) α (TopologicalSpace.CompactOpens.setLike.{u1} α _inst_1)))) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_1] (s : TopologicalSpace.CompactOpens.{u1} α _inst_1) (t : TopologicalSpace.CompactOpens.{u1} α _inst_1), Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) α (TopologicalSpace.CompactOpens.instSetLikeCompactOpens.{u1} α _inst_1) (HasInf.inf.{u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) (TopologicalSpace.CompactOpens.instHasInfCompactOpens.{u1} α _inst_1 (T2Space.to_quasiSeparatedSpace.{u1} α _inst_1 _inst_3)) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) α (TopologicalSpace.CompactOpens.instSetLikeCompactOpens.{u1} α _inst_1) s) (SetLike.coe.{u1, u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) α (TopologicalSpace.CompactOpens.instSetLikeCompactOpens.{u1} α _inst_1) t))
Case conversion may be inaccurate. Consider using '#align topological_space.compact_opens.coe_inf TopologicalSpace.CompactOpens.coe_infₓ'. -/
@[simp]
theorem coe_inf [T2Space α] (s t : CompactOpens α) : (↑(s ⊓ t) : Set α) = s ∩ t :=
  rfl
#align topological_space.compact_opens.coe_inf TopologicalSpace.CompactOpens.coe_inf

#print TopologicalSpace.CompactOpens.coe_top /-
@[simp]
theorem coe_top [CompactSpace α] : (↑(⊤ : CompactOpens α) : Set α) = univ :=
  rfl
#align topological_space.compact_opens.coe_top TopologicalSpace.CompactOpens.coe_top
-/

#print TopologicalSpace.CompactOpens.coe_bot /-
@[simp]
theorem coe_bot : (↑(⊥ : CompactOpens α) : Set α) = ∅ :=
  rfl
#align topological_space.compact_opens.coe_bot TopologicalSpace.CompactOpens.coe_bot
-/

/- warning: topological_space.compact_opens.coe_sdiff -> TopologicalSpace.CompactOpens.coe_sdiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_1] (s : TopologicalSpace.CompactOpens.{u1} α _inst_1) (t : TopologicalSpace.CompactOpens.{u1} α _inst_1), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) α (TopologicalSpace.CompactOpens.setLike.{u1} α _inst_1)))) (SDiff.sdiff.{u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) (TopologicalSpace.CompactOpens.hasSdiff.{u1} α _inst_1 _inst_3) s t)) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) α (TopologicalSpace.CompactOpens.setLike.{u1} α _inst_1)))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) α (TopologicalSpace.CompactOpens.setLike.{u1} α _inst_1)))) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_1] (s : TopologicalSpace.CompactOpens.{u1} α _inst_1) (t : TopologicalSpace.CompactOpens.{u1} α _inst_1), Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) α (TopologicalSpace.CompactOpens.instSetLikeCompactOpens.{u1} α _inst_1) (SDiff.sdiff.{u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) (TopologicalSpace.CompactOpens.instSDiffCompactOpens.{u1} α _inst_1 _inst_3) s t)) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) α (TopologicalSpace.CompactOpens.instSetLikeCompactOpens.{u1} α _inst_1) s) (SetLike.coe.{u1, u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) α (TopologicalSpace.CompactOpens.instSetLikeCompactOpens.{u1} α _inst_1) t))
Case conversion may be inaccurate. Consider using '#align topological_space.compact_opens.coe_sdiff TopologicalSpace.CompactOpens.coe_sdiffₓ'. -/
@[simp]
theorem coe_sdiff [T2Space α] (s t : CompactOpens α) : (↑(s \ t) : Set α) = s \ t :=
  rfl
#align topological_space.compact_opens.coe_sdiff TopologicalSpace.CompactOpens.coe_sdiff

/- warning: topological_space.compact_opens.coe_compl -> TopologicalSpace.CompactOpens.coe_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_1] [_inst_4 : CompactSpace.{u1} α _inst_1] (s : TopologicalSpace.CompactOpens.{u1} α _inst_1), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) α (TopologicalSpace.CompactOpens.setLike.{u1} α _inst_1)))) (HasCompl.compl.{u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) (TopologicalSpace.CompactOpens.hasCompl.{u1} α _inst_1 _inst_3 _inst_4) s)) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) α (TopologicalSpace.CompactOpens.setLike.{u1} α _inst_1)))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_3 : T2Space.{u1} α _inst_1] [_inst_4 : CompactSpace.{u1} α _inst_1] (s : TopologicalSpace.CompactOpens.{u1} α _inst_1), Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) α (TopologicalSpace.CompactOpens.instSetLikeCompactOpens.{u1} α _inst_1) (HasCompl.compl.{u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) (TopologicalSpace.CompactOpens.instHasComplCompactOpens.{u1} α _inst_1 _inst_3 _inst_4) s)) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (SetLike.coe.{u1, u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) α (TopologicalSpace.CompactOpens.instSetLikeCompactOpens.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align topological_space.compact_opens.coe_compl TopologicalSpace.CompactOpens.coe_complₓ'. -/
@[simp]
theorem coe_compl [T2Space α] [CompactSpace α] (s : CompactOpens α) : (↑(sᶜ) : Set α) = sᶜ :=
  rfl
#align topological_space.compact_opens.coe_compl TopologicalSpace.CompactOpens.coe_compl

instance : Inhabited (CompactOpens α) :=
  ⟨⊥⟩

#print TopologicalSpace.CompactOpens.map /-
/-- The image of a compact open under a continuous open map. -/
@[simps]
def map (f : α → β) (hf : Continuous f) (hf' : IsOpenMap f) (s : CompactOpens α) : CompactOpens β :=
  ⟨s.toCompacts.map f hf, hf' _ s.IsOpen⟩
#align topological_space.compact_opens.map TopologicalSpace.CompactOpens.map
-/

/- warning: topological_space.compact_opens.coe_map -> TopologicalSpace.CompactOpens.coe_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} (hf : Continuous.{u1, u2} α β _inst_1 _inst_2 f) (hf' : IsOpenMap.{u1, u2} α β _inst_1 _inst_2 f) (s : TopologicalSpace.CompactOpens.{u1} α _inst_1), Eq.{succ u2} (Set.{u2} β) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (TopologicalSpace.CompactOpens.{u2} β _inst_2) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (TopologicalSpace.CompactOpens.{u2} β _inst_2) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (TopologicalSpace.CompactOpens.{u2} β _inst_2) (Set.{u2} β) (SetLike.Set.hasCoeT.{u2, u2} (TopologicalSpace.CompactOpens.{u2} β _inst_2) β (TopologicalSpace.CompactOpens.setLike.{u2} β _inst_2)))) (TopologicalSpace.CompactOpens.map.{u1, u2} α β _inst_1 _inst_2 f hf hf' s)) (Set.image.{u1, u2} α β f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) α (TopologicalSpace.CompactOpens.setLike.{u1} α _inst_1)))) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} (hf : Continuous.{u2, u1} α β _inst_1 _inst_2 f) (hf' : IsOpenMap.{u2, u1} α β _inst_1 _inst_2 f) (s : TopologicalSpace.CompactOpens.{u2} α _inst_1), Eq.{succ u1} (Set.{u1} β) (SetLike.coe.{u1, u1} (TopologicalSpace.CompactOpens.{u1} β _inst_2) β (TopologicalSpace.CompactOpens.instSetLikeCompactOpens.{u1} β _inst_2) (TopologicalSpace.CompactOpens.map.{u2, u1} α β _inst_1 _inst_2 f hf hf' s)) (Set.image.{u2, u1} α β f (SetLike.coe.{u2, u2} (TopologicalSpace.CompactOpens.{u2} α _inst_1) α (TopologicalSpace.CompactOpens.instSetLikeCompactOpens.{u2} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align topological_space.compact_opens.coe_map TopologicalSpace.CompactOpens.coe_mapₓ'. -/
@[simp]
theorem coe_map {f : α → β} (hf : Continuous f) (hf' : IsOpenMap f) (s : CompactOpens α) :
    (s.map f hf hf' : Set β) = f '' s :=
  rfl
#align topological_space.compact_opens.coe_map TopologicalSpace.CompactOpens.coe_map

/- warning: topological_space.compact_opens.prod -> TopologicalSpace.CompactOpens.prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], (TopologicalSpace.CompactOpens.{u1} α _inst_1) -> (TopologicalSpace.CompactOpens.{u2} β _inst_2) -> (TopologicalSpace.CompactOpens.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], (TopologicalSpace.CompactOpens.{u1} α _inst_1) -> (TopologicalSpace.CompactOpens.{u2} β _inst_2) -> (TopologicalSpace.CompactOpens.{max u2 u1} (Prod.{u1, u2} α β) (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2))
Case conversion may be inaccurate. Consider using '#align topological_space.compact_opens.prod TopologicalSpace.CompactOpens.prodₓ'. -/
/-- The product of two `compact_opens`, as a `compact_opens` in the product space. -/
protected def prod (K : CompactOpens α) (L : CompactOpens β) : CompactOpens (α × β) :=
  { K.toCompacts.Prod L.toCompacts with is_open' := K.IsOpen.Prod L.IsOpen }
#align topological_space.compact_opens.prod TopologicalSpace.CompactOpens.prod

/- warning: topological_space.compact_opens.coe_prod -> TopologicalSpace.CompactOpens.coe_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (K : TopologicalSpace.CompactOpens.{u1} α _inst_1) (L : TopologicalSpace.CompactOpens.{u2} β _inst_2), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) ((fun (a : Type.{max u1 u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ (max u1 u2), succ (max u1 u2)} a b] => self.0) (TopologicalSpace.CompactOpens.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2)) (Set.{max u1 u2} (Prod.{u1, u2} α β)) (HasLiftT.mk.{succ (max u1 u2), succ (max u1 u2)} (TopologicalSpace.CompactOpens.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2)) (Set.{max u1 u2} (Prod.{u1, u2} α β)) (CoeTCₓ.coe.{succ (max u1 u2), succ (max u1 u2)} (TopologicalSpace.CompactOpens.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2)) (Set.{max u1 u2} (Prod.{u1, u2} α β)) (SetLike.Set.hasCoeT.{max u1 u2, max u1 u2} (TopologicalSpace.CompactOpens.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2)) (Prod.{u1, u2} α β) (TopologicalSpace.CompactOpens.setLike.{max u1 u2} (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2))))) (TopologicalSpace.CompactOpens.prod.{u1, u2} α β _inst_1 _inst_2 K L)) (Set.prod.{u1, u2} α β ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.CompactOpens.{u1} α _inst_1) α (TopologicalSpace.CompactOpens.setLike.{u1} α _inst_1)))) K) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (TopologicalSpace.CompactOpens.{u2} β _inst_2) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (TopologicalSpace.CompactOpens.{u2} β _inst_2) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (TopologicalSpace.CompactOpens.{u2} β _inst_2) (Set.{u2} β) (SetLike.Set.hasCoeT.{u2, u2} (TopologicalSpace.CompactOpens.{u2} β _inst_2) β (TopologicalSpace.CompactOpens.setLike.{u2} β _inst_2)))) L))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (K : TopologicalSpace.CompactOpens.{u2} α _inst_1) (L : TopologicalSpace.CompactOpens.{u1} β _inst_2), Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (Prod.{u2, u1} α β)) (SetLike.coe.{max u2 u1, max u2 u1} (TopologicalSpace.CompactOpens.{max u1 u2} (Prod.{u2, u1} α β) (instTopologicalSpaceProd.{u2, u1} α β _inst_1 _inst_2)) (Prod.{u2, u1} α β) (TopologicalSpace.CompactOpens.instSetLikeCompactOpens.{max u2 u1} (Prod.{u2, u1} α β) (instTopologicalSpaceProd.{u2, u1} α β _inst_1 _inst_2)) (TopologicalSpace.CompactOpens.prod.{u2, u1} α β _inst_1 _inst_2 K L)) (Set.prod.{u2, u1} α β (SetLike.coe.{u2, u2} (TopologicalSpace.CompactOpens.{u2} α _inst_1) α (TopologicalSpace.CompactOpens.instSetLikeCompactOpens.{u2} α _inst_1) K) (SetLike.coe.{u1, u1} (TopologicalSpace.CompactOpens.{u1} β _inst_2) β (TopologicalSpace.CompactOpens.instSetLikeCompactOpens.{u1} β _inst_2) L))
Case conversion may be inaccurate. Consider using '#align topological_space.compact_opens.coe_prod TopologicalSpace.CompactOpens.coe_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem coe_prod (K : CompactOpens α) (L : CompactOpens β) : (K.Prod L : Set (α × β)) = K ×ˢ L :=
  rfl
#align topological_space.compact_opens.coe_prod TopologicalSpace.CompactOpens.coe_prod

end CompactOpens

end TopologicalSpace

