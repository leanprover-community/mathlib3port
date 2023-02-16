/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module topology.sets.order
! leanprover-community/mathlib commit 32253a1a1071173b33dc7d6a218cf722c6feb514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.UpperLower.Basic
import Mathbin.Topology.Sets.Closeds

/-!
# Clopen upper sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define the type of clopen upper sets.
-/


open Set TopologicalSpace

variable {α β : Type _} [TopologicalSpace α] [LE α] [TopologicalSpace β] [LE β]

/-! ### Compact open sets -/


#print ClopenUpperSet /-
/-- The type of clopen upper sets of a topological space. -/
structure ClopenUpperSet (α : Type _) [TopologicalSpace α] [LE α] extends Clopens α where
  upper' : IsUpperSet carrier
#align clopen_upper_set ClopenUpperSet
-/

namespace ClopenUpperSet

instance : SetLike (ClopenUpperSet α) α
    where
  coe s := s.carrier
  coe_injective' s t h := by
    obtain ⟨⟨_, _⟩, _⟩ := s
    obtain ⟨⟨_, _⟩, _⟩ := t
    congr

#print ClopenUpperSet.upper /-
theorem upper (s : ClopenUpperSet α) : IsUpperSet (s : Set α) :=
  s.upper'
#align clopen_upper_set.upper ClopenUpperSet.upper
-/

#print ClopenUpperSet.clopen /-
theorem clopen (s : ClopenUpperSet α) : IsClopen (s : Set α) :=
  s.clopen'
#align clopen_upper_set.clopen ClopenUpperSet.clopen
-/

#print ClopenUpperSet.toUpperSet /-
/-- Reinterpret a upper clopen as an upper set. -/
@[simps]
def toUpperSet (s : ClopenUpperSet α) : UpperSet α :=
  ⟨s, s.upper⟩
#align clopen_upper_set.to_upper_set ClopenUpperSet.toUpperSet
-/

#print ClopenUpperSet.ext /-
@[ext]
protected theorem ext {s t : ClopenUpperSet α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h
#align clopen_upper_set.ext ClopenUpperSet.ext
-/

#print ClopenUpperSet.coe_mk /-
@[simp]
theorem coe_mk (s : Clopens α) (h) : (mk s h : Set α) = s :=
  rfl
#align clopen_upper_set.coe_mk ClopenUpperSet.coe_mk
-/

instance : HasSup (ClopenUpperSet α) :=
  ⟨fun s t => ⟨s.toClopens ⊔ t.toClopens, s.upper.union t.upper⟩⟩

instance : HasInf (ClopenUpperSet α) :=
  ⟨fun s t => ⟨s.toClopens ⊓ t.toClopens, s.upper.inter t.upper⟩⟩

instance : Top (ClopenUpperSet α) :=
  ⟨⟨⊤, isUpperSet_univ⟩⟩

instance : Bot (ClopenUpperSet α) :=
  ⟨⟨⊥, isUpperSet_empty⟩⟩

instance : Lattice (ClopenUpperSet α) :=
  SetLike.coe_injective.Lattice _ (fun _ _ => rfl) fun _ _ => rfl

instance : BoundedOrder (ClopenUpperSet α) :=
  BoundedOrder.lift (coe : _ → Set α) (fun _ _ => id) rfl rfl

/- warning: clopen_upper_set.coe_sup -> ClopenUpperSet.coe_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LE.{u1} α] (s : ClopenUpperSet.{u1} α _inst_1 _inst_2) (t : ClopenUpperSet.{u1} α _inst_1 _inst_2), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (ClopenUpperSet.{u1} α _inst_1 _inst_2) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) α (ClopenUpperSet.setLike.{u1} α _inst_1 _inst_2)))) (HasSup.sup.{u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) (ClopenUpperSet.hasSup.{u1} α _inst_1 _inst_2) s t)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (ClopenUpperSet.{u1} α _inst_1 _inst_2) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) α (ClopenUpperSet.setLike.{u1} α _inst_1 _inst_2)))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (ClopenUpperSet.{u1} α _inst_1 _inst_2) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) α (ClopenUpperSet.setLike.{u1} α _inst_1 _inst_2)))) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LE.{u1} α] (s : ClopenUpperSet.{u1} α _inst_1 _inst_2) (t : ClopenUpperSet.{u1} α _inst_1 _inst_2), Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) α (ClopenUpperSet.instSetLikeClopenUpperSet.{u1} α _inst_1 _inst_2) (HasSup.sup.{u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) (ClopenUpperSet.instHasSupClopenUpperSet.{u1} α _inst_1 _inst_2) s t)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (SetLike.coe.{u1, u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) α (ClopenUpperSet.instSetLikeClopenUpperSet.{u1} α _inst_1 _inst_2) s) (SetLike.coe.{u1, u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) α (ClopenUpperSet.instSetLikeClopenUpperSet.{u1} α _inst_1 _inst_2) t))
Case conversion may be inaccurate. Consider using '#align clopen_upper_set.coe_sup ClopenUpperSet.coe_supₓ'. -/
@[simp]
theorem coe_sup (s t : ClopenUpperSet α) : (↑(s ⊔ t) : Set α) = s ∪ t :=
  rfl
#align clopen_upper_set.coe_sup ClopenUpperSet.coe_sup

/- warning: clopen_upper_set.coe_inf -> ClopenUpperSet.coe_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LE.{u1} α] (s : ClopenUpperSet.{u1} α _inst_1 _inst_2) (t : ClopenUpperSet.{u1} α _inst_1 _inst_2), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (ClopenUpperSet.{u1} α _inst_1 _inst_2) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) α (ClopenUpperSet.setLike.{u1} α _inst_1 _inst_2)))) (HasInf.inf.{u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) (ClopenUpperSet.hasInf.{u1} α _inst_1 _inst_2) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (ClopenUpperSet.{u1} α _inst_1 _inst_2) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) α (ClopenUpperSet.setLike.{u1} α _inst_1 _inst_2)))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (ClopenUpperSet.{u1} α _inst_1 _inst_2) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) α (ClopenUpperSet.setLike.{u1} α _inst_1 _inst_2)))) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LE.{u1} α] (s : ClopenUpperSet.{u1} α _inst_1 _inst_2) (t : ClopenUpperSet.{u1} α _inst_1 _inst_2), Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) α (ClopenUpperSet.instSetLikeClopenUpperSet.{u1} α _inst_1 _inst_2) (HasInf.inf.{u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) (ClopenUpperSet.instHasInfClopenUpperSet.{u1} α _inst_1 _inst_2) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (SetLike.coe.{u1, u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) α (ClopenUpperSet.instSetLikeClopenUpperSet.{u1} α _inst_1 _inst_2) s) (SetLike.coe.{u1, u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) α (ClopenUpperSet.instSetLikeClopenUpperSet.{u1} α _inst_1 _inst_2) t))
Case conversion may be inaccurate. Consider using '#align clopen_upper_set.coe_inf ClopenUpperSet.coe_infₓ'. -/
@[simp]
theorem coe_inf (s t : ClopenUpperSet α) : (↑(s ⊓ t) : Set α) = s ∩ t :=
  rfl
#align clopen_upper_set.coe_inf ClopenUpperSet.coe_inf

/- warning: clopen_upper_set.coe_top -> ClopenUpperSet.coe_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LE.{u1} α], Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (ClopenUpperSet.{u1} α _inst_1 _inst_2) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) α (ClopenUpperSet.setLike.{u1} α _inst_1 _inst_2)))) (Top.top.{u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) (ClopenUpperSet.hasTop.{u1} α _inst_1 _inst_2))) (Set.univ.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LE.{u1} α], Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) α (ClopenUpperSet.instSetLikeClopenUpperSet.{u1} α _inst_1 _inst_2) (Top.top.{u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) (ClopenUpperSet.instTopClopenUpperSet.{u1} α _inst_1 _inst_2))) (Set.univ.{u1} α)
Case conversion may be inaccurate. Consider using '#align clopen_upper_set.coe_top ClopenUpperSet.coe_topₓ'. -/
@[simp]
theorem coe_top : (↑(⊤ : ClopenUpperSet α) : Set α) = univ :=
  rfl
#align clopen_upper_set.coe_top ClopenUpperSet.coe_top

/- warning: clopen_upper_set.coe_bot -> ClopenUpperSet.coe_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LE.{u1} α], Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (ClopenUpperSet.{u1} α _inst_1 _inst_2) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) α (ClopenUpperSet.setLike.{u1} α _inst_1 _inst_2)))) (Bot.bot.{u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) (ClopenUpperSet.hasBot.{u1} α _inst_1 _inst_2))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : LE.{u1} α], Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) α (ClopenUpperSet.instSetLikeClopenUpperSet.{u1} α _inst_1 _inst_2) (Bot.bot.{u1} (ClopenUpperSet.{u1} α _inst_1 _inst_2) (ClopenUpperSet.instBotClopenUpperSet.{u1} α _inst_1 _inst_2))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))
Case conversion may be inaccurate. Consider using '#align clopen_upper_set.coe_bot ClopenUpperSet.coe_botₓ'. -/
@[simp]
theorem coe_bot : (↑(⊥ : ClopenUpperSet α) : Set α) = ∅ :=
  rfl
#align clopen_upper_set.coe_bot ClopenUpperSet.coe_bot

instance : Inhabited (ClopenUpperSet α) :=
  ⟨⊥⟩

end ClopenUpperSet

