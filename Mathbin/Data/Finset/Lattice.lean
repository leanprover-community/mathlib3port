/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.finset.lattice
! leanprover-community/mathlib commit 2d44d6823a96f9c79b7d1ab185918377be663424
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Fold
import Mathbin.Data.Finset.Option
import Mathbin.Data.Finset.Pi
import Mathbin.Data.Finset.Prod
import Mathbin.Data.Multiset.Lattice
import Mathbin.Order.CompleteLattice
import Mathbin.Order.Hom.Lattice

/-!
# Lattice operations on finsets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {F α β γ ι κ : Type _}

namespace Finset

open Multiset OrderDual

/-! ### sup -/


section Sup

-- TODO: define with just `[has_bot α]` where some lemmas hold without requiring `[order_bot α]`
variable [SemilatticeSup α] [OrderBot α]

/- warning: finset.sup -> Finset.sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))], (Finset.{u2} β) -> (β -> α) -> α
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))], (Finset.{u2} β) -> (β -> α) -> α
Case conversion may be inaccurate. Consider using '#align finset.sup Finset.supₓ'. -/
/-- Supremum of a finite set: `sup {a, b, c} f = f a ⊔ f b ⊔ f c` -/
def sup (s : Finset β) (f : β → α) : α :=
  s.fold (· ⊔ ·) ⊥ f
#align finset.sup Finset.sup

variable {s s₁ s₂ : Finset β} {f g : β → α} {a : α}

/- warning: finset.sup_def -> Finset.sup_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} {f : β -> α}, Eq.{succ u1} α (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s f) (Multiset.sup.{u1} α _inst_1 _inst_2 (Multiset.map.{u2, u1} β α f (Finset.val.{u2} β s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SemilatticeSup.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1)))] {s : Finset.{u1} β} {f : β -> α}, Eq.{succ u2} α (Finset.sup.{u2, u1} α β _inst_1 _inst_2 s f) (Multiset.sup.{u2} α _inst_1 _inst_2 (Multiset.map.{u1, u2} β α f (Finset.val.{u1} β s)))
Case conversion may be inaccurate. Consider using '#align finset.sup_def Finset.sup_defₓ'. -/
theorem sup_def : s.sup f = (s.1.map f).sup :=
  rfl
#align finset.sup_def Finset.sup_def

/- warning: finset.sup_empty -> Finset.sup_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {f : β -> α}, Eq.{succ u1} α (Finset.sup.{u1, u2} α β _inst_1 _inst_2 (EmptyCollection.emptyCollection.{u2} (Finset.{u2} β) (Finset.hasEmptyc.{u2} β)) f) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) _inst_2))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SemilatticeSup.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1)))] {f : β -> α}, Eq.{succ u2} α (Finset.sup.{u2, u1} α β _inst_1 _inst_2 (EmptyCollection.emptyCollection.{u1} (Finset.{u1} β) (Finset.instEmptyCollectionFinset.{u1} β)) f) (Bot.bot.{u2} α (OrderBot.toBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1))) _inst_2))
Case conversion may be inaccurate. Consider using '#align finset.sup_empty Finset.sup_emptyₓ'. -/
@[simp]
theorem sup_empty : (∅ : Finset β).sup f = ⊥ :=
  fold_empty
#align finset.sup_empty Finset.sup_empty

/- warning: finset.sup_cons -> Finset.sup_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} {f : β -> α} {b : β} (h : Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s)), Eq.{succ u1} α (Finset.sup.{u1, u2} α β _inst_1 _inst_2 (Finset.cons.{u2} β b s h) f) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1) (f b) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} {f : β -> α} {b : β} (h : Not (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b s)), Eq.{succ u1} α (Finset.sup.{u1, u2} α β _inst_1 _inst_2 (Finset.cons.{u2} β b s h) f) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_1) (f b) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s f))
Case conversion may be inaccurate. Consider using '#align finset.sup_cons Finset.sup_consₓ'. -/
@[simp]
theorem sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b ⊔ s.sup f :=
  fold_cons h
#align finset.sup_cons Finset.sup_cons

/- warning: finset.sup_insert -> Finset.sup_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} {f : β -> α} [_inst_3 : DecidableEq.{succ u2} β] {b : β}, Eq.{succ u1} α (Finset.sup.{u1, u2} α β _inst_1 _inst_2 (Insert.insert.{u2, u2} β (Finset.{u2} β) (Finset.hasInsert.{u2} β (fun (a : β) (b : β) => _inst_3 a b)) b s) f) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1) (f b) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} {f : β -> α} [_inst_3 : DecidableEq.{succ u2} β] {b : β}, Eq.{succ u1} α (Finset.sup.{u1, u2} α β _inst_1 _inst_2 (Insert.insert.{u2, u2} β (Finset.{u2} β) (Finset.instInsertFinset.{u2} β (fun (a : β) (b : β) => _inst_3 a b)) b s) f) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_1) (f b) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s f))
Case conversion may be inaccurate. Consider using '#align finset.sup_insert Finset.sup_insertₓ'. -/
@[simp]
theorem sup_insert [DecidableEq β] {b : β} : (insert b s : Finset β).sup f = f b ⊔ s.sup f :=
  fold_insert_idem
#align finset.sup_insert Finset.sup_insert

/- warning: finset.sup_image -> Finset.sup_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : DecidableEq.{succ u2} β] (s : Finset.{u3} γ) (f : γ -> β) (g : β -> α), Eq.{succ u1} α (Finset.sup.{u1, u2} α β _inst_1 _inst_2 (Finset.image.{u3, u2} γ β (fun (a : β) (b : β) => _inst_3 a b) f s) g) (Finset.sup.{u1, u3} α γ _inst_1 _inst_2 s (Function.comp.{succ u3, succ u2, succ u1} γ β α g f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : DecidableEq.{succ u3} β] (s : Finset.{u2} γ) (f : γ -> β) (g : β -> α), Eq.{succ u1} α (Finset.sup.{u1, u3} α β _inst_1 _inst_2 (Finset.image.{u2, u3} γ β (fun (a : β) (b : β) => _inst_3 a b) f s) g) (Finset.sup.{u1, u2} α γ _inst_1 _inst_2 s (Function.comp.{succ u2, succ u3, succ u1} γ β α g f))
Case conversion may be inaccurate. Consider using '#align finset.sup_image Finset.sup_imageₓ'. -/
theorem sup_image [DecidableEq β] (s : Finset γ) (f : γ → β) (g : β → α) :
    (s.image f).sup g = s.sup (g ∘ f) :=
  fold_image_idem
#align finset.sup_image Finset.sup_image

/- warning: finset.sup_map -> Finset.sup_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] (s : Finset.{u3} γ) (f : Function.Embedding.{succ u3, succ u2} γ β) (g : β -> α), Eq.{succ u1} α (Finset.sup.{u1, u2} α β _inst_1 _inst_2 (Finset.map.{u3, u2} γ β f s) g) (Finset.sup.{u1, u3} α γ _inst_1 _inst_2 s (Function.comp.{succ u3, succ u2, succ u1} γ β α g (coeFn.{max 1 (succ u3) (succ u2), max (succ u3) (succ u2)} (Function.Embedding.{succ u3, succ u2} γ β) (fun (_x : Function.Embedding.{succ u3, succ u2} γ β) => γ -> β) (Function.Embedding.hasCoeToFun.{succ u3, succ u2} γ β) f)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] (s : Finset.{u3} γ) (f : Function.Embedding.{succ u3, succ u2} γ β) (g : β -> α), Eq.{succ u1} α (Finset.sup.{u1, u2} α β _inst_1 _inst_2 (Finset.map.{u3, u2} γ β f s) g) (Finset.sup.{u1, u3} α γ _inst_1 _inst_2 s (Function.comp.{succ u3, succ u2, succ u1} γ β α g (FunLike.coe.{max (succ u2) (succ u3), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} γ β) γ (fun (_x : γ) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : γ) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u3), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} γ β) γ β (Function.instEmbeddingLikeEmbedding.{succ u3, succ u2} γ β)) f)))
Case conversion may be inaccurate. Consider using '#align finset.sup_map Finset.sup_mapₓ'. -/
@[simp]
theorem sup_map (s : Finset γ) (f : γ ↪ β) (g : β → α) : (s.map f).sup g = s.sup (g ∘ f) :=
  fold_map
#align finset.sup_map Finset.sup_map

/- warning: finset.sup_singleton -> Finset.sup_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {f : β -> α} {b : β}, Eq.{succ u1} α (Finset.sup.{u1, u2} α β _inst_1 _inst_2 (Singleton.singleton.{u2, u2} β (Finset.{u2} β) (Finset.hasSingleton.{u2} β) b) f) (f b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SemilatticeSup.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1)))] {f : β -> α} {b : β}, Eq.{succ u2} α (Finset.sup.{u2, u1} α β _inst_1 _inst_2 (Singleton.singleton.{u1, u1} β (Finset.{u1} β) (Finset.instSingletonFinset.{u1} β) b) f) (f b)
Case conversion may be inaccurate. Consider using '#align finset.sup_singleton Finset.sup_singletonₓ'. -/
@[simp]
theorem sup_singleton {b : β} : ({b} : Finset β).sup f = f b :=
  sup_singleton
#align finset.sup_singleton Finset.sup_singleton

/- warning: finset.sup_union -> Finset.sup_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {s₁ : Finset.{u2} β} {s₂ : Finset.{u2} β} {f : β -> α} [_inst_3 : DecidableEq.{succ u2} β], Eq.{succ u1} α (Finset.sup.{u1, u2} α β _inst_1 _inst_2 (Union.union.{u2} (Finset.{u2} β) (Finset.hasUnion.{u2} β (fun (a : β) (b : β) => _inst_3 a b)) s₁ s₂) f) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s₁ f) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s₂ f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {s₁ : Finset.{u2} β} {s₂ : Finset.{u2} β} {f : β -> α} [_inst_3 : DecidableEq.{succ u2} β], Eq.{succ u1} α (Finset.sup.{u1, u2} α β _inst_1 _inst_2 (Union.union.{u2} (Finset.{u2} β) (Finset.instUnionFinset.{u2} β (fun (a : β) (b : β) => _inst_3 a b)) s₁ s₂) f) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_1) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s₁ f) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s₂ f))
Case conversion may be inaccurate. Consider using '#align finset.sup_union Finset.sup_unionₓ'. -/
theorem sup_union [DecidableEq β] : (s₁ ∪ s₂).sup f = s₁.sup f ⊔ s₂.sup f :=
  Finset.induction_on s₁ (by rw [empty_union, sup_empty, bot_sup_eq]) fun a s has ih => by
    rw [insert_union, sup_insert, sup_insert, ih, sup_assoc]
#align finset.sup_union Finset.sup_union

/- warning: finset.sup_sup -> Finset.sup_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} {f : β -> α} {g : β -> α}, Eq.{succ u1} α (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s (Sup.sup.{max u2 u1} (β -> α) (Pi.hasSup.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => SemilatticeSup.toHasSup.{u1} α _inst_1)) f g)) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s f) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s g))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SemilatticeSup.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1)))] {s : Finset.{u1} β} {f : β -> α} {g : β -> α}, Eq.{succ u2} α (Finset.sup.{u2, u1} α β _inst_1 _inst_2 s (Sup.sup.{max u1 u2} (β -> α) (Pi.instSupForAll.{u1, u2} β (fun (ᾰ : β) => α) (fun (i : β) => SemilatticeSup.toSup.{u2} α _inst_1)) f g)) (Sup.sup.{u2} α (SemilatticeSup.toSup.{u2} α _inst_1) (Finset.sup.{u2, u1} α β _inst_1 _inst_2 s f) (Finset.sup.{u2, u1} α β _inst_1 _inst_2 s g))
Case conversion may be inaccurate. Consider using '#align finset.sup_sup Finset.sup_supₓ'. -/
theorem sup_sup : s.sup (f ⊔ g) = s.sup f ⊔ s.sup g :=
  by
  refine' Finset.cons_induction_on s _ fun b t _ h => _
  · rw [sup_empty, sup_empty, sup_empty, bot_sup_eq]
  · rw [sup_cons, sup_cons, sup_cons, h]
    exact sup_sup_sup_comm _ _ _ _
#align finset.sup_sup Finset.sup_sup

/- warning: finset.sup_congr -> Finset.sup_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {s₁ : Finset.{u2} β} {s₂ : Finset.{u2} β} {f : β -> α} {g : β -> α}, (Eq.{succ u2} (Finset.{u2} β) s₁ s₂) -> (forall (a : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a s₂) -> (Eq.{succ u1} α (f a) (g a))) -> (Eq.{succ u1} α (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s₁ f) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s₂ g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {s₁ : Finset.{u2} β} {s₂ : Finset.{u2} β} {f : β -> α} {g : β -> α}, (Eq.{succ u2} (Finset.{u2} β) s₁ s₂) -> (forall (a : β), (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) a s₂) -> (Eq.{succ u1} α (f a) (g a))) -> (Eq.{succ u1} α (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s₁ f) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s₂ g))
Case conversion may be inaccurate. Consider using '#align finset.sup_congr Finset.sup_congrₓ'. -/
theorem sup_congr {f g : β → α} (hs : s₁ = s₂) (hfg : ∀ a ∈ s₂, f a = g a) : s₁.sup f = s₂.sup g :=
  by subst hs <;> exact Finset.fold_congr hfg
#align finset.sup_congr Finset.sup_congr

/- warning: map_finset_sup -> map_finset_sup is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {ι : Type.{u4}} [_inst_1 : SemilatticeSup.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1)))] [_inst_3 : SemilatticeSup.{u3} β] [_inst_4 : OrderBot.{u3} β (Preorder.toHasLe.{u3} β (PartialOrder.toPreorder.{u3} β (SemilatticeSup.toPartialOrder.{u3} β _inst_3)))] [_inst_5 : SupBotHomClass.{u1, u2, u3} F α β (SemilatticeSup.toHasSup.{u2} α _inst_1) (SemilatticeSup.toHasSup.{u3} β _inst_3) (OrderBot.toHasBot.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1))) _inst_2) (OrderBot.toHasBot.{u3} β (Preorder.toHasLe.{u3} β (PartialOrder.toPreorder.{u3} β (SemilatticeSup.toPartialOrder.{u3} β _inst_3))) _inst_4)] (f : F) (s : Finset.{u4} ι) (g : ι -> α), Eq.{succ u3} β (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (SupHomClass.toFunLike.{u1, u2, u3} F α β (SemilatticeSup.toHasSup.{u2} α _inst_1) (SemilatticeSup.toHasSup.{u3} β _inst_3) (SupBotHomClass.toSupHomClass.{u1, u2, u3} F α β (SemilatticeSup.toHasSup.{u2} α _inst_1) (SemilatticeSup.toHasSup.{u3} β _inst_3) (OrderBot.toHasBot.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1))) _inst_2) (OrderBot.toHasBot.{u3} β (Preorder.toHasLe.{u3} β (PartialOrder.toPreorder.{u3} β (SemilatticeSup.toPartialOrder.{u3} β _inst_3))) _inst_4) _inst_5))) f (Finset.sup.{u2, u4} α ι _inst_1 _inst_2 s g)) (Finset.sup.{u3, u4} β ι _inst_3 _inst_4 s (Function.comp.{succ u4, succ u2, succ u3} ι α β (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (SupHomClass.toFunLike.{u1, u2, u3} F α β (SemilatticeSup.toHasSup.{u2} α _inst_1) (SemilatticeSup.toHasSup.{u3} β _inst_3) (SupBotHomClass.toSupHomClass.{u1, u2, u3} F α β (SemilatticeSup.toHasSup.{u2} α _inst_1) (SemilatticeSup.toHasSup.{u3} β _inst_3) (OrderBot.toHasBot.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1))) _inst_2) (OrderBot.toHasBot.{u3} β (Preorder.toHasLe.{u3} β (PartialOrder.toPreorder.{u3} β (SemilatticeSup.toPartialOrder.{u3} β _inst_3))) _inst_4) _inst_5))) f) g))
but is expected to have type
  forall {F : Type.{u3}} {α : Type.{u2}} {β : Type.{u4}} {ι : Type.{u1}} [_inst_1 : SemilatticeSup.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1)))] [_inst_3 : SemilatticeSup.{u4} β] [_inst_4 : OrderBot.{u4} β (Preorder.toLE.{u4} β (PartialOrder.toPreorder.{u4} β (SemilatticeSup.toPartialOrder.{u4} β _inst_3)))] [_inst_5 : SupBotHomClass.{u3, u2, u4} F α β (SemilatticeSup.toSup.{u2} α _inst_1) (SemilatticeSup.toSup.{u4} β _inst_3) (OrderBot.toBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1))) _inst_2) (OrderBot.toBot.{u4} β (Preorder.toLE.{u4} β (PartialOrder.toPreorder.{u4} β (SemilatticeSup.toPartialOrder.{u4} β _inst_3))) _inst_4)] (f : F) (s : Finset.{u1} ι) (g : ι -> α), Eq.{succ u4} ((fun (x._@.Mathlib.Order.Hom.Lattice._hyg.433 : α) => β) (Finset.sup.{u2, u1} α ι _inst_1 _inst_2 s g)) (FunLike.coe.{succ u3, succ u2, succ u4} F α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.Lattice._hyg.433 : α) => β) _x) (SupHomClass.toFunLike.{u3, u2, u4} F α β (SemilatticeSup.toSup.{u2} α _inst_1) (SemilatticeSup.toSup.{u4} β _inst_3) (SupBotHomClass.toSupHomClass.{u3, u2, u4} F α β (SemilatticeSup.toSup.{u2} α _inst_1) (SemilatticeSup.toSup.{u4} β _inst_3) (OrderBot.toBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1))) _inst_2) (OrderBot.toBot.{u4} β (Preorder.toLE.{u4} β (PartialOrder.toPreorder.{u4} β (SemilatticeSup.toPartialOrder.{u4} β _inst_3))) _inst_4) _inst_5)) f (Finset.sup.{u2, u1} α ι _inst_1 _inst_2 s g)) (Finset.sup.{u4, u1} β ι _inst_3 _inst_4 s (Function.comp.{succ u1, succ u2, succ u4} ι α β (FunLike.coe.{succ u3, succ u2, succ u4} F α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.Lattice._hyg.433 : α) => β) _x) (SupHomClass.toFunLike.{u3, u2, u4} F α β (SemilatticeSup.toSup.{u2} α _inst_1) (SemilatticeSup.toSup.{u4} β _inst_3) (SupBotHomClass.toSupHomClass.{u3, u2, u4} F α β (SemilatticeSup.toSup.{u2} α _inst_1) (SemilatticeSup.toSup.{u4} β _inst_3) (OrderBot.toBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1))) _inst_2) (OrderBot.toBot.{u4} β (Preorder.toLE.{u4} β (PartialOrder.toPreorder.{u4} β (SemilatticeSup.toPartialOrder.{u4} β _inst_3))) _inst_4) _inst_5)) f) g))
Case conversion may be inaccurate. Consider using '#align map_finset_sup map_finset_supₓ'. -/
@[simp]
theorem map_finset_sup [SemilatticeSup β] [OrderBot β] [SupBotHomClass F α β] (f : F) (s : Finset ι)
    (g : ι → α) : f (s.sup g) = s.sup (f ∘ g) :=
  Finset.cons_induction_on s (map_bot f) fun i s _ h => by rw [sup_cons, sup_cons, map_sup, h]
#align map_finset_sup map_finset_sup

/- warning: finset.sup_le_iff -> Finset.sup_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} {f : β -> α} {a : α}, Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s f) a) (forall (b : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) (f b) a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SemilatticeSup.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1)))] {s : Finset.{u1} β} {f : β -> α} {a : α}, Iff (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1))) (Finset.sup.{u2, u1} α β _inst_1 _inst_2 s f) a) (forall (b : β), (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) b s) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1))) (f b) a))
Case conversion may be inaccurate. Consider using '#align finset.sup_le_iff Finset.sup_le_iffₓ'. -/
@[simp]
protected theorem sup_le_iff {a : α} : s.sup f ≤ a ↔ ∀ b ∈ s, f b ≤ a :=
  by
  apply Iff.trans Multiset.sup_le
  simp only [Multiset.mem_map, and_imp, exists_imp]
  exact ⟨fun k b hb => k _ _ hb rfl, fun k a' b hb h => h ▸ k _ hb⟩
#align finset.sup_le_iff Finset.sup_le_iff

/- warning: finset.sup_le -> Finset.sup_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} {f : β -> α} {a : α}, (forall (b : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) (f b) a)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s f) a)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SemilatticeSup.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1)))] {s : Finset.{u1} β} {f : β -> α} {a : α}, (forall (b : β), (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) b s) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1))) (f b) a)) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1))) (Finset.sup.{u2, u1} α β _inst_1 _inst_2 s f) a)
Case conversion may be inaccurate. Consider using '#align finset.sup_le Finset.sup_leₓ'. -/
alias Finset.sup_le_iff ↔ _ sup_le
#align finset.sup_le Finset.sup_le

attribute [protected] sup_le

/- warning: finset.sup_const_le -> Finset.sup_const_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} {a : α}, LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s (fun (_x : β) => a)) a
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SemilatticeSup.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1)))] {s : Finset.{u1} β} {a : α}, LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1))) (Finset.sup.{u2, u1} α β _inst_1 _inst_2 s (fun (_x : β) => a)) a
Case conversion may be inaccurate. Consider using '#align finset.sup_const_le Finset.sup_const_leₓ'. -/
theorem sup_const_le : (s.sup fun _ => a) ≤ a :=
  Finset.sup_le fun _ _ => le_rfl
#align finset.sup_const_le Finset.sup_const_le

/- warning: finset.le_sup -> Finset.le_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} {f : β -> α} {b : β}, (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) (f b) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} {f : β -> α} {b : β}, (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) (f b) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s f))
Case conversion may be inaccurate. Consider using '#align finset.le_sup Finset.le_supₓ'. -/
theorem le_sup {b : β} (hb : b ∈ s) : f b ≤ s.sup f :=
  Finset.sup_le_iff.1 le_rfl _ hb
#align finset.le_sup Finset.le_sup

/- warning: finset.le_sup_of_le -> Finset.le_sup_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} {f : β -> α} {a : α} {b : β}, (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) a (f b)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) a (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} {f : β -> α} {a : α} {b : β}, (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) a (f b)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) a (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s f))
Case conversion may be inaccurate. Consider using '#align finset.le_sup_of_le Finset.le_sup_of_leₓ'. -/
theorem le_sup_of_le {b : β} (hb : b ∈ s) (h : a ≤ f b) : a ≤ s.sup f :=
  h.trans <| le_sup hb
#align finset.le_sup_of_le Finset.le_sup_of_le

/- warning: finset.sup_bUnion -> Finset.sup_biUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {f : β -> α} [_inst_3 : DecidableEq.{succ u2} β] (s : Finset.{u3} γ) (t : γ -> (Finset.{u2} β)), Eq.{succ u1} α (Finset.sup.{u1, u2} α β _inst_1 _inst_2 (Finset.biUnion.{u3, u2} γ β (fun (a : β) (b : β) => _inst_3 a b) s t) f) (Finset.sup.{u1, u3} α γ _inst_1 _inst_2 s (fun (x : γ) => Finset.sup.{u1, u2} α β _inst_1 _inst_2 (t x) f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {f : β -> α} [_inst_3 : DecidableEq.{succ u3} β] (s : Finset.{u2} γ) (t : γ -> (Finset.{u3} β)), Eq.{succ u1} α (Finset.sup.{u1, u3} α β _inst_1 _inst_2 (Finset.biUnion.{u2, u3} γ β (fun (a : β) (b : β) => _inst_3 a b) s t) f) (Finset.sup.{u1, u2} α γ _inst_1 _inst_2 s (fun (x : γ) => Finset.sup.{u1, u3} α β _inst_1 _inst_2 (t x) f))
Case conversion may be inaccurate. Consider using '#align finset.sup_bUnion Finset.sup_biUnionₓ'. -/
@[simp]
theorem sup_biUnion [DecidableEq β] (s : Finset γ) (t : γ → Finset β) :
    (s.biUnion t).sup f = s.sup fun x => (t x).sup f :=
  eq_of_forall_ge_iff fun c => by simp [@forall_swap _ β]
#align finset.sup_bUnion Finset.sup_biUnion

/- warning: finset.sup_const -> Finset.sup_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β}, (Finset.Nonempty.{u2} β s) -> (forall (c : α), Eq.{succ u1} α (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s (fun (_x : β) => c)) c)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β}, (Finset.Nonempty.{u2} β s) -> (forall (c : α), Eq.{succ u1} α (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s (fun (_x : β) => c)) c)
Case conversion may be inaccurate. Consider using '#align finset.sup_const Finset.sup_constₓ'. -/
theorem sup_const {s : Finset β} (h : s.Nonempty) (c : α) : (s.sup fun _ => c) = c :=
  eq_of_forall_ge_iff fun b => Finset.sup_le_iff.trans h.forall_const
#align finset.sup_const Finset.sup_const

/- warning: finset.sup_bot -> Finset.sup_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] (s : Finset.{u2} β), Eq.{succ u1} α (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s (fun (_x : β) => Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) _inst_2))) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) _inst_2))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] (s : Finset.{u2} β), Eq.{succ u1} α (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s (fun (_x : β) => Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) _inst_2))) (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) _inst_2))
Case conversion may be inaccurate. Consider using '#align finset.sup_bot Finset.sup_botₓ'. -/
@[simp]
theorem sup_bot (s : Finset β) : (s.sup fun _ => ⊥) = (⊥ : α) :=
  by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · exact sup_empty
  · exact sup_const hs _
#align finset.sup_bot Finset.sup_bot

/- warning: finset.sup_ite -> Finset.sup_ite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} {f : β -> α} {g : β -> α} (p : β -> Prop) [_inst_3 : DecidablePred.{succ u2} β p], Eq.{succ u1} α (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s (fun (i : β) => ite.{succ u1} α (p i) (_inst_3 i) (f i) (g i))) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 (Finset.filter.{u2} β p (fun (a : β) => _inst_3 a) s) f) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 (Finset.filter.{u2} β (fun (i : β) => Not (p i)) (fun (a : β) => Not.decidable (p a) (_inst_3 a)) s) g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} {f : β -> α} {g : β -> α} (p : β -> Prop) [_inst_3 : DecidablePred.{succ u2} β p], Eq.{succ u1} α (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s (fun (i : β) => ite.{succ u1} α (p i) (_inst_3 i) (f i) (g i))) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_1) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 (Finset.filter.{u2} β p (fun (a : β) => _inst_3 a) s) f) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 (Finset.filter.{u2} β (fun (i : β) => Not (p i)) (fun (a : β) => instDecidableNot (p a) (_inst_3 a)) s) g))
Case conversion may be inaccurate. Consider using '#align finset.sup_ite Finset.sup_iteₓ'. -/
theorem sup_ite (p : β → Prop) [DecidablePred p] :
    (s.sup fun i => ite (p i) (f i) (g i)) =
      (s.filterₓ p).sup f ⊔ (s.filterₓ fun i => ¬p i).sup g :=
  fold_ite _
#align finset.sup_ite Finset.sup_ite

/- warning: finset.sup_mono_fun -> Finset.sup_mono_fun is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} {f : β -> α} {g : β -> α}, (forall (b : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) (f b) (g b))) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s f) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} {f : β -> α} {g : β -> α}, (forall (b : β), (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) (f b) (g b))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s f) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s g))
Case conversion may be inaccurate. Consider using '#align finset.sup_mono_fun Finset.sup_mono_funₓ'. -/
theorem sup_mono_fun {g : β → α} (h : ∀ b ∈ s, f b ≤ g b) : s.sup f ≤ s.sup g :=
  Finset.sup_le fun b hb => le_trans (h b hb) (le_sup hb)
#align finset.sup_mono_fun Finset.sup_mono_fun

/- warning: finset.sup_mono -> Finset.sup_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {s₁ : Finset.{u2} β} {s₂ : Finset.{u2} β} {f : β -> α}, (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) s₁ s₂) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s₁ f) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s₂ f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {s₁ : Finset.{u2} β} {s₂ : Finset.{u2} β} {f : β -> α}, (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.instHasSubsetFinset.{u2} β) s₁ s₂) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s₁ f) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s₂ f))
Case conversion may be inaccurate. Consider using '#align finset.sup_mono Finset.sup_monoₓ'. -/
theorem sup_mono (h : s₁ ⊆ s₂) : s₁.sup f ≤ s₂.sup f :=
  Finset.sup_le fun b hb => le_sup <| h hb
#align finset.sup_mono Finset.sup_mono

/- warning: finset.sup_comm -> Finset.sup_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] (s : Finset.{u2} β) (t : Finset.{u3} γ) (f : β -> γ -> α), Eq.{succ u1} α (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s (fun (b : β) => Finset.sup.{u1, u3} α γ _inst_1 _inst_2 t (f b))) (Finset.sup.{u1, u3} α γ _inst_1 _inst_2 t (fun (c : γ) => Finset.sup.{u1, u2} α β _inst_1 _inst_2 s (fun (b : β) => f b c)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] (s : Finset.{u3} β) (t : Finset.{u2} γ) (f : β -> γ -> α), Eq.{succ u1} α (Finset.sup.{u1, u3} α β _inst_1 _inst_2 s (fun (b : β) => Finset.sup.{u1, u2} α γ _inst_1 _inst_2 t (f b))) (Finset.sup.{u1, u2} α γ _inst_1 _inst_2 t (fun (c : γ) => Finset.sup.{u1, u3} α β _inst_1 _inst_2 s (fun (b : β) => f b c)))
Case conversion may be inaccurate. Consider using '#align finset.sup_comm Finset.sup_commₓ'. -/
protected theorem sup_comm (s : Finset β) (t : Finset γ) (f : β → γ → α) :
    (s.sup fun b => t.sup (f b)) = t.sup fun c => s.sup fun b => f b c :=
  by
  refine' eq_of_forall_ge_iff fun a => _
  simp_rw [Finset.sup_le_iff]
  exact ⟨fun h c hc b hb => h b hb c hc, fun h b hb c hc => h c hc b hb⟩
#align finset.sup_comm Finset.sup_comm

/- warning: finset.sup_attach -> Finset.sup_attach is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] (s : Finset.{u2} β) (f : β -> α), Eq.{succ u1} α (Finset.sup.{u1, u2} α (Subtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s)) _inst_1 _inst_2 (Finset.attach.{u2} β s) (fun (x : Subtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s)) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Subtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s)) β (HasLiftT.mk.{succ u2, succ u2} (Subtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s)) β (CoeTCₓ.coe.{succ u2, succ u2} (Subtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s)) β (coeBase.{succ u2, succ u2} (Subtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s)) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s))))) x))) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] (s : Finset.{u2} β) (f : β -> α), Eq.{succ u1} α (Finset.sup.{u1, u2} α (Subtype.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) x s)) _inst_1 _inst_2 (Finset.attach.{u2} β s) (fun (x : Subtype.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) x s)) => f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) x s) x))) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s f)
Case conversion may be inaccurate. Consider using '#align finset.sup_attach Finset.sup_attachₓ'. -/
@[simp]
theorem sup_attach (s : Finset β) (f : β → α) : (s.attach.sup fun x => f x) = s.sup f :=
  (s.attach.sup_map (Function.Embedding.subtype _) f).symm.trans <| congr_arg _ attach_map_val
#align finset.sup_attach Finset.sup_attach

/- warning: finset.sup_product_left -> Finset.sup_product_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] (s : Finset.{u2} β) (t : Finset.{u3} γ) (f : (Prod.{u2, u3} β γ) -> α), Eq.{succ u1} α (Finset.sup.{u1, max u2 u3} α (Prod.{u2, u3} β γ) _inst_1 _inst_2 (Finset.product.{u2, u3} β γ s t) f) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s (fun (i : β) => Finset.sup.{u1, u3} α γ _inst_1 _inst_2 t (fun (i' : γ) => f (Prod.mk.{u2, u3} β γ i i'))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] (s : Finset.{u3} β) (t : Finset.{u2} γ) (f : (Prod.{u3, u2} β γ) -> α), Eq.{succ u1} α (Finset.sup.{u1, max u3 u2} α (Prod.{u3, u2} β γ) _inst_1 _inst_2 (Finset.product.{u3, u2} β γ s t) f) (Finset.sup.{u1, u3} α β _inst_1 _inst_2 s (fun (i : β) => Finset.sup.{u1, u2} α γ _inst_1 _inst_2 t (fun (i' : γ) => f (Prod.mk.{u3, u2} β γ i i'))))
Case conversion may be inaccurate. Consider using '#align finset.sup_product_left Finset.sup_product_leftₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- See also `finset.product_bUnion`. -/
theorem sup_product_left (s : Finset β) (t : Finset γ) (f : β × γ → α) :
    (s ×ˢ t).sup f = s.sup fun i => t.sup fun i' => f ⟨i, i'⟩ :=
  by
  simp only [le_antisymm_iff, Finset.sup_le_iff, mem_product, and_imp, Prod.forall]
  exact
    ⟨fun b c hb hc => (le_sup hb).trans' <| le_sup hc, fun b hb c hc =>
      le_sup <| mem_product.2 ⟨hb, hc⟩⟩
#align finset.sup_product_left Finset.sup_product_left

/- warning: finset.sup_product_right -> Finset.sup_product_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] (s : Finset.{u2} β) (t : Finset.{u3} γ) (f : (Prod.{u2, u3} β γ) -> α), Eq.{succ u1} α (Finset.sup.{u1, max u2 u3} α (Prod.{u2, u3} β γ) _inst_1 _inst_2 (Finset.product.{u2, u3} β γ s t) f) (Finset.sup.{u1, u3} α γ _inst_1 _inst_2 t (fun (i' : γ) => Finset.sup.{u1, u2} α β _inst_1 _inst_2 s (fun (i : β) => f (Prod.mk.{u2, u3} β γ i i'))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] (s : Finset.{u3} β) (t : Finset.{u2} γ) (f : (Prod.{u3, u2} β γ) -> α), Eq.{succ u1} α (Finset.sup.{u1, max u3 u2} α (Prod.{u3, u2} β γ) _inst_1 _inst_2 (Finset.product.{u3, u2} β γ s t) f) (Finset.sup.{u1, u2} α γ _inst_1 _inst_2 t (fun (i' : γ) => Finset.sup.{u1, u3} α β _inst_1 _inst_2 s (fun (i : β) => f (Prod.mk.{u3, u2} β γ i i'))))
Case conversion may be inaccurate. Consider using '#align finset.sup_product_right Finset.sup_product_rightₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem sup_product_right (s : Finset β) (t : Finset γ) (f : β × γ → α) :
    (s ×ˢ t).sup f = t.sup fun i' => s.sup fun i => f ⟨i, i'⟩ := by
  rw [sup_product_left, Finset.sup_comm]
#align finset.sup_product_right Finset.sup_product_right

/- warning: finset.sup_erase_bot -> Finset.sup_erase_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Eq.{succ u1} α (Finset.sup.{u1, u1} α α _inst_1 _inst_2 (Finset.erase.{u1} α (fun (a : α) (b : α) => _inst_3 a b) s (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) _inst_2))) (id.{succ u1} α)) (Finset.sup.{u1, u1} α α _inst_1 _inst_2 s (id.{succ u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Eq.{succ u1} α (Finset.sup.{u1, u1} α α _inst_1 _inst_2 (Finset.erase.{u1} α (fun (a : α) (b : α) => _inst_3 a b) s (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) _inst_2))) (id.{succ u1} α)) (Finset.sup.{u1, u1} α α _inst_1 _inst_2 s (id.{succ u1} α))
Case conversion may be inaccurate. Consider using '#align finset.sup_erase_bot Finset.sup_erase_botₓ'. -/
@[simp]
theorem sup_erase_bot [DecidableEq α] (s : Finset α) : (s.eraseₓ ⊥).sup id = s.sup id :=
  by
  refine' (sup_mono (s.erase_subset _)).antisymm (Finset.sup_le_iff.2 fun a ha => _)
  obtain rfl | ha' := eq_or_ne a ⊥
  · exact bot_le
  · exact le_sup (mem_erase.2 ⟨ha', ha⟩)
#align finset.sup_erase_bot Finset.sup_erase_bot

/- warning: finset.sup_sdiff_right -> Finset.sup_sdiff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_3 : GeneralizedBooleanAlgebra.{u1} α] (s : Finset.{u2} β) (f : β -> α) (a : α), Eq.{succ u1} α (Finset.sup.{u1, u2} α β (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_3))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_3) s (fun (b : β) => SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_3) (f b) a)) (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_3) (Finset.sup.{u1, u2} α β (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_3))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_3) s f) a)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_3 : GeneralizedBooleanAlgebra.{u2} α] (s : Finset.{u1} β) (f : β -> α) (a : α), Eq.{succ u2} α (Finset.sup.{u2, u1} α β (Lattice.toSemilatticeSup.{u2} α (GeneralizedCoheytingAlgebra.toLattice.{u2} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u2} α _inst_3))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} α _inst_3) s (fun (b : β) => SDiff.sdiff.{u2} α (GeneralizedBooleanAlgebra.toSDiff.{u2} α _inst_3) (f b) a)) (SDiff.sdiff.{u2} α (GeneralizedBooleanAlgebra.toSDiff.{u2} α _inst_3) (Finset.sup.{u2, u1} α β (Lattice.toSemilatticeSup.{u2} α (GeneralizedCoheytingAlgebra.toLattice.{u2} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u2} α _inst_3))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} α _inst_3) s f) a)
Case conversion may be inaccurate. Consider using '#align finset.sup_sdiff_right Finset.sup_sdiff_rightₓ'. -/
theorem sup_sdiff_right {α β : Type _} [GeneralizedBooleanAlgebra α] (s : Finset β) (f : β → α)
    (a : α) : (s.sup fun b => f b \ a) = s.sup f \ a :=
  by
  refine' Finset.cons_induction_on s _ fun b t _ h => _
  · rw [sup_empty, sup_empty, bot_sdiff]
  · rw [sup_cons, sup_cons, h, sup_sdiff]
#align finset.sup_sdiff_right Finset.sup_sdiff_right

/- warning: finset.comp_sup_eq_sup_comp -> Finset.comp_sup_eq_sup_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : SemilatticeSup.{u3} γ] [_inst_4 : OrderBot.{u3} γ (Preorder.toHasLe.{u3} γ (PartialOrder.toPreorder.{u3} γ (SemilatticeSup.toPartialOrder.{u3} γ _inst_3)))] {s : Finset.{u2} β} {f : β -> α} (g : α -> γ), (forall (x : α) (y : α), Eq.{succ u3} γ (g (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1) x y)) (Sup.sup.{u3} γ (SemilatticeSup.toHasSup.{u3} γ _inst_3) (g x) (g y))) -> (Eq.{succ u3} γ (g (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) _inst_2))) (Bot.bot.{u3} γ (OrderBot.toHasBot.{u3} γ (Preorder.toHasLe.{u3} γ (PartialOrder.toPreorder.{u3} γ (SemilatticeSup.toPartialOrder.{u3} γ _inst_3))) _inst_4))) -> (Eq.{succ u3} γ (g (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s f)) (Finset.sup.{u3, u2} γ β _inst_3 _inst_4 s (Function.comp.{succ u2, succ u1, succ u3} β α γ g f)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : SemilatticeSup.{u3} γ] [_inst_4 : OrderBot.{u3} γ (Preorder.toLE.{u3} γ (PartialOrder.toPreorder.{u3} γ (SemilatticeSup.toPartialOrder.{u3} γ _inst_3)))] {s : Finset.{u2} β} {f : β -> α} (g : α -> γ), (forall (x : α) (y : α), Eq.{succ u3} γ (g (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_1) x y)) (Sup.sup.{u3} γ (SemilatticeSup.toSup.{u3} γ _inst_3) (g x) (g y))) -> (Eq.{succ u3} γ (g (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) _inst_2))) (Bot.bot.{u3} γ (OrderBot.toBot.{u3} γ (Preorder.toLE.{u3} γ (PartialOrder.toPreorder.{u3} γ (SemilatticeSup.toPartialOrder.{u3} γ _inst_3))) _inst_4))) -> (Eq.{succ u3} γ (g (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s f)) (Finset.sup.{u3, u2} γ β _inst_3 _inst_4 s (Function.comp.{succ u2, succ u1, succ u3} β α γ g f)))
Case conversion may be inaccurate. Consider using '#align finset.comp_sup_eq_sup_comp Finset.comp_sup_eq_sup_compₓ'. -/
theorem comp_sup_eq_sup_comp [SemilatticeSup γ] [OrderBot γ] {s : Finset β} {f : β → α} (g : α → γ)
    (g_sup : ∀ x y, g (x ⊔ y) = g x ⊔ g y) (bot : g ⊥ = ⊥) : g (s.sup f) = s.sup (g ∘ f) :=
  Finset.cons_induction_on s bot fun c t hc ih => by rw [sup_cons, sup_cons, g_sup, ih]
#align finset.comp_sup_eq_sup_comp Finset.comp_sup_eq_sup_comp

/- warning: finset.sup_coe -> Finset.sup_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {P : α -> Prop} {Pbot : P (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) _inst_2))} {Psup : forall {{x : α}} {{y : α}}, (P x) -> (P y) -> (P (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1) x y))} (t : Finset.{u2} β) (f : β -> (Subtype.{succ u1} α (fun (x : α) => P x))), Eq.{succ u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => P x)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => P x)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => P x)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => P x)) α (coeSubtype.{succ u1} α (fun (x : α) => P x))))) (Finset.sup.{u1, u2} (Subtype.{succ u1} α (fun (x : α) => P x)) β (Subtype.semilatticeSup.{u1} α _inst_1 (fun (x : α) => P x) Psup) (Subtype.orderBot.{u1} α (fun (x : α) => P x) (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) _inst_2 Pbot) t f)) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 t (fun (x : β) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => P x)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => P x)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => P x)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => P x)) α (coeSubtype.{succ u1} α (fun (x : α) => P x))))) (f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SemilatticeSup.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1)))] {P : α -> Prop} {Pbot : P (Bot.bot.{u2} α (OrderBot.toBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1))) _inst_2))} {Psup : forall {{x : α}} {{y : α}}, (P x) -> (P y) -> (P (Sup.sup.{u2} α (SemilatticeSup.toSup.{u2} α _inst_1) x y))} (t : Finset.{u1} β) (f : β -> (Subtype.{succ u2} α (fun (x : α) => P x))), Eq.{succ u2} α (Subtype.val.{succ u2} α (fun (x : α) => P x) (Finset.sup.{u2, u1} (Subtype.{succ u2} α (fun (x : α) => P x)) β (Subtype.semilatticeSup.{u2} α _inst_1 (fun (x : α) => P x) Psup) (Subtype.orderBot.{u2} α (fun (x : α) => P x) (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1))) _inst_2 Pbot) t f)) (Finset.sup.{u2, u1} α β _inst_1 _inst_2 t (fun (x : β) => Subtype.val.{succ u2} α (fun (x : α) => P x) (f x)))
Case conversion may be inaccurate. Consider using '#align finset.sup_coe Finset.sup_coeₓ'. -/
/-- Computing `sup` in a subtype (closed under `sup`) is the same as computing it in `α`. -/
theorem sup_coe {P : α → Prop} {Pbot : P ⊥} {Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y)} (t : Finset β)
    (f : β → { x : α // P x }) :
    (@sup _ _ (Subtype.semilatticeSup Psup) (Subtype.orderBot Pbot) t f : α) = t.sup fun x => f x :=
  by rw [comp_sup_eq_sup_comp coe] <;> intros <;> rfl
#align finset.sup_coe Finset.sup_coe

/- warning: finset.sup_to_finset -> Finset.sup_toFinset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_3 : DecidableEq.{succ u2} β] (s : Finset.{u1} α) (f : α -> (Multiset.{u2} β)), Eq.{succ u2} (Finset.{u2} β) (Multiset.toFinset.{u2} β (fun (a : β) (b : β) => _inst_3 a b) (Finset.sup.{u2, u1} (Multiset.{u2} β) α (Lattice.toSemilatticeSup.{u2} (Multiset.{u2} β) (Multiset.lattice.{u2} β (fun (a : β) (b : β) => _inst_3 a b))) (Multiset.orderBot.{u2} β) s f)) (Finset.sup.{u2, u1} (Finset.{u2} β) α (Lattice.toSemilatticeSup.{u2} (Finset.{u2} β) (Finset.lattice.{u2} β (fun (a : β) (b : β) => _inst_3 a b))) (Finset.orderBot.{u2} β) s (fun (x : α) => Multiset.toFinset.{u2} β (fun (a : β) (b : β) => _inst_3 a b) (f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_3 : DecidableEq.{succ u1} β] (s : Finset.{u2} α) (f : α -> (Multiset.{u1} β)), Eq.{succ u1} (Finset.{u1} β) (Multiset.toFinset.{u1} β (fun (a : β) (b : β) => _inst_3 a b) (Finset.sup.{u1, u2} (Multiset.{u1} β) α (Lattice.toSemilatticeSup.{u1} (Multiset.{u1} β) (Multiset.instLatticeMultiset.{u1} β (fun (a : β) (b : β) => _inst_3 a b))) (Multiset.instOrderBotMultisetToLEToPreorderInstPartialOrderMultiset.{u1} β) s f)) (Finset.sup.{u1, u2} (Finset.{u1} β) α (Lattice.toSemilatticeSup.{u1} (Finset.{u1} β) (Finset.instLatticeFinset.{u1} β (fun (a : β) (b : β) => _inst_3 a b))) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} β) s (fun (x : α) => Multiset.toFinset.{u1} β (fun (a : β) (b : β) => _inst_3 a b) (f x)))
Case conversion may be inaccurate. Consider using '#align finset.sup_to_finset Finset.sup_toFinsetₓ'. -/
@[simp]
theorem sup_toFinset {α β} [DecidableEq β] (s : Finset α) (f : α → Multiset β) :
    (s.sup f).toFinset = s.sup fun x => (f x).toFinset :=
  comp_sup_eq_sup_comp Multiset.toFinset toFinset_union rfl
#align finset.sup_to_finset Finset.sup_toFinset

/- warning: list.foldr_sup_eq_sup_to_finset -> List.foldr_sup_eq_sup_toFinset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : DecidableEq.{succ u1} α] (l : List.{u1} α), Eq.{succ u1} α (List.foldr.{u1, u1} α α (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1)) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) _inst_2)) l) (Finset.sup.{u1, u1} α α _inst_1 _inst_2 (List.toFinset.{u1} α (fun (a : α) (b : α) => _inst_3 a b) l) (id.{succ u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : DecidableEq.{succ u1} α] (l : List.{u1} α), Eq.{succ u1} α (List.foldr.{u1, u1} α α (fun (x._@.Mathlib.Data.Finset.Lattice._hyg.2519 : α) (x._@.Mathlib.Data.Finset.Lattice._hyg.2521 : α) => Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_1) x._@.Mathlib.Data.Finset.Lattice._hyg.2519 x._@.Mathlib.Data.Finset.Lattice._hyg.2521) (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) _inst_2)) l) (Finset.sup.{u1, u1} α α _inst_1 _inst_2 (List.toFinset.{u1} α (fun (a : α) (b : α) => _inst_3 a b) l) (id.{succ u1} α))
Case conversion may be inaccurate. Consider using '#align list.foldr_sup_eq_sup_to_finset List.foldr_sup_eq_sup_toFinsetₓ'. -/
theorem List.foldr_sup_eq_sup_toFinset [DecidableEq α] (l : List α) :
    l.foldr (· ⊔ ·) ⊥ = l.toFinset.sup id :=
  by
  rw [← coe_fold_r, ← Multiset.fold_dedup_idem, sup_def, ← List.toFinset_coe, to_finset_val,
    Multiset.map_id]
  rfl
#align list.foldr_sup_eq_sup_to_finset List.foldr_sup_eq_sup_toFinset

#print Finset.subset_range_sup_succ /-
theorem subset_range_sup_succ (s : Finset ℕ) : s ⊆ range (s.sup id).succ := fun n hn =>
  mem_range.2 <| Nat.lt_succ_of_le <| le_sup hn
#align finset.subset_range_sup_succ Finset.subset_range_sup_succ
-/

#print Finset.exists_nat_subset_range /-
theorem exists_nat_subset_range (s : Finset ℕ) : ∃ n : ℕ, s ⊆ range n :=
  ⟨_, s.subset_range_sup_succ⟩
#align finset.exists_nat_subset_range Finset.exists_nat_subset_range
-/

/- warning: finset.sup_induction -> Finset.sup_induction is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} {f : β -> α} {p : α -> Prop}, (p (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) _inst_2))) -> (forall (a₁ : α), (p a₁) -> (forall (a₂ : α), (p a₂) -> (p (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1) a₁ a₂)))) -> (forall (b : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s) -> (p (f b))) -> (p (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SemilatticeSup.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1)))] {s : Finset.{u1} β} {f : β -> α} {p : α -> Prop}, (p (Bot.bot.{u2} α (OrderBot.toBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1))) _inst_2))) -> (forall (a₁ : α), (p a₁) -> (forall (a₂ : α), (p a₂) -> (p (Sup.sup.{u2} α (SemilatticeSup.toSup.{u2} α _inst_1) a₁ a₂)))) -> (forall (b : β), (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) b s) -> (p (f b))) -> (p (Finset.sup.{u2, u1} α β _inst_1 _inst_2 s f))
Case conversion may be inaccurate. Consider using '#align finset.sup_induction Finset.sup_inductionₓ'. -/
theorem sup_induction {p : α → Prop} (hb : p ⊥) (hp : ∀ a₁, p a₁ → ∀ a₂, p a₂ → p (a₁ ⊔ a₂))
    (hs : ∀ b ∈ s, p (f b)) : p (s.sup f) :=
  by
  induction' s using Finset.cons_induction with c s hc ih
  · exact hb
  · rw [sup_cons]
    apply hp
    · exact hs c (mem_cons.2 (Or.inl rfl))
    · exact ih fun b h => hs b (mem_cons.2 (Or.inr h))
#align finset.sup_induction Finset.sup_induction

/- warning: finset.sup_le_of_le_directed -> Finset.sup_le_of_le_directed is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_3 : SemilatticeSup.{u1} α] [_inst_4 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_3)))] (s : Set.{u1} α), (Set.Nonempty.{u1} α s) -> (DirectedOn.{u1} α (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_3)))) s) -> (forall (t : Finset.{u1} α), (forall (x : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x t) -> (Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) => LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_3))) x y)))) -> (Exists.{succ u1} α (fun (x : α) => And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_3))) (Finset.sup.{u1, u1} α α _inst_3 _inst_4 t (id.{succ u1} α)) x))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_3 : SemilatticeSup.{u1} α] [_inst_4 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_3)))] (s : Set.{u1} α), (Set.Nonempty.{u1} α s) -> (DirectedOn.{u1} α (fun (x._@.Mathlib.Data.Finset.Lattice._hyg.2877 : α) (x._@.Mathlib.Data.Finset.Lattice._hyg.2879 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_3))) x._@.Mathlib.Data.Finset.Lattice._hyg.2877 x._@.Mathlib.Data.Finset.Lattice._hyg.2879) s) -> (forall (t : Finset.{u1} α), (forall (x : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x t) -> (Exists.{succ u1} α (fun (y : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_3))) x y)))) -> (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_3))) (Finset.sup.{u1, u1} α α _inst_3 _inst_4 t (id.{succ u1} α)) x))))
Case conversion may be inaccurate. Consider using '#align finset.sup_le_of_le_directed Finset.sup_le_of_le_directedₓ'. -/
theorem sup_le_of_le_directed {α : Type _} [SemilatticeSup α] [OrderBot α] (s : Set α)
    (hs : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s) (t : Finset α) :
    (∀ x ∈ t, ∃ y ∈ s, x ≤ y) → ∃ x, x ∈ s ∧ t.sup id ≤ x := by
  classical
    apply Finset.induction_on t
    ·
      simpa only [forall_prop_of_true, and_true_iff, forall_prop_of_false, bot_le, not_false_iff,
        sup_empty, forall_true_iff, not_mem_empty]
    · intro a r har ih h
      have incs : ↑r ⊆ ↑(insert a r) := by
        rw [Finset.coe_subset]
        apply Finset.subset_insert
      -- x ∈ s is above the sup of r
      obtain ⟨x, ⟨hxs, hsx_sup⟩⟩ := ih fun x hx => h x <| incs hx
      -- y ∈ s is above a
      obtain ⟨y, hys, hay⟩ := h a (Finset.mem_insert_self a r)
      -- z ∈ s is above x and y
      obtain ⟨z, hzs, ⟨hxz, hyz⟩⟩ := hdir x hxs y hys
      use z, hzs
      rw [sup_insert, id.def, sup_le_iff]
      exact ⟨le_trans hay hyz, le_trans hsx_sup hxz⟩
#align finset.sup_le_of_le_directed Finset.sup_le_of_le_directed

/- warning: finset.sup_mem -> Finset.sup_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] (s : Set.{u1} α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) _inst_2)) s) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1) x y) s))) -> (forall {ι : Type.{u2}} (t : Finset.{u2} ι) (p : ι -> α), (forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i t) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (p i) s)) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Finset.sup.{u1, u2} α ι _inst_1 _inst_2 t p) s))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : SemilatticeSup.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1)))] (s : Set.{u2} α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (Bot.bot.{u2} α (OrderBot.toBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1))) _inst_2)) s) -> (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (forall (y : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) y s) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (Sup.sup.{u2} α (SemilatticeSup.toSup.{u2} α _inst_1) x y) s))) -> (forall {ι : Type.{u1}} (t : Finset.{u1} ι) (p : ι -> α), (forall (i : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i t) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (p i) s)) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (Finset.sup.{u2, u1} α ι _inst_1 _inst_2 t p) s))
Case conversion may be inaccurate. Consider using '#align finset.sup_mem Finset.sup_memₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » s) -/
-- If we acquire sublattices
-- the hypotheses should be reformulated as `s : subsemilattice_sup_bot`
theorem sup_mem (s : Set α) (w₁ : ⊥ ∈ s) (w₂ : ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s), x ⊔ y ∈ s)
    {ι : Type _} (t : Finset ι) (p : ι → α) (h : ∀ i ∈ t, p i ∈ s) : t.sup p ∈ s :=
  @sup_induction _ _ _ _ _ _ (· ∈ s) w₁ w₂ h
#align finset.sup_mem Finset.sup_mem

/- warning: finset.sup_eq_bot_iff -> Finset.sup_eq_bot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] (f : β -> α) (S : Finset.{u2} β), Iff (Eq.{succ u1} α (Finset.sup.{u1, u2} α β _inst_1 _inst_2 S f) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) _inst_2))) (forall (s : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) s S) -> (Eq.{succ u1} α (f s) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) _inst_2))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] (f : β -> α) (S : Finset.{u2} β), Iff (Eq.{succ u1} α (Finset.sup.{u1, u2} α β _inst_1 _inst_2 S f) (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) _inst_2))) (forall (s : β), (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) s S) -> (Eq.{succ u1} α (f s) (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) _inst_2))))
Case conversion may be inaccurate. Consider using '#align finset.sup_eq_bot_iff Finset.sup_eq_bot_iffₓ'. -/
@[simp]
protected theorem sup_eq_bot_iff (f : β → α) (S : Finset β) : S.sup f = ⊥ ↔ ∀ s ∈ S, f s = ⊥ := by
  classical induction' S using Finset.induction with a S haS hi <;> simp [*]
#align finset.sup_eq_bot_iff Finset.sup_eq_bot_iff

end Sup

/- warning: finset.sup_eq_supr -> Finset.sup_eq_iSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u2} β] (s : Finset.{u1} α) (f : α -> β), Eq.{succ u2} β (Finset.sup.{u2, u1} β α (Lattice.toSemilatticeSup.{u2} β (CompleteLattice.toLattice.{u2} β _inst_1)) (BoundedOrder.toOrderBot.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β (Lattice.toSemilatticeSup.{u2} β (CompleteLattice.toLattice.{u2} β _inst_1))))) (CompleteLattice.toBoundedOrder.{u2} β _inst_1)) s f) (iSup.{u2, succ u1} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) α (fun (a : α) => iSup.{u2, 0} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => f a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u2} β] (s : Finset.{u1} α) (f : α -> β), Eq.{succ u2} β (Finset.sup.{u2, u1} β α (Lattice.toSemilatticeSup.{u2} β (CompleteLattice.toLattice.{u2} β _inst_1)) (BoundedOrder.toOrderBot.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β (Lattice.toSemilatticeSup.{u2} β (CompleteLattice.toLattice.{u2} β _inst_1))))) (CompleteLattice.toBoundedOrder.{u2} β _inst_1)) s f) (iSup.{u2, succ u1} β (CompleteLattice.toSupSet.{u2} β _inst_1) α (fun (a : α) => iSup.{u2, 0} β (CompleteLattice.toSupSet.{u2} β _inst_1) (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) => f a)))
Case conversion may be inaccurate. Consider using '#align finset.sup_eq_supr Finset.sup_eq_iSupₓ'. -/
theorem sup_eq_iSup [CompleteLattice β] (s : Finset α) (f : α → β) : s.sup f = ⨆ a ∈ s, f a :=
  le_antisymm (Finset.sup_le fun a ha => le_iSup_of_le a <| le_iSup _ ha)
    (iSup_le fun a => iSup_le fun ha => le_sup ha)
#align finset.sup_eq_supr Finset.sup_eq_iSup

/- warning: finset.sup_id_eq_Sup -> Finset.sup_id_eq_sSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (s : Finset.{u1} α), Eq.{succ u1} α (Finset.sup.{u1, u1} α α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) s (id.{succ u1} α)) (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (s : Finset.{u1} α), Eq.{succ u1} α (Finset.sup.{u1, u1} α α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) s (id.{succ u1} α)) (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Finset.toSet.{u1} α s))
Case conversion may be inaccurate. Consider using '#align finset.sup_id_eq_Sup Finset.sup_id_eq_sSupₓ'. -/
theorem sup_id_eq_sSup [CompleteLattice α] (s : Finset α) : s.sup id = sSup s := by
  simp [sSup_eq_iSup, sup_eq_iSup]
#align finset.sup_id_eq_Sup Finset.sup_id_eq_sSup

/- warning: finset.sup_id_set_eq_sUnion -> Finset.sup_id_set_eq_sUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Finset.{u1} (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Finset.sup.{u1, u1} (Set.{u1} α) (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (CompleteLattice.toLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s (id.{succ u1} (Set.{u1} α))) (Set.sUnion.{u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} (Set.{u1} α)) (Set.{u1} (Set.{u1} α)) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} (Set.{u1} α)) (Set.{u1} (Set.{u1} α)) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} (Set.{u1} α)) (Set.{u1} (Set.{u1} α)) (Finset.Set.hasCoeT.{u1} (Set.{u1} α)))) s))
but is expected to have type
  forall {α : Type.{u1}} (s : Finset.{u1} (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Finset.sup.{u1, u1} (Set.{u1} α) (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (CompleteLattice.toLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeSup.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (CompleteLattice.toLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) s (id.{succ u1} (Set.{u1} α))) (Set.sUnion.{u1} α (Finset.toSet.{u1} (Set.{u1} α) s))
Case conversion may be inaccurate. Consider using '#align finset.sup_id_set_eq_sUnion Finset.sup_id_set_eq_sUnionₓ'. -/
theorem sup_id_set_eq_sUnion (s : Finset (Set α)) : s.sup id = ⋃₀ ↑s :=
  sup_id_eq_sSup _
#align finset.sup_id_set_eq_sUnion Finset.sup_id_set_eq_sUnion

/- warning: finset.sup_set_eq_bUnion -> Finset.sup_set_eq_biUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Finset.{u1} α) (f : α -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Finset.sup.{u2, u1} (Set.{u2} β) α (Lattice.toSemilatticeSup.{u2} (Set.{u2} β) (CompleteLattice.toLattice.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β))) s f) (Set.iUnion.{u2, succ u1} β α (fun (x : α) => Set.iUnion.{u2, 0} β (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) => f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Finset.{u2} α) (f : α -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Finset.sup.{u1, u2} (Set.{u1} β) α (Lattice.toSemilatticeSup.{u1} (Set.{u1} β) (CompleteLattice.toLattice.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} β) (Preorder.toLE.{u1} (Set.{u1} β) (PartialOrder.toPreorder.{u1} (Set.{u1} β) (SemilatticeSup.toPartialOrder.{u1} (Set.{u1} β) (Lattice.toSemilatticeSup.{u1} (Set.{u1} β) (CompleteLattice.toLattice.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β)))))) s f) (Set.iUnion.{u1, succ u2} β α (fun (x : α) => Set.iUnion.{u1, 0} β (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) => f x)))
Case conversion may be inaccurate. Consider using '#align finset.sup_set_eq_bUnion Finset.sup_set_eq_biUnionₓ'. -/
@[simp]
theorem sup_set_eq_biUnion (s : Finset α) (f : α → Set β) : s.sup f = ⋃ x ∈ s, f x :=
  sup_eq_iSup _ _
#align finset.sup_set_eq_bUnion Finset.sup_set_eq_biUnion

/- warning: finset.sup_eq_Sup_image -> Finset.sup_eq_sSup_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u2} β] (s : Finset.{u1} α) (f : α -> β), Eq.{succ u2} β (Finset.sup.{u2, u1} β α (Lattice.toSemilatticeSup.{u2} β (CompleteLattice.toLattice.{u2} β _inst_1)) (BoundedOrder.toOrderBot.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β (Lattice.toSemilatticeSup.{u2} β (CompleteLattice.toLattice.{u2} β _inst_1))))) (CompleteLattice.toBoundedOrder.{u2} β _inst_1)) s f) (SupSet.sSup.{u2} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) (Set.image.{u1, u2} α β f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u2} β] (s : Finset.{u1} α) (f : α -> β), Eq.{succ u2} β (Finset.sup.{u2, u1} β α (Lattice.toSemilatticeSup.{u2} β (CompleteLattice.toLattice.{u2} β _inst_1)) (BoundedOrder.toOrderBot.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β (Lattice.toSemilatticeSup.{u2} β (CompleteLattice.toLattice.{u2} β _inst_1))))) (CompleteLattice.toBoundedOrder.{u2} β _inst_1)) s f) (SupSet.sSup.{u2} β (CompleteLattice.toSupSet.{u2} β _inst_1) (Set.image.{u1, u2} α β f (Finset.toSet.{u1} α s)))
Case conversion may be inaccurate. Consider using '#align finset.sup_eq_Sup_image Finset.sup_eq_sSup_imageₓ'. -/
theorem sup_eq_sSup_image [CompleteLattice β] (s : Finset α) (f : α → β) :
    s.sup f = sSup (f '' s) := by
  classical rw [← Finset.coe_image, ← sup_id_eq_Sup, sup_image, Function.comp.left_id]
#align finset.sup_eq_Sup_image Finset.sup_eq_sSup_image

/-! ### inf -/


section Inf

-- TODO: define with just `[has_top α]` where some lemmas hold without requiring `[order_top α]`
variable [SemilatticeInf α] [OrderTop α]

/- warning: finset.inf -> Finset.inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))], (Finset.{u2} β) -> (β -> α) -> α
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))], (Finset.{u2} β) -> (β -> α) -> α
Case conversion may be inaccurate. Consider using '#align finset.inf Finset.infₓ'. -/
/-- Infimum of a finite set: `inf {a, b, c} f = f a ⊓ f b ⊓ f c` -/
def inf (s : Finset β) (f : β → α) : α :=
  s.fold (· ⊓ ·) ⊤ f
#align finset.inf Finset.inf

variable {s s₁ s₂ : Finset β} {f g : β → α} {a : α}

/- warning: finset.inf_def -> Finset.inf_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} {f : β -> α}, Eq.{succ u1} α (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s f) (Multiset.inf.{u1} α _inst_1 _inst_2 (Multiset.map.{u2, u1} β α f (Finset.val.{u2} β s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SemilatticeInf.{u2} α] [_inst_2 : OrderTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1)))] {s : Finset.{u1} β} {f : β -> α}, Eq.{succ u2} α (Finset.inf.{u2, u1} α β _inst_1 _inst_2 s f) (Multiset.inf.{u2} α _inst_1 _inst_2 (Multiset.map.{u1, u2} β α f (Finset.val.{u1} β s)))
Case conversion may be inaccurate. Consider using '#align finset.inf_def Finset.inf_defₓ'. -/
theorem inf_def : s.inf f = (s.1.map f).inf :=
  rfl
#align finset.inf_def Finset.inf_def

/- warning: finset.inf_empty -> Finset.inf_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {f : β -> α}, Eq.{succ u1} α (Finset.inf.{u1, u2} α β _inst_1 _inst_2 (EmptyCollection.emptyCollection.{u2} (Finset.{u2} β) (Finset.hasEmptyc.{u2} β)) f) (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SemilatticeInf.{u2} α] [_inst_2 : OrderTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1)))] {f : β -> α}, Eq.{succ u2} α (Finset.inf.{u2, u1} α β _inst_1 _inst_2 (EmptyCollection.emptyCollection.{u1} (Finset.{u1} β) (Finset.instEmptyCollectionFinset.{u1} β)) f) (Top.top.{u2} α (OrderTop.toTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1))) _inst_2))
Case conversion may be inaccurate. Consider using '#align finset.inf_empty Finset.inf_emptyₓ'. -/
@[simp]
theorem inf_empty : (∅ : Finset β).inf f = ⊤ :=
  fold_empty
#align finset.inf_empty Finset.inf_empty

/- warning: finset.inf_cons -> Finset.inf_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} {f : β -> α} {b : β} (h : Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s)), Eq.{succ u1} α (Finset.inf.{u1, u2} α β _inst_1 _inst_2 (Finset.cons.{u2} β b s h) f) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1) (f b) (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} {f : β -> α} {b : β} (h : Not (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b s)), Eq.{succ u1} α (Finset.inf.{u1, u2} α β _inst_1 _inst_2 (Finset.cons.{u2} β b s h) f) (Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_1) (f b) (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s f))
Case conversion may be inaccurate. Consider using '#align finset.inf_cons Finset.inf_consₓ'. -/
@[simp]
theorem inf_cons {b : β} (h : b ∉ s) : (cons b s h).inf f = f b ⊓ s.inf f :=
  @sup_cons αᵒᵈ _ _ _ _ _ _ h
#align finset.inf_cons Finset.inf_cons

/- warning: finset.inf_insert -> Finset.inf_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} {f : β -> α} [_inst_3 : DecidableEq.{succ u2} β] {b : β}, Eq.{succ u1} α (Finset.inf.{u1, u2} α β _inst_1 _inst_2 (Insert.insert.{u2, u2} β (Finset.{u2} β) (Finset.hasInsert.{u2} β (fun (a : β) (b : β) => _inst_3 a b)) b s) f) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1) (f b) (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} {f : β -> α} [_inst_3 : DecidableEq.{succ u2} β] {b : β}, Eq.{succ u1} α (Finset.inf.{u1, u2} α β _inst_1 _inst_2 (Insert.insert.{u2, u2} β (Finset.{u2} β) (Finset.instInsertFinset.{u2} β (fun (a : β) (b : β) => _inst_3 a b)) b s) f) (Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_1) (f b) (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s f))
Case conversion may be inaccurate. Consider using '#align finset.inf_insert Finset.inf_insertₓ'. -/
@[simp]
theorem inf_insert [DecidableEq β] {b : β} : (insert b s : Finset β).inf f = f b ⊓ s.inf f :=
  fold_insert_idem
#align finset.inf_insert Finset.inf_insert

/- warning: finset.inf_image -> Finset.inf_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : DecidableEq.{succ u2} β] (s : Finset.{u3} γ) (f : γ -> β) (g : β -> α), Eq.{succ u1} α (Finset.inf.{u1, u2} α β _inst_1 _inst_2 (Finset.image.{u3, u2} γ β (fun (a : β) (b : β) => _inst_3 a b) f s) g) (Finset.inf.{u1, u3} α γ _inst_1 _inst_2 s (Function.comp.{succ u3, succ u2, succ u1} γ β α g f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : DecidableEq.{succ u3} β] (s : Finset.{u2} γ) (f : γ -> β) (g : β -> α), Eq.{succ u1} α (Finset.inf.{u1, u3} α β _inst_1 _inst_2 (Finset.image.{u2, u3} γ β (fun (a : β) (b : β) => _inst_3 a b) f s) g) (Finset.inf.{u1, u2} α γ _inst_1 _inst_2 s (Function.comp.{succ u2, succ u3, succ u1} γ β α g f))
Case conversion may be inaccurate. Consider using '#align finset.inf_image Finset.inf_imageₓ'. -/
theorem inf_image [DecidableEq β] (s : Finset γ) (f : γ → β) (g : β → α) :
    (s.image f).inf g = s.inf (g ∘ f) :=
  fold_image_idem
#align finset.inf_image Finset.inf_image

/- warning: finset.inf_map -> Finset.inf_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] (s : Finset.{u3} γ) (f : Function.Embedding.{succ u3, succ u2} γ β) (g : β -> α), Eq.{succ u1} α (Finset.inf.{u1, u2} α β _inst_1 _inst_2 (Finset.map.{u3, u2} γ β f s) g) (Finset.inf.{u1, u3} α γ _inst_1 _inst_2 s (Function.comp.{succ u3, succ u2, succ u1} γ β α g (coeFn.{max 1 (succ u3) (succ u2), max (succ u3) (succ u2)} (Function.Embedding.{succ u3, succ u2} γ β) (fun (_x : Function.Embedding.{succ u3, succ u2} γ β) => γ -> β) (Function.Embedding.hasCoeToFun.{succ u3, succ u2} γ β) f)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] (s : Finset.{u3} γ) (f : Function.Embedding.{succ u3, succ u2} γ β) (g : β -> α), Eq.{succ u1} α (Finset.inf.{u1, u2} α β _inst_1 _inst_2 (Finset.map.{u3, u2} γ β f s) g) (Finset.inf.{u1, u3} α γ _inst_1 _inst_2 s (Function.comp.{succ u3, succ u2, succ u1} γ β α g (FunLike.coe.{max (succ u2) (succ u3), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} γ β) γ (fun (_x : γ) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : γ) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u3), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} γ β) γ β (Function.instEmbeddingLikeEmbedding.{succ u3, succ u2} γ β)) f)))
Case conversion may be inaccurate. Consider using '#align finset.inf_map Finset.inf_mapₓ'. -/
@[simp]
theorem inf_map (s : Finset γ) (f : γ ↪ β) (g : β → α) : (s.map f).inf g = s.inf (g ∘ f) :=
  fold_map
#align finset.inf_map Finset.inf_map

/- warning: finset.inf_singleton -> Finset.inf_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {f : β -> α} {b : β}, Eq.{succ u1} α (Finset.inf.{u1, u2} α β _inst_1 _inst_2 (Singleton.singleton.{u2, u2} β (Finset.{u2} β) (Finset.hasSingleton.{u2} β) b) f) (f b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SemilatticeInf.{u2} α] [_inst_2 : OrderTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1)))] {f : β -> α} {b : β}, Eq.{succ u2} α (Finset.inf.{u2, u1} α β _inst_1 _inst_2 (Singleton.singleton.{u1, u1} β (Finset.{u1} β) (Finset.instSingletonFinset.{u1} β) b) f) (f b)
Case conversion may be inaccurate. Consider using '#align finset.inf_singleton Finset.inf_singletonₓ'. -/
@[simp]
theorem inf_singleton {b : β} : ({b} : Finset β).inf f = f b :=
  inf_singleton
#align finset.inf_singleton Finset.inf_singleton

/- warning: finset.inf_union -> Finset.inf_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s₁ : Finset.{u2} β} {s₂ : Finset.{u2} β} {f : β -> α} [_inst_3 : DecidableEq.{succ u2} β], Eq.{succ u1} α (Finset.inf.{u1, u2} α β _inst_1 _inst_2 (Union.union.{u2} (Finset.{u2} β) (Finset.hasUnion.{u2} β (fun (a : β) (b : β) => _inst_3 a b)) s₁ s₂) f) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1) (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s₁ f) (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s₂ f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s₁ : Finset.{u2} β} {s₂ : Finset.{u2} β} {f : β -> α} [_inst_3 : DecidableEq.{succ u2} β], Eq.{succ u1} α (Finset.inf.{u1, u2} α β _inst_1 _inst_2 (Union.union.{u2} (Finset.{u2} β) (Finset.instUnionFinset.{u2} β (fun (a : β) (b : β) => _inst_3 a b)) s₁ s₂) f) (Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_1) (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s₁ f) (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s₂ f))
Case conversion may be inaccurate. Consider using '#align finset.inf_union Finset.inf_unionₓ'. -/
theorem inf_union [DecidableEq β] : (s₁ ∪ s₂).inf f = s₁.inf f ⊓ s₂.inf f :=
  @sup_union αᵒᵈ _ _ _ _ _ _ _
#align finset.inf_union Finset.inf_union

/- warning: finset.inf_inf -> Finset.inf_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} {f : β -> α} {g : β -> α}, Eq.{succ u1} α (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s (Inf.inf.{max u2 u1} (β -> α) (Pi.hasInf.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => SemilatticeInf.toHasInf.{u1} α _inst_1)) f g)) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1) (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s f) (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s g))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SemilatticeInf.{u2} α] [_inst_2 : OrderTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1)))] {s : Finset.{u1} β} {f : β -> α} {g : β -> α}, Eq.{succ u2} α (Finset.inf.{u2, u1} α β _inst_1 _inst_2 s (Inf.inf.{max u1 u2} (β -> α) (Pi.instInfForAll.{u1, u2} β (fun (ᾰ : β) => α) (fun (i : β) => SemilatticeInf.toInf.{u2} α _inst_1)) f g)) (Inf.inf.{u2} α (SemilatticeInf.toInf.{u2} α _inst_1) (Finset.inf.{u2, u1} α β _inst_1 _inst_2 s f) (Finset.inf.{u2, u1} α β _inst_1 _inst_2 s g))
Case conversion may be inaccurate. Consider using '#align finset.inf_inf Finset.inf_infₓ'. -/
theorem inf_inf : s.inf (f ⊓ g) = s.inf f ⊓ s.inf g :=
  @sup_sup αᵒᵈ _ _ _ _ _ _
#align finset.inf_inf Finset.inf_inf

/- warning: finset.inf_congr -> Finset.inf_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s₁ : Finset.{u2} β} {s₂ : Finset.{u2} β} {f : β -> α} {g : β -> α}, (Eq.{succ u2} (Finset.{u2} β) s₁ s₂) -> (forall (a : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a s₂) -> (Eq.{succ u1} α (f a) (g a))) -> (Eq.{succ u1} α (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s₁ f) (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s₂ g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s₁ : Finset.{u2} β} {s₂ : Finset.{u2} β} {f : β -> α} {g : β -> α}, (Eq.{succ u2} (Finset.{u2} β) s₁ s₂) -> (forall (a : β), (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) a s₂) -> (Eq.{succ u1} α (f a) (g a))) -> (Eq.{succ u1} α (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s₁ f) (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s₂ g))
Case conversion may be inaccurate. Consider using '#align finset.inf_congr Finset.inf_congrₓ'. -/
theorem inf_congr {f g : β → α} (hs : s₁ = s₂) (hfg : ∀ a ∈ s₂, f a = g a) : s₁.inf f = s₂.inf g :=
  by subst hs <;> exact Finset.fold_congr hfg
#align finset.inf_congr Finset.inf_congr

/- warning: map_finset_inf -> map_finset_inf is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {ι : Type.{u4}} [_inst_1 : SemilatticeInf.{u2} α] [_inst_2 : OrderTop.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1)))] [_inst_3 : SemilatticeInf.{u3} β] [_inst_4 : OrderTop.{u3} β (Preorder.toHasLe.{u3} β (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β _inst_3)))] [_inst_5 : InfTopHomClass.{u1, u2, u3} F α β (SemilatticeInf.toHasInf.{u2} α _inst_1) (SemilatticeInf.toHasInf.{u3} β _inst_3) (OrderTop.toHasTop.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1))) _inst_2) (OrderTop.toHasTop.{u3} β (Preorder.toHasLe.{u3} β (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β _inst_3))) _inst_4)] (f : F) (s : Finset.{u4} ι) (g : ι -> α), Eq.{succ u3} β (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (InfHomClass.toFunLike.{u1, u2, u3} F α β (SemilatticeInf.toHasInf.{u2} α _inst_1) (SemilatticeInf.toHasInf.{u3} β _inst_3) (InfTopHomClass.toInfHomClass.{u1, u2, u3} F α β (SemilatticeInf.toHasInf.{u2} α _inst_1) (SemilatticeInf.toHasInf.{u3} β _inst_3) (OrderTop.toHasTop.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1))) _inst_2) (OrderTop.toHasTop.{u3} β (Preorder.toHasLe.{u3} β (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β _inst_3))) _inst_4) _inst_5))) f (Finset.inf.{u2, u4} α ι _inst_1 _inst_2 s g)) (Finset.inf.{u3, u4} β ι _inst_3 _inst_4 s (Function.comp.{succ u4, succ u2, succ u3} ι α β (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (InfHomClass.toFunLike.{u1, u2, u3} F α β (SemilatticeInf.toHasInf.{u2} α _inst_1) (SemilatticeInf.toHasInf.{u3} β _inst_3) (InfTopHomClass.toInfHomClass.{u1, u2, u3} F α β (SemilatticeInf.toHasInf.{u2} α _inst_1) (SemilatticeInf.toHasInf.{u3} β _inst_3) (OrderTop.toHasTop.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1))) _inst_2) (OrderTop.toHasTop.{u3} β (Preorder.toHasLe.{u3} β (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β _inst_3))) _inst_4) _inst_5))) f) g))
but is expected to have type
  forall {F : Type.{u3}} {α : Type.{u2}} {β : Type.{u4}} {ι : Type.{u1}} [_inst_1 : SemilatticeInf.{u2} α] [_inst_2 : OrderTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1)))] [_inst_3 : SemilatticeInf.{u4} β] [_inst_4 : OrderTop.{u4} β (Preorder.toLE.{u4} β (PartialOrder.toPreorder.{u4} β (SemilatticeInf.toPartialOrder.{u4} β _inst_3)))] [_inst_5 : InfTopHomClass.{u3, u2, u4} F α β (SemilatticeInf.toInf.{u2} α _inst_1) (SemilatticeInf.toInf.{u4} β _inst_3) (OrderTop.toTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1))) _inst_2) (OrderTop.toTop.{u4} β (Preorder.toLE.{u4} β (PartialOrder.toPreorder.{u4} β (SemilatticeInf.toPartialOrder.{u4} β _inst_3))) _inst_4)] (f : F) (s : Finset.{u1} ι) (g : ι -> α), Eq.{succ u4} ((fun (x._@.Mathlib.Order.Hom.Lattice._hyg.494 : α) => β) (Finset.inf.{u2, u1} α ι _inst_1 _inst_2 s g)) (FunLike.coe.{succ u3, succ u2, succ u4} F α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.Lattice._hyg.494 : α) => β) _x) (InfHomClass.toFunLike.{u3, u2, u4} F α β (SemilatticeInf.toInf.{u2} α _inst_1) (SemilatticeInf.toInf.{u4} β _inst_3) (InfTopHomClass.toInfHomClass.{u3, u2, u4} F α β (SemilatticeInf.toInf.{u2} α _inst_1) (SemilatticeInf.toInf.{u4} β _inst_3) (OrderTop.toTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1))) _inst_2) (OrderTop.toTop.{u4} β (Preorder.toLE.{u4} β (PartialOrder.toPreorder.{u4} β (SemilatticeInf.toPartialOrder.{u4} β _inst_3))) _inst_4) _inst_5)) f (Finset.inf.{u2, u1} α ι _inst_1 _inst_2 s g)) (Finset.inf.{u4, u1} β ι _inst_3 _inst_4 s (Function.comp.{succ u1, succ u2, succ u4} ι α β (FunLike.coe.{succ u3, succ u2, succ u4} F α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.Lattice._hyg.494 : α) => β) _x) (InfHomClass.toFunLike.{u3, u2, u4} F α β (SemilatticeInf.toInf.{u2} α _inst_1) (SemilatticeInf.toInf.{u4} β _inst_3) (InfTopHomClass.toInfHomClass.{u3, u2, u4} F α β (SemilatticeInf.toInf.{u2} α _inst_1) (SemilatticeInf.toInf.{u4} β _inst_3) (OrderTop.toTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1))) _inst_2) (OrderTop.toTop.{u4} β (Preorder.toLE.{u4} β (PartialOrder.toPreorder.{u4} β (SemilatticeInf.toPartialOrder.{u4} β _inst_3))) _inst_4) _inst_5)) f) g))
Case conversion may be inaccurate. Consider using '#align map_finset_inf map_finset_infₓ'. -/
@[simp]
theorem map_finset_inf [SemilatticeInf β] [OrderTop β] [InfTopHomClass F α β] (f : F) (s : Finset ι)
    (g : ι → α) : f (s.inf g) = s.inf (f ∘ g) :=
  Finset.cons_induction_on s (map_top f) fun i s _ h => by rw [inf_cons, inf_cons, map_inf, h]
#align map_finset_inf map_finset_inf

/- warning: finset.inf_bUnion -> Finset.inf_biUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {f : β -> α} [_inst_3 : DecidableEq.{succ u2} β] (s : Finset.{u3} γ) (t : γ -> (Finset.{u2} β)), Eq.{succ u1} α (Finset.inf.{u1, u2} α β _inst_1 _inst_2 (Finset.biUnion.{u3, u2} γ β (fun (a : β) (b : β) => _inst_3 a b) s t) f) (Finset.inf.{u1, u3} α γ _inst_1 _inst_2 s (fun (x : γ) => Finset.inf.{u1, u2} α β _inst_1 _inst_2 (t x) f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {f : β -> α} [_inst_3 : DecidableEq.{succ u3} β] (s : Finset.{u2} γ) (t : γ -> (Finset.{u3} β)), Eq.{succ u1} α (Finset.inf.{u1, u3} α β _inst_1 _inst_2 (Finset.biUnion.{u2, u3} γ β (fun (a : β) (b : β) => _inst_3 a b) s t) f) (Finset.inf.{u1, u2} α γ _inst_1 _inst_2 s (fun (x : γ) => Finset.inf.{u1, u3} α β _inst_1 _inst_2 (t x) f))
Case conversion may be inaccurate. Consider using '#align finset.inf_bUnion Finset.inf_biUnionₓ'. -/
@[simp]
theorem inf_biUnion [DecidableEq β] (s : Finset γ) (t : γ → Finset β) :
    (s.biUnion t).inf f = s.inf fun x => (t x).inf f :=
  @sup_biUnion αᵒᵈ _ _ _ _ _ _ _ _
#align finset.inf_bUnion Finset.inf_biUnion

/- warning: finset.inf_const -> Finset.inf_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β}, (Finset.Nonempty.{u2} β s) -> (forall (c : α), Eq.{succ u1} α (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s (fun (_x : β) => c)) c)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β}, (Finset.Nonempty.{u2} β s) -> (forall (c : α), Eq.{succ u1} α (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s (fun (_x : β) => c)) c)
Case conversion may be inaccurate. Consider using '#align finset.inf_const Finset.inf_constₓ'. -/
theorem inf_const {s : Finset β} (h : s.Nonempty) (c : α) : (s.inf fun _ => c) = c :=
  @sup_const αᵒᵈ _ _ _ _ h _
#align finset.inf_const Finset.inf_const

/- warning: finset.inf_top -> Finset.inf_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] (s : Finset.{u2} β), Eq.{succ u1} α (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s (fun (_x : β) => Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2))) (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] (s : Finset.{u2} β), Eq.{succ u1} α (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s (fun (_x : β) => Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2))) (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2))
Case conversion may be inaccurate. Consider using '#align finset.inf_top Finset.inf_topₓ'. -/
@[simp]
theorem inf_top (s : Finset β) : (s.inf fun _ => ⊤) = (⊤ : α) :=
  @sup_bot αᵒᵈ _ _ _ _
#align finset.inf_top Finset.inf_top

/- warning: finset.le_inf_iff -> Finset.le_inf_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} {f : β -> α} {a : α}, Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) a (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s f)) (forall (b : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) a (f b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SemilatticeInf.{u2} α] [_inst_2 : OrderTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1)))] {s : Finset.{u1} β} {f : β -> α} {a : α}, Iff (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1))) a (Finset.inf.{u2, u1} α β _inst_1 _inst_2 s f)) (forall (b : β), (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) b s) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1))) a (f b)))
Case conversion may be inaccurate. Consider using '#align finset.le_inf_iff Finset.le_inf_iffₓ'. -/
protected theorem le_inf_iff {a : α} : a ≤ s.inf f ↔ ∀ b ∈ s, a ≤ f b :=
  @Finset.sup_le_iff αᵒᵈ _ _ _ _ _ _
#align finset.le_inf_iff Finset.le_inf_iff

/- warning: finset.le_inf -> Finset.le_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} {f : β -> α} {a : α}, (forall (b : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) a (f b))) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) a (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SemilatticeInf.{u2} α] [_inst_2 : OrderTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1)))] {s : Finset.{u1} β} {f : β -> α} {a : α}, (forall (b : β), (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) b s) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1))) a (f b))) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1))) a (Finset.inf.{u2, u1} α β _inst_1 _inst_2 s f))
Case conversion may be inaccurate. Consider using '#align finset.le_inf Finset.le_infₓ'. -/
alias Finset.le_inf_iff ↔ _ le_inf
#align finset.le_inf Finset.le_inf

attribute [protected] le_inf

/- warning: finset.le_inf_const_le -> Finset.le_inf_const_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} {a : α}, LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) a (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s (fun (_x : β) => a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SemilatticeInf.{u2} α] [_inst_2 : OrderTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1)))] {s : Finset.{u1} β} {a : α}, LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1))) a (Finset.inf.{u2, u1} α β _inst_1 _inst_2 s (fun (_x : β) => a))
Case conversion may be inaccurate. Consider using '#align finset.le_inf_const_le Finset.le_inf_const_leₓ'. -/
theorem le_inf_const_le : a ≤ s.inf fun _ => a :=
  Finset.le_inf fun _ _ => le_rfl
#align finset.le_inf_const_le Finset.le_inf_const_le

/- warning: finset.inf_le -> Finset.inf_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} {f : β -> α} {b : β}, (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s f) (f b))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} {f : β -> α} {b : β}, (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s f) (f b))
Case conversion may be inaccurate. Consider using '#align finset.inf_le Finset.inf_leₓ'. -/
theorem inf_le {b : β} (hb : b ∈ s) : s.inf f ≤ f b :=
  Finset.le_inf_iff.1 le_rfl _ hb
#align finset.inf_le Finset.inf_le

/- warning: finset.inf_le_of_le -> Finset.inf_le_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} {f : β -> α} {a : α} {b : β}, (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) (f b) a) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s f) a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} {f : β -> α} {a : α} {b : β}, (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) (f b) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s f) a)
Case conversion may be inaccurate. Consider using '#align finset.inf_le_of_le Finset.inf_le_of_leₓ'. -/
theorem inf_le_of_le {b : β} (hb : b ∈ s) (h : f b ≤ a) : s.inf f ≤ a :=
  (inf_le hb).trans h
#align finset.inf_le_of_le Finset.inf_le_of_le

/- warning: finset.inf_mono_fun -> Finset.inf_mono_fun is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} {f : β -> α} {g : β -> α}, (forall (b : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) (f b) (g b))) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s f) (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} {f : β -> α} {g : β -> α}, (forall (b : β), (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) (f b) (g b))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s f) (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s g))
Case conversion may be inaccurate. Consider using '#align finset.inf_mono_fun Finset.inf_mono_funₓ'. -/
theorem inf_mono_fun {g : β → α} (h : ∀ b ∈ s, f b ≤ g b) : s.inf f ≤ s.inf g :=
  Finset.le_inf fun b hb => le_trans (inf_le hb) (h b hb)
#align finset.inf_mono_fun Finset.inf_mono_fun

/- warning: finset.inf_mono -> Finset.inf_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s₁ : Finset.{u2} β} {s₂ : Finset.{u2} β} {f : β -> α}, (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) s₁ s₂) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s₂ f) (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s₁ f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s₁ : Finset.{u2} β} {s₂ : Finset.{u2} β} {f : β -> α}, (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.instHasSubsetFinset.{u2} β) s₁ s₂) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s₂ f) (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s₁ f))
Case conversion may be inaccurate. Consider using '#align finset.inf_mono Finset.inf_monoₓ'. -/
theorem inf_mono (h : s₁ ⊆ s₂) : s₂.inf f ≤ s₁.inf f :=
  Finset.le_inf fun b hb => inf_le <| h hb
#align finset.inf_mono Finset.inf_mono

/- warning: finset.inf_attach -> Finset.inf_attach is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] (s : Finset.{u2} β) (f : β -> α), Eq.{succ u1} α (Finset.inf.{u1, u2} α (Subtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s)) _inst_1 _inst_2 (Finset.attach.{u2} β s) (fun (x : Subtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s)) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Subtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s)) β (HasLiftT.mk.{succ u2, succ u2} (Subtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s)) β (CoeTCₓ.coe.{succ u2, succ u2} (Subtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s)) β (coeBase.{succ u2, succ u2} (Subtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s)) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s))))) x))) (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] (s : Finset.{u2} β) (f : β -> α), Eq.{succ u1} α (Finset.inf.{u1, u2} α (Subtype.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) x s)) _inst_1 _inst_2 (Finset.attach.{u2} β s) (fun (x : Subtype.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) x s)) => f (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) x s) x))) (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s f)
Case conversion may be inaccurate. Consider using '#align finset.inf_attach Finset.inf_attachₓ'. -/
theorem inf_attach (s : Finset β) (f : β → α) : (s.attach.inf fun x => f x) = s.inf f :=
  @sup_attach αᵒᵈ _ _ _ _ _
#align finset.inf_attach Finset.inf_attach

/- warning: finset.inf_comm -> Finset.inf_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] (s : Finset.{u2} β) (t : Finset.{u3} γ) (f : β -> γ -> α), Eq.{succ u1} α (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s (fun (b : β) => Finset.inf.{u1, u3} α γ _inst_1 _inst_2 t (f b))) (Finset.inf.{u1, u3} α γ _inst_1 _inst_2 t (fun (c : γ) => Finset.inf.{u1, u2} α β _inst_1 _inst_2 s (fun (b : β) => f b c)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] (s : Finset.{u3} β) (t : Finset.{u2} γ) (f : β -> γ -> α), Eq.{succ u1} α (Finset.inf.{u1, u3} α β _inst_1 _inst_2 s (fun (b : β) => Finset.inf.{u1, u2} α γ _inst_1 _inst_2 t (f b))) (Finset.inf.{u1, u2} α γ _inst_1 _inst_2 t (fun (c : γ) => Finset.inf.{u1, u3} α β _inst_1 _inst_2 s (fun (b : β) => f b c)))
Case conversion may be inaccurate. Consider using '#align finset.inf_comm Finset.inf_commₓ'. -/
protected theorem inf_comm (s : Finset β) (t : Finset γ) (f : β → γ → α) :
    (s.inf fun b => t.inf (f b)) = t.inf fun c => s.inf fun b => f b c :=
  @Finset.sup_comm αᵒᵈ _ _ _ _ _ _ _
#align finset.inf_comm Finset.inf_comm

/- warning: finset.inf_product_left -> Finset.inf_product_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] (s : Finset.{u2} β) (t : Finset.{u3} γ) (f : (Prod.{u2, u3} β γ) -> α), Eq.{succ u1} α (Finset.inf.{u1, max u2 u3} α (Prod.{u2, u3} β γ) _inst_1 _inst_2 (Finset.product.{u2, u3} β γ s t) f) (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s (fun (i : β) => Finset.inf.{u1, u3} α γ _inst_1 _inst_2 t (fun (i' : γ) => f (Prod.mk.{u2, u3} β γ i i'))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] (s : Finset.{u3} β) (t : Finset.{u2} γ) (f : (Prod.{u3, u2} β γ) -> α), Eq.{succ u1} α (Finset.inf.{u1, max u3 u2} α (Prod.{u3, u2} β γ) _inst_1 _inst_2 (Finset.product.{u3, u2} β γ s t) f) (Finset.inf.{u1, u3} α β _inst_1 _inst_2 s (fun (i : β) => Finset.inf.{u1, u2} α γ _inst_1 _inst_2 t (fun (i' : γ) => f (Prod.mk.{u3, u2} β γ i i'))))
Case conversion may be inaccurate. Consider using '#align finset.inf_product_left Finset.inf_product_leftₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem inf_product_left (s : Finset β) (t : Finset γ) (f : β × γ → α) :
    (s ×ˢ t).inf f = s.inf fun i => t.inf fun i' => f ⟨i, i'⟩ :=
  @sup_product_left αᵒᵈ _ _ _ _ _ _ _
#align finset.inf_product_left Finset.inf_product_left

/- warning: finset.inf_product_right -> Finset.inf_product_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] (s : Finset.{u2} β) (t : Finset.{u3} γ) (f : (Prod.{u2, u3} β γ) -> α), Eq.{succ u1} α (Finset.inf.{u1, max u2 u3} α (Prod.{u2, u3} β γ) _inst_1 _inst_2 (Finset.product.{u2, u3} β γ s t) f) (Finset.inf.{u1, u3} α γ _inst_1 _inst_2 t (fun (i' : γ) => Finset.inf.{u1, u2} α β _inst_1 _inst_2 s (fun (i : β) => f (Prod.mk.{u2, u3} β γ i i'))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] (s : Finset.{u3} β) (t : Finset.{u2} γ) (f : (Prod.{u3, u2} β γ) -> α), Eq.{succ u1} α (Finset.inf.{u1, max u3 u2} α (Prod.{u3, u2} β γ) _inst_1 _inst_2 (Finset.product.{u3, u2} β γ s t) f) (Finset.inf.{u1, u2} α γ _inst_1 _inst_2 t (fun (i' : γ) => Finset.inf.{u1, u3} α β _inst_1 _inst_2 s (fun (i : β) => f (Prod.mk.{u3, u2} β γ i i'))))
Case conversion may be inaccurate. Consider using '#align finset.inf_product_right Finset.inf_product_rightₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem inf_product_right (s : Finset β) (t : Finset γ) (f : β × γ → α) :
    (s ×ˢ t).inf f = t.inf fun i' => s.inf fun i => f ⟨i, i'⟩ :=
  @sup_product_right αᵒᵈ _ _ _ _ _ _ _
#align finset.inf_product_right Finset.inf_product_right

/- warning: finset.inf_erase_top -> Finset.inf_erase_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Eq.{succ u1} α (Finset.inf.{u1, u1} α α _inst_1 _inst_2 (Finset.erase.{u1} α (fun (a : α) (b : α) => _inst_3 a b) s (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2))) (id.{succ u1} α)) (Finset.inf.{u1, u1} α α _inst_1 _inst_2 s (id.{succ u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Eq.{succ u1} α (Finset.inf.{u1, u1} α α _inst_1 _inst_2 (Finset.erase.{u1} α (fun (a : α) (b : α) => _inst_3 a b) s (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2))) (id.{succ u1} α)) (Finset.inf.{u1, u1} α α _inst_1 _inst_2 s (id.{succ u1} α))
Case conversion may be inaccurate. Consider using '#align finset.inf_erase_top Finset.inf_erase_topₓ'. -/
@[simp]
theorem inf_erase_top [DecidableEq α] (s : Finset α) : (s.eraseₓ ⊤).inf id = s.inf id :=
  @sup_erase_bot αᵒᵈ _ _ _ _
#align finset.inf_erase_top Finset.inf_erase_top

/- warning: finset.comp_inf_eq_inf_comp -> Finset.comp_inf_eq_inf_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : SemilatticeInf.{u3} γ] [_inst_4 : OrderTop.{u3} γ (Preorder.toHasLe.{u3} γ (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ _inst_3)))] {s : Finset.{u2} β} {f : β -> α} (g : α -> γ), (forall (x : α) (y : α), Eq.{succ u3} γ (g (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1) x y)) (Inf.inf.{u3} γ (SemilatticeInf.toHasInf.{u3} γ _inst_3) (g x) (g y))) -> (Eq.{succ u3} γ (g (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2))) (Top.top.{u3} γ (OrderTop.toHasTop.{u3} γ (Preorder.toHasLe.{u3} γ (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ _inst_3))) _inst_4))) -> (Eq.{succ u3} γ (g (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s f)) (Finset.inf.{u3, u2} γ β _inst_3 _inst_4 s (Function.comp.{succ u2, succ u1, succ u3} β α γ g f)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : SemilatticeInf.{u3} γ] [_inst_4 : OrderTop.{u3} γ (Preorder.toLE.{u3} γ (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ _inst_3)))] {s : Finset.{u2} β} {f : β -> α} (g : α -> γ), (forall (x : α) (y : α), Eq.{succ u3} γ (g (Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_1) x y)) (Inf.inf.{u3} γ (SemilatticeInf.toInf.{u3} γ _inst_3) (g x) (g y))) -> (Eq.{succ u3} γ (g (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2))) (Top.top.{u3} γ (OrderTop.toTop.{u3} γ (Preorder.toLE.{u3} γ (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ _inst_3))) _inst_4))) -> (Eq.{succ u3} γ (g (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s f)) (Finset.inf.{u3, u2} γ β _inst_3 _inst_4 s (Function.comp.{succ u2, succ u1, succ u3} β α γ g f)))
Case conversion may be inaccurate. Consider using '#align finset.comp_inf_eq_inf_comp Finset.comp_inf_eq_inf_compₓ'. -/
theorem comp_inf_eq_inf_comp [SemilatticeInf γ] [OrderTop γ] {s : Finset β} {f : β → α} (g : α → γ)
    (g_inf : ∀ x y, g (x ⊓ y) = g x ⊓ g y) (top : g ⊤ = ⊤) : g (s.inf f) = s.inf (g ∘ f) :=
  @comp_sup_eq_sup_comp αᵒᵈ _ γᵒᵈ _ _ _ _ _ _ _ g_inf top
#align finset.comp_inf_eq_inf_comp Finset.comp_inf_eq_inf_comp

/- warning: finset.inf_coe -> Finset.inf_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {P : α -> Prop} {Ptop : P (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2))} {Pinf : forall {{x : α}} {{y : α}}, (P x) -> (P y) -> (P (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1) x y))} (t : Finset.{u2} β) (f : β -> (Subtype.{succ u1} α (fun (x : α) => P x))), Eq.{succ u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => P x)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => P x)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => P x)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => P x)) α (coeSubtype.{succ u1} α (fun (x : α) => P x))))) (Finset.inf.{u1, u2} (Subtype.{succ u1} α (fun (x : α) => P x)) β (Subtype.semilatticeInf.{u1} α _inst_1 (fun (x : α) => P x) Pinf) (Subtype.orderTop.{u1} α (fun (x : α) => P x) (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2 Ptop) t f)) (Finset.inf.{u1, u2} α β _inst_1 _inst_2 t (fun (x : β) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => P x)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => P x)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => P x)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => P x)) α (coeSubtype.{succ u1} α (fun (x : α) => P x))))) (f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SemilatticeInf.{u2} α] [_inst_2 : OrderTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1)))] {P : α -> Prop} {Ptop : P (Top.top.{u2} α (OrderTop.toTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1))) _inst_2))} {Pinf : forall {{x : α}} {{y : α}}, (P x) -> (P y) -> (P (Inf.inf.{u2} α (SemilatticeInf.toInf.{u2} α _inst_1) x y))} (t : Finset.{u1} β) (f : β -> (Subtype.{succ u2} α (fun (x : α) => P x))), Eq.{succ u2} α (Subtype.val.{succ u2} α (fun (x : α) => P x) (Finset.inf.{u2, u1} (Subtype.{succ u2} α (fun (x : α) => P x)) β (Subtype.semilatticeInf.{u2} α _inst_1 (fun (x : α) => P x) Pinf) (Subtype.orderTop.{u2} α (fun (x : α) => P x) (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1))) _inst_2 Ptop) t f)) (Finset.inf.{u2, u1} α β _inst_1 _inst_2 t (fun (x : β) => Subtype.val.{succ u2} α (fun (x : α) => P x) (f x)))
Case conversion may be inaccurate. Consider using '#align finset.inf_coe Finset.inf_coeₓ'. -/
/-- Computing `inf` in a subtype (closed under `inf`) is the same as computing it in `α`. -/
theorem inf_coe {P : α → Prop} {Ptop : P ⊤} {Pinf : ∀ ⦃x y⦄, P x → P y → P (x ⊓ y)} (t : Finset β)
    (f : β → { x : α // P x }) :
    (@inf _ _ (Subtype.semilatticeInf Pinf) (Subtype.orderTop Ptop) t f : α) = t.inf fun x => f x :=
  @sup_coe αᵒᵈ _ _ _ _ Ptop Pinf t f
#align finset.inf_coe Finset.inf_coe

/- warning: list.foldr_inf_eq_inf_to_finset -> List.foldr_inf_eq_inf_toFinset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : DecidableEq.{succ u1} α] (l : List.{u1} α), Eq.{succ u1} α (List.foldr.{u1, u1} α α (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1)) (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2)) l) (Finset.inf.{u1, u1} α α _inst_1 _inst_2 (List.toFinset.{u1} α (fun (a : α) (b : α) => _inst_3 a b) l) (id.{succ u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : DecidableEq.{succ u1} α] (l : List.{u1} α), Eq.{succ u1} α (List.foldr.{u1, u1} α α (fun (x._@.Mathlib.Data.Finset.Lattice._hyg.5388 : α) (x._@.Mathlib.Data.Finset.Lattice._hyg.5390 : α) => Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_1) x._@.Mathlib.Data.Finset.Lattice._hyg.5388 x._@.Mathlib.Data.Finset.Lattice._hyg.5390) (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2)) l) (Finset.inf.{u1, u1} α α _inst_1 _inst_2 (List.toFinset.{u1} α (fun (a : α) (b : α) => _inst_3 a b) l) (id.{succ u1} α))
Case conversion may be inaccurate. Consider using '#align list.foldr_inf_eq_inf_to_finset List.foldr_inf_eq_inf_toFinsetₓ'. -/
theorem List.foldr_inf_eq_inf_toFinset [DecidableEq α] (l : List α) :
    l.foldr (· ⊓ ·) ⊤ = l.toFinset.inf id :=
  by
  rw [← coe_fold_r, ← Multiset.fold_dedup_idem, inf_def, ← List.toFinset_coe, to_finset_val,
    Multiset.map_id]
  rfl
#align list.foldr_inf_eq_inf_to_finset List.foldr_inf_eq_inf_toFinset

/- warning: finset.inf_induction -> Finset.inf_induction is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} {f : β -> α} {p : α -> Prop}, (p (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2))) -> (forall (a₁ : α), (p a₁) -> (forall (a₂ : α), (p a₂) -> (p (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1) a₁ a₂)))) -> (forall (b : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s) -> (p (f b))) -> (p (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SemilatticeInf.{u2} α] [_inst_2 : OrderTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1)))] {s : Finset.{u1} β} {f : β -> α} {p : α -> Prop}, (p (Top.top.{u2} α (OrderTop.toTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1))) _inst_2))) -> (forall (a₁ : α), (p a₁) -> (forall (a₂ : α), (p a₂) -> (p (Inf.inf.{u2} α (SemilatticeInf.toInf.{u2} α _inst_1) a₁ a₂)))) -> (forall (b : β), (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) b s) -> (p (f b))) -> (p (Finset.inf.{u2, u1} α β _inst_1 _inst_2 s f))
Case conversion may be inaccurate. Consider using '#align finset.inf_induction Finset.inf_inductionₓ'. -/
theorem inf_induction {p : α → Prop} (ht : p ⊤) (hp : ∀ a₁, p a₁ → ∀ a₂, p a₂ → p (a₁ ⊓ a₂))
    (hs : ∀ b ∈ s, p (f b)) : p (s.inf f) :=
  @sup_induction αᵒᵈ _ _ _ _ _ _ ht hp hs
#align finset.inf_induction Finset.inf_induction

/- warning: finset.inf_mem -> Finset.inf_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] (s : Set.{u1} α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2)) s) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1) x y) s))) -> (forall {ι : Type.{u2}} (t : Finset.{u2} ι) (p : ι -> α), (forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i t) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (p i) s)) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Finset.inf.{u1, u2} α ι _inst_1 _inst_2 t p) s))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : SemilatticeInf.{u2} α] [_inst_2 : OrderTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1)))] (s : Set.{u2} α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (Top.top.{u2} α (OrderTop.toTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1))) _inst_2)) s) -> (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (forall (y : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) y s) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (Inf.inf.{u2} α (SemilatticeInf.toInf.{u2} α _inst_1) x y) s))) -> (forall {ι : Type.{u1}} (t : Finset.{u1} ι) (p : ι -> α), (forall (i : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i t) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (p i) s)) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (Finset.inf.{u2, u1} α ι _inst_1 _inst_2 t p) s))
Case conversion may be inaccurate. Consider using '#align finset.inf_mem Finset.inf_memₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » s) -/
theorem inf_mem (s : Set α) (w₁ : ⊤ ∈ s) (w₂ : ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s), x ⊓ y ∈ s)
    {ι : Type _} (t : Finset ι) (p : ι → α) (h : ∀ i ∈ t, p i ∈ s) : t.inf p ∈ s :=
  @inf_induction _ _ _ _ _ _ (· ∈ s) w₁ w₂ h
#align finset.inf_mem Finset.inf_mem

/- warning: finset.inf_eq_top_iff -> Finset.inf_eq_top_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] (f : β -> α) (S : Finset.{u2} β), Iff (Eq.{succ u1} α (Finset.inf.{u1, u2} α β _inst_1 _inst_2 S f) (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2))) (forall (s : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) s S) -> (Eq.{succ u1} α (f s) (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] (f : β -> α) (S : Finset.{u2} β), Iff (Eq.{succ u1} α (Finset.inf.{u1, u2} α β _inst_1 _inst_2 S f) (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2))) (forall (s : β), (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) s S) -> (Eq.{succ u1} α (f s) (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2))))
Case conversion may be inaccurate. Consider using '#align finset.inf_eq_top_iff Finset.inf_eq_top_iffₓ'. -/
@[simp]
protected theorem inf_eq_top_iff (f : β → α) (S : Finset β) : S.inf f = ⊤ ↔ ∀ s ∈ S, f s = ⊤ :=
  @Finset.sup_eq_bot_iff αᵒᵈ _ _ _ _ _
#align finset.inf_eq_top_iff Finset.inf_eq_top_iff

end Inf

/- warning: finset.to_dual_sup -> Finset.toDual_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] (s : Finset.{u2} β) (f : β -> α), Eq.{succ u1} (OrderDual.{u1} α) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) => α -> (OrderDual.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (OrderDual.{u1} α)) (OrderDual.toDual.{u1} α) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s f)) (Finset.inf.{u1, u2} (OrderDual.{u1} α) β (OrderDual.semilatticeInf.{u1} α _inst_1) (OrderDual.orderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) _inst_2) s (Function.comp.{succ u2, succ u1, succ u1} β α (OrderDual.{u1} α) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) => α -> (OrderDual.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (OrderDual.{u1} α)) (OrderDual.toDual.{u1} α)) f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SemilatticeSup.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1)))] (s : Finset.{u1} β) (f : β -> α), Eq.{succ u2} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => OrderDual.{u2} α) (Finset.sup.{u2, u1} α β _inst_1 _inst_2 s f)) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => OrderDual.{u2} α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α) (Finset.sup.{u2, u1} α β _inst_1 _inst_2 s f)) (Finset.inf.{u2, u1} (OrderDual.{u2} α) β (OrderDual.semilatticeInf.{u2} α _inst_1) (OrderDual.orderTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1))) _inst_2) s (Function.comp.{succ u1, succ u2, succ u2} β α (OrderDual.{u2} α) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => OrderDual.{u2} α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α)) f))
Case conversion may be inaccurate. Consider using '#align finset.to_dual_sup Finset.toDual_supₓ'. -/
@[simp]
theorem toDual_sup [SemilatticeSup α] [OrderBot α] (s : Finset β) (f : β → α) :
    toDual (s.sup f) = s.inf (toDual ∘ f) :=
  rfl
#align finset.to_dual_sup Finset.toDual_sup

/- warning: finset.to_dual_inf -> Finset.toDual_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] (s : Finset.{u2} β) (f : β -> α), Eq.{succ u1} (OrderDual.{u1} α) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) => α -> (OrderDual.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (OrderDual.{u1} α)) (OrderDual.toDual.{u1} α) (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s f)) (Finset.sup.{u1, u2} (OrderDual.{u1} α) β (OrderDual.semilatticeSup.{u1} α _inst_1) (OrderDual.orderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2) s (Function.comp.{succ u2, succ u1, succ u1} β α (OrderDual.{u1} α) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) => α -> (OrderDual.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (OrderDual.{u1} α)) (OrderDual.toDual.{u1} α)) f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SemilatticeInf.{u2} α] [_inst_2 : OrderTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1)))] (s : Finset.{u1} β) (f : β -> α), Eq.{succ u2} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => OrderDual.{u2} α) (Finset.inf.{u2, u1} α β _inst_1 _inst_2 s f)) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => OrderDual.{u2} α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α) (Finset.inf.{u2, u1} α β _inst_1 _inst_2 s f)) (Finset.sup.{u2, u1} (OrderDual.{u2} α) β (OrderDual.semilatticeSup.{u2} α _inst_1) (OrderDual.orderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1))) _inst_2) s (Function.comp.{succ u1, succ u2, succ u2} β α (OrderDual.{u2} α) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => OrderDual.{u2} α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α)) f))
Case conversion may be inaccurate. Consider using '#align finset.to_dual_inf Finset.toDual_infₓ'. -/
@[simp]
theorem toDual_inf [SemilatticeInf α] [OrderTop α] (s : Finset β) (f : β → α) :
    toDual (s.inf f) = s.sup (toDual ∘ f) :=
  rfl
#align finset.to_dual_inf Finset.toDual_inf

/- warning: finset.of_dual_sup -> Finset.ofDual_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] (s : Finset.{u2} β) (f : β -> (OrderDual.{u1} α)), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) => (OrderDual.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.ofDual.{u1} α) (Finset.sup.{u1, u2} (OrderDual.{u1} α) β (OrderDual.semilatticeSup.{u1} α _inst_1) (OrderDual.orderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2) s f)) (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s (Function.comp.{succ u2, succ u1, succ u1} β (OrderDual.{u1} α) α (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) => (OrderDual.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.ofDual.{u1} α)) f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SemilatticeInf.{u2} α] [_inst_2 : OrderTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1)))] (s : Finset.{u1} β) (f : β -> (OrderDual.{u2} α)), Eq.{succ u2} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : OrderDual.{u2} α) => α) (Finset.sup.{u2, u1} (OrderDual.{u2} α) β (OrderDual.semilatticeSup.{u2} α _inst_1) (OrderDual.orderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1))) _inst_2) s f)) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.{u2} α) (fun (_x : OrderDual.{u2} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : OrderDual.{u2} α) => α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.ofDual.{u2} α) (Finset.sup.{u2, u1} (OrderDual.{u2} α) β (OrderDual.semilatticeSup.{u2} α _inst_1) (OrderDual.orderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1))) _inst_2) s f)) (Finset.inf.{u2, u1} α β _inst_1 _inst_2 s (Function.comp.{succ u1, succ u2, succ u2} β (OrderDual.{u2} α) α (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.{u2} α) (fun (_x : OrderDual.{u2} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : OrderDual.{u2} α) => α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.ofDual.{u2} α)) f))
Case conversion may be inaccurate. Consider using '#align finset.of_dual_sup Finset.ofDual_supₓ'. -/
@[simp]
theorem ofDual_sup [SemilatticeInf α] [OrderTop α] (s : Finset β) (f : β → αᵒᵈ) :
    ofDual (s.sup f) = s.inf (ofDual ∘ f) :=
  rfl
#align finset.of_dual_sup Finset.ofDual_sup

/- warning: finset.of_dual_inf -> Finset.ofDual_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] (s : Finset.{u2} β) (f : β -> (OrderDual.{u1} α)), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) => (OrderDual.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.ofDual.{u1} α) (Finset.inf.{u1, u2} (OrderDual.{u1} α) β (OrderDual.semilatticeInf.{u1} α _inst_1) (OrderDual.orderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) _inst_2) s f)) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s (Function.comp.{succ u2, succ u1, succ u1} β (OrderDual.{u1} α) α (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) => (OrderDual.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.ofDual.{u1} α)) f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SemilatticeSup.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1)))] (s : Finset.{u1} β) (f : β -> (OrderDual.{u2} α)), Eq.{succ u2} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : OrderDual.{u2} α) => α) (Finset.inf.{u2, u1} (OrderDual.{u2} α) β (OrderDual.semilatticeInf.{u2} α _inst_1) (OrderDual.orderTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1))) _inst_2) s f)) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.{u2} α) (fun (_x : OrderDual.{u2} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : OrderDual.{u2} α) => α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.ofDual.{u2} α) (Finset.inf.{u2, u1} (OrderDual.{u2} α) β (OrderDual.semilatticeInf.{u2} α _inst_1) (OrderDual.orderTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1))) _inst_2) s f)) (Finset.sup.{u2, u1} α β _inst_1 _inst_2 s (Function.comp.{succ u1, succ u2, succ u2} β (OrderDual.{u2} α) α (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.{u2} α) (fun (_x : OrderDual.{u2} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : OrderDual.{u2} α) => α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.ofDual.{u2} α)) f))
Case conversion may be inaccurate. Consider using '#align finset.of_dual_inf Finset.ofDual_infₓ'. -/
@[simp]
theorem ofDual_inf [SemilatticeSup α] [OrderBot α] (s : Finset β) (f : β → αᵒᵈ) :
    ofDual (s.inf f) = s.sup (ofDual ∘ f) :=
  rfl
#align finset.of_dual_inf Finset.ofDual_inf

section DistribLattice

variable [DistribLattice α]

section OrderBot

variable [OrderBot α] {s : Finset ι} {t : Finset κ} {f : ι → α} {g : κ → α} {a : α}

/- warning: finset.sup_inf_distrib_left -> Finset.sup_inf_distrib_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : DistribLattice.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)))))] (s : Finset.{u2} ι) (f : ι -> α) (a : α), Eq.{succ u1} α (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))) a (Finset.sup.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) _inst_2 s f)) (Finset.sup.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) _inst_2 s (fun (i : ι) => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))) a (f i)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : DistribLattice.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)))))] (s : Finset.{u2} ι) (f : ι -> α) (a : α), Eq.{succ u1} α (Inf.inf.{u1} α (Lattice.toInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) a (Finset.sup.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) _inst_2 s f)) (Finset.sup.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) _inst_2 s (fun (i : ι) => Inf.inf.{u1} α (Lattice.toInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) a (f i)))
Case conversion may be inaccurate. Consider using '#align finset.sup_inf_distrib_left Finset.sup_inf_distrib_leftₓ'. -/
theorem sup_inf_distrib_left (s : Finset ι) (f : ι → α) (a : α) :
    a ⊓ s.sup f = s.sup fun i => a ⊓ f i :=
  by
  induction' s using Finset.cons_induction with i s hi h
  · simp_rw [Finset.sup_empty, inf_bot_eq]
  · rw [sup_cons, sup_cons, inf_sup_left, h]
#align finset.sup_inf_distrib_left Finset.sup_inf_distrib_left

/- warning: finset.sup_inf_distrib_right -> Finset.sup_inf_distrib_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : DistribLattice.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)))))] (s : Finset.{u2} ι) (f : ι -> α) (a : α), Eq.{succ u1} α (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))) (Finset.sup.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) _inst_2 s f) a) (Finset.sup.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) _inst_2 s (fun (i : ι) => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))) (f i) a))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : DistribLattice.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)))))] (s : Finset.{u2} ι) (f : ι -> α) (a : α), Eq.{succ u1} α (Inf.inf.{u1} α (Lattice.toInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) (Finset.sup.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) _inst_2 s f) a) (Finset.sup.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) _inst_2 s (fun (i : ι) => Inf.inf.{u1} α (Lattice.toInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) (f i) a))
Case conversion may be inaccurate. Consider using '#align finset.sup_inf_distrib_right Finset.sup_inf_distrib_rightₓ'. -/
theorem sup_inf_distrib_right (s : Finset ι) (f : ι → α) (a : α) :
    s.sup f ⊓ a = s.sup fun i => f i ⊓ a :=
  by
  rw [_root_.inf_comm, s.sup_inf_distrib_left]
  simp_rw [_root_.inf_comm]
#align finset.sup_inf_distrib_right Finset.sup_inf_distrib_right

/- warning: finset.disjoint_sup_right -> Finset.disjoint_sup_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : DistribLattice.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)))))] {s : Finset.{u2} ι} {f : ι -> α} {a : α}, Iff (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))) _inst_2 a (Finset.sup.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) _inst_2 s f)) (forall {{i : ι}}, (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) -> (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))) _inst_2 a (f i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : DistribLattice.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α _inst_1)))))] {s : Finset.{u1} ι} {f : ι -> α} {a : α}, Iff (Disjoint.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α _inst_1))) _inst_2 a (Finset.sup.{u2, u1} α ι (Lattice.toSemilatticeSup.{u2} α (DistribLattice.toLattice.{u2} α _inst_1)) _inst_2 s f)) (forall {{i : ι}}, (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) -> (Disjoint.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α _inst_1))) _inst_2 a (f i)))
Case conversion may be inaccurate. Consider using '#align finset.disjoint_sup_right Finset.disjoint_sup_rightₓ'. -/
protected theorem disjoint_sup_right : Disjoint a (s.sup f) ↔ ∀ ⦃i⦄, i ∈ s → Disjoint a (f i) := by
  simp only [disjoint_iff, sup_inf_distrib_left, Finset.sup_eq_bot_iff]
#align finset.disjoint_sup_right Finset.disjoint_sup_right

/- warning: finset.disjoint_sup_left -> Finset.disjoint_sup_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : DistribLattice.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)))))] {s : Finset.{u2} ι} {f : ι -> α} {a : α}, Iff (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))) _inst_2 (Finset.sup.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) _inst_2 s f) a) (forall {{i : ι}}, (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) -> (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))) _inst_2 (f i) a))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : DistribLattice.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α _inst_1)))))] {s : Finset.{u1} ι} {f : ι -> α} {a : α}, Iff (Disjoint.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α _inst_1))) _inst_2 (Finset.sup.{u2, u1} α ι (Lattice.toSemilatticeSup.{u2} α (DistribLattice.toLattice.{u2} α _inst_1)) _inst_2 s f) a) (forall {{i : ι}}, (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) -> (Disjoint.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α _inst_1))) _inst_2 (f i) a))
Case conversion may be inaccurate. Consider using '#align finset.disjoint_sup_left Finset.disjoint_sup_leftₓ'. -/
protected theorem disjoint_sup_left : Disjoint (s.sup f) a ↔ ∀ ⦃i⦄, i ∈ s → Disjoint (f i) a := by
  simp only [disjoint_iff, sup_inf_distrib_right, Finset.sup_eq_bot_iff]
#align finset.disjoint_sup_left Finset.disjoint_sup_left

/- warning: finset.sup_inf_sup -> Finset.sup_inf_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {κ : Type.{u3}} [_inst_1 : DistribLattice.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)))))] (s : Finset.{u2} ι) (t : Finset.{u3} κ) (f : ι -> α) (g : κ -> α), Eq.{succ u1} α (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))) (Finset.sup.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) _inst_2 s f) (Finset.sup.{u1, u3} α κ (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) _inst_2 t g)) (Finset.sup.{u1, max u2 u3} α (Prod.{u2, u3} ι κ) (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) _inst_2 (Finset.product.{u2, u3} ι κ s t) (fun (i : Prod.{u2, u3} ι κ) => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))) (f (Prod.fst.{u2, u3} ι κ i)) (g (Prod.snd.{u2, u3} ι κ i))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u3}} {κ : Type.{u2}} [_inst_1 : DistribLattice.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)))))] (s : Finset.{u3} ι) (t : Finset.{u2} κ) (f : ι -> α) (g : κ -> α), Eq.{succ u1} α (Inf.inf.{u1} α (Lattice.toInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) (Finset.sup.{u1, u3} α ι (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) _inst_2 s f) (Finset.sup.{u1, u2} α κ (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) _inst_2 t g)) (Finset.sup.{u1, max u3 u2} α (Prod.{u3, u2} ι κ) (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) _inst_2 (Finset.product.{u3, u2} ι κ s t) (fun (i : Prod.{u3, u2} ι κ) => Inf.inf.{u1} α (Lattice.toInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) (f (Prod.fst.{u3, u2} ι κ i)) (g (Prod.snd.{u3, u2} ι κ i))))
Case conversion may be inaccurate. Consider using '#align finset.sup_inf_sup Finset.sup_inf_supₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem sup_inf_sup (s : Finset ι) (t : Finset κ) (f : ι → α) (g : κ → α) :
    s.sup f ⊓ t.sup g = (s ×ˢ t).sup fun i => f i.1 ⊓ g i.2 := by
  simp_rw [Finset.sup_inf_distrib_right, Finset.sup_inf_distrib_left, sup_product_left]
#align finset.sup_inf_sup Finset.sup_inf_sup

end OrderBot

section OrderTop

variable [OrderTop α] {f : ι → α} {g : κ → α} {s : Finset ι} {t : Finset κ} {a : α}

/- warning: finset.inf_sup_distrib_left -> Finset.inf_sup_distrib_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : DistribLattice.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)))))] (s : Finset.{u2} ι) (f : ι -> α) (a : α), Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))) a (Finset.inf.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) _inst_2 s f)) (Finset.inf.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) _inst_2 s (fun (i : ι) => Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))) a (f i)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : DistribLattice.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)))))] (s : Finset.{u2} ι) (f : ι -> α) (a : α), Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))) a (Finset.inf.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) _inst_2 s f)) (Finset.inf.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) _inst_2 s (fun (i : ι) => Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))) a (f i)))
Case conversion may be inaccurate. Consider using '#align finset.inf_sup_distrib_left Finset.inf_sup_distrib_leftₓ'. -/
theorem inf_sup_distrib_left (s : Finset ι) (f : ι → α) (a : α) :
    a ⊔ s.inf f = s.inf fun i => a ⊔ f i :=
  @sup_inf_distrib_left αᵒᵈ _ _ _ _ _ _
#align finset.inf_sup_distrib_left Finset.inf_sup_distrib_left

/- warning: finset.inf_sup_distrib_right -> Finset.inf_sup_distrib_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : DistribLattice.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)))))] (s : Finset.{u2} ι) (f : ι -> α) (a : α), Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))) (Finset.inf.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) _inst_2 s f) a) (Finset.inf.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) _inst_2 s (fun (i : ι) => Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))) (f i) a))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : DistribLattice.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)))))] (s : Finset.{u2} ι) (f : ι -> α) (a : α), Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))) (Finset.inf.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) _inst_2 s f) a) (Finset.inf.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) _inst_2 s (fun (i : ι) => Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))) (f i) a))
Case conversion may be inaccurate. Consider using '#align finset.inf_sup_distrib_right Finset.inf_sup_distrib_rightₓ'. -/
theorem inf_sup_distrib_right (s : Finset ι) (f : ι → α) (a : α) :
    s.inf f ⊔ a = s.inf fun i => f i ⊔ a :=
  @sup_inf_distrib_right αᵒᵈ _ _ _ _ _ _
#align finset.inf_sup_distrib_right Finset.inf_sup_distrib_right

/- warning: finset.codisjoint_inf_right -> Finset.codisjoint_inf_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : DistribLattice.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)))))] {f : ι -> α} {s : Finset.{u2} ι} {a : α}, Iff (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))) _inst_2 a (Finset.inf.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) _inst_2 s f)) (forall {{i : ι}}, (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) -> (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))) _inst_2 a (f i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : DistribLattice.{u2} α] [_inst_2 : OrderTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α _inst_1)))))] {f : ι -> α} {s : Finset.{u1} ι} {a : α}, Iff (Codisjoint.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α _inst_1))) _inst_2 a (Finset.inf.{u2, u1} α ι (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α _inst_1)) _inst_2 s f)) (forall {{i : ι}}, (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) -> (Codisjoint.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α _inst_1))) _inst_2 a (f i)))
Case conversion may be inaccurate. Consider using '#align finset.codisjoint_inf_right Finset.codisjoint_inf_rightₓ'. -/
protected theorem codisjoint_inf_right :
    Codisjoint a (s.inf f) ↔ ∀ ⦃i⦄, i ∈ s → Codisjoint a (f i) :=
  @Finset.disjoint_sup_right αᵒᵈ _ _ _ _ _ _
#align finset.codisjoint_inf_right Finset.codisjoint_inf_right

/- warning: finset.codisjoint_inf_left -> Finset.codisjoint_inf_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : DistribLattice.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)))))] {f : ι -> α} {s : Finset.{u2} ι} {a : α}, Iff (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))) _inst_2 (Finset.inf.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) _inst_2 s f) a) (forall {{i : ι}}, (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) -> (Codisjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))) _inst_2 (f i) a))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : DistribLattice.{u2} α] [_inst_2 : OrderTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α _inst_1)))))] {f : ι -> α} {s : Finset.{u1} ι} {a : α}, Iff (Codisjoint.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α _inst_1))) _inst_2 (Finset.inf.{u2, u1} α ι (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α _inst_1)) _inst_2 s f) a) (forall {{i : ι}}, (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) -> (Codisjoint.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α _inst_1))) _inst_2 (f i) a))
Case conversion may be inaccurate. Consider using '#align finset.codisjoint_inf_left Finset.codisjoint_inf_leftₓ'. -/
protected theorem codisjoint_inf_left :
    Codisjoint (s.inf f) a ↔ ∀ ⦃i⦄, i ∈ s → Codisjoint (f i) a :=
  @Finset.disjoint_sup_left αᵒᵈ _ _ _ _ _ _
#align finset.codisjoint_inf_left Finset.codisjoint_inf_left

/- warning: finset.inf_sup_inf -> Finset.inf_sup_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {κ : Type.{u3}} [_inst_1 : DistribLattice.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)))))] (s : Finset.{u2} ι) (t : Finset.{u3} κ) (f : ι -> α) (g : κ -> α), Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))) (Finset.inf.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) _inst_2 s f) (Finset.inf.{u1, u3} α κ (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) _inst_2 t g)) (Finset.inf.{u1, max u2 u3} α (Prod.{u2, u3} ι κ) (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) _inst_2 (Finset.product.{u2, u3} ι κ s t) (fun (i : Prod.{u2, u3} ι κ) => Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))) (f (Prod.fst.{u2, u3} ι κ i)) (g (Prod.snd.{u2, u3} ι κ i))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u3}} {κ : Type.{u2}} [_inst_1 : DistribLattice.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)))))] (s : Finset.{u3} ι) (t : Finset.{u2} κ) (f : ι -> α) (g : κ -> α), Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))) (Finset.inf.{u1, u3} α ι (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) _inst_2 s f) (Finset.inf.{u1, u2} α κ (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) _inst_2 t g)) (Finset.inf.{u1, max u3 u2} α (Prod.{u3, u2} ι κ) (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) _inst_2 (Finset.product.{u3, u2} ι κ s t) (fun (i : Prod.{u3, u2} ι κ) => Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))) (f (Prod.fst.{u3, u2} ι κ i)) (g (Prod.snd.{u3, u2} ι κ i))))
Case conversion may be inaccurate. Consider using '#align finset.inf_sup_inf Finset.inf_sup_infₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem inf_sup_inf (s : Finset ι) (t : Finset κ) (f : ι → α) (g : κ → α) :
    s.inf f ⊔ t.inf g = (s ×ˢ t).inf fun i => f i.1 ⊔ g i.2 :=
  @sup_inf_sup αᵒᵈ _ _ _ _ _ _ _ _
#align finset.inf_sup_inf Finset.inf_sup_inf

end OrderTop

section BoundedOrder

variable [BoundedOrder α] [DecidableEq ι]

/- warning: finset.inf_sup -> Finset.inf_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : DistribLattice.{u1} α] [_inst_2 : BoundedOrder.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)))))] [_inst_3 : DecidableEq.{succ u2} ι] {κ : ι -> Type.{u3}} (s : Finset.{u2} ι) (t : forall (i : ι), Finset.{u3} (κ i)) (f : forall (i : ι), (κ i) -> α), Eq.{succ u1} α (Finset.inf.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) (BoundedOrder.toOrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))))) _inst_2) s (fun (i : ι) => Finset.sup.{u1, u3} α (κ i) (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))))) _inst_2) (t i) (f i))) (Finset.sup.{u1, max u2 u3} α (forall (a : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) a s) -> (κ a)) (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))))) _inst_2) (Finset.pi.{u2, u3} ι (fun (i : ι) => κ i) (fun (a : ι) (b : ι) => _inst_3 a b) s t) (fun (g : forall (a : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) a s) -> (κ a)) => Finset.inf.{u1, u2} α (Subtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) x s)) (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) (BoundedOrder.toOrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))))) _inst_2) (Finset.attach.{u2} ι s) (fun (i : Subtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) x s)) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Subtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) x s)) ι (HasLiftT.mk.{succ u2, succ u2} (Subtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) x s)) ι (CoeTCₓ.coe.{succ u2, succ u2} (Subtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) x s)) ι (coeBase.{succ u2, succ u2} (Subtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) x s)) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) x s))))) i) (g ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Subtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) x s)) ι (HasLiftT.mk.{succ u2, succ u2} (Subtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) x s)) ι (CoeTCₓ.coe.{succ u2, succ u2} (Subtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) x s)) ι (coeBase.{succ u2, succ u2} (Subtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) x s)) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) x s))))) i) (Subtype.prop.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) x s) i)))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : DistribLattice.{u1} α] [_inst_2 : BoundedOrder.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)))))] [_inst_3 : DecidableEq.{succ u2} ι] {κ : ι -> Type.{u3}} (s : Finset.{u2} ι) (t : forall (i : ι), Finset.{u3} (κ i)) (f : forall (i : ι), (κ i) -> α), Eq.{succ u1} α (Finset.inf.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))))) _inst_2) s (fun (i : ι) => Finset.sup.{u1, u3} α (κ i) (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))))) _inst_2) (t i) (f i))) (Finset.sup.{u1, max u2 u3} α (forall (a : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) a s) -> (κ a)) (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))))) _inst_2) (Finset.pi.{u3, u2} ι (fun (i : ι) => κ i) (fun (a : ι) (b : ι) => _inst_3 a b) s t) (fun (g : forall (a : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) a s) -> (κ a)) => Finset.inf.{u1, u2} α (Subtype.{succ u2} ι (fun (x : ι) => Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) x s)) (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))))) _inst_2) (Finset.attach.{u2} ι s) (fun (i : Subtype.{succ u2} ι (fun (x : ι) => Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) x s)) => f (Subtype.val.{succ u2} ι (fun (x : ι) => Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) x s) i) (g (Subtype.val.{succ u2} ι (fun (x : ι) => Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) x s) i) (Subtype.property.{succ u2} ι (fun (x : ι) => Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) x s) i)))))
Case conversion may be inaccurate. Consider using '#align finset.inf_sup Finset.inf_supₓ'. -/
--TODO: Extract out the obvious isomorphism `(insert i s).pi t ≃ t i ×ˢ s.pi t` from this proof
theorem inf_sup {κ : ι → Type _} (s : Finset ι) (t : ∀ i, Finset (κ i)) (f : ∀ i, κ i → α) :
    (s.inf fun i => (t i).sup (f i)) =
      (s.pi t).sup fun g => s.attach.inf fun i => f _ <| g _ i.Prop :=
  by
  induction' s using Finset.induction with i s hi ih
  · simp
  rw [inf_insert, ih, attach_insert, sup_inf_sup]
  refine' eq_of_forall_ge_iff fun c => _
  simp only [Subtype.val_eq_coe, Finset.sup_le_iff, mem_product, mem_pi, and_imp, Prod.forall,
    inf_insert, inf_image]
  refine'
    ⟨fun h g hg =>
      h (g i <| mem_insert_self _ _) (fun j hj => g j <| mem_insert_of_mem hj)
        (hg _ <| mem_insert_self _ _) fun j hj => hg _ <| mem_insert_of_mem hj,
      fun h a g ha hg => _⟩
  -- TODO: This `have` must be named to prevent it being shadowed by the internal `this` in `simpa`
  have aux : ∀ j : { x // x ∈ s }, ↑j ≠ i := fun j : s => ne_of_mem_of_not_mem j.2 hi
  simpa only [cast_eq, dif_pos, Function.comp, Subtype.coe_mk, dif_neg, aux] using
    h
      (fun j hj =>
        if hji : j = i then cast (congr_arg κ hji.symm) a
        else g _ <| mem_of_mem_insert_of_ne hj hji)
      _
  simp_rw [mem_insert]
  rintro j (rfl | hj)
  · simpa
  · simpa [ne_of_mem_of_not_mem hj hi] using hg _ _
#align finset.inf_sup Finset.inf_sup

/- warning: finset.sup_inf -> Finset.sup_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : DistribLattice.{u1} α] [_inst_2 : BoundedOrder.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)))))] [_inst_3 : DecidableEq.{succ u2} ι] {κ : ι -> Type.{u3}} (s : Finset.{u2} ι) (t : forall (i : ι), Finset.{u3} (κ i)) (f : forall (i : ι), (κ i) -> α), Eq.{succ u1} α (Finset.sup.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))))) _inst_2) s (fun (i : ι) => Finset.inf.{u1, u3} α (κ i) (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) (BoundedOrder.toOrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))))) _inst_2) (t i) (f i))) (Finset.inf.{u1, max u2 u3} α (forall (a : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) a s) -> (κ a)) (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) (BoundedOrder.toOrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))))) _inst_2) (Finset.pi.{u2, u3} ι (fun (i : ι) => κ i) (fun (a : ι) (b : ι) => _inst_3 a b) s t) (fun (g : forall (a : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) a s) -> (κ a)) => Finset.sup.{u1, u2} α (Subtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) x s)) (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))))) _inst_2) (Finset.attach.{u2} ι s) (fun (i : Subtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) x s)) => f (Subtype.val.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) x s) i) (g (Subtype.val.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) x s) i) (Subtype.property.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) x s) i)))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : DistribLattice.{u1} α] [_inst_2 : BoundedOrder.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)))))] [_inst_3 : DecidableEq.{succ u2} ι] {κ : ι -> Type.{u3}} (s : Finset.{u2} ι) (t : forall (i : ι), Finset.{u3} (κ i)) (f : forall (i : ι), (κ i) -> α), Eq.{succ u1} α (Finset.sup.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))))) _inst_2) s (fun (i : ι) => Finset.inf.{u1, u3} α (κ i) (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))))) _inst_2) (t i) (f i))) (Finset.inf.{u1, max u2 u3} α (forall (a : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) a s) -> (κ a)) (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))))) _inst_2) (Finset.pi.{u3, u2} ι (fun (i : ι) => κ i) (fun (a : ι) (b : ι) => _inst_3 a b) s t) (fun (g : forall (a : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) a s) -> (κ a)) => Finset.sup.{u1, u2} α (Subtype.{succ u2} ι (fun (x : ι) => Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) x s)) (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α _inst_1))))) _inst_2) (Finset.attach.{u2} ι s) (fun (i : Subtype.{succ u2} ι (fun (x : ι) => Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) x s)) => f (Subtype.val.{succ u2} ι (fun (x : ι) => Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) x s) i) (g (Subtype.val.{succ u2} ι (fun (x : ι) => Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) x s) i) (Subtype.property.{succ u2} ι (fun (x : ι) => Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) x s) i)))))
Case conversion may be inaccurate. Consider using '#align finset.sup_inf Finset.sup_infₓ'. -/
theorem sup_inf {κ : ι → Type _} (s : Finset ι) (t : ∀ i, Finset (κ i)) (f : ∀ i, κ i → α) :
    (s.sup fun i => (t i).inf (f i)) = (s.pi t).inf fun g => s.attach.sup fun i => f _ <| g _ i.2 :=
  @inf_sup αᵒᵈ _ _ _ _ _ _ _ _
#align finset.sup_inf Finset.sup_inf

end BoundedOrder

end DistribLattice

section BooleanAlgebra

variable [BooleanAlgebra α] {s : Finset ι}

/- warning: finset.sup_sdiff_left -> Finset.sup_sdiff_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : BooleanAlgebra.{u1} α] (s : Finset.{u2} ι) (f : ι -> α) (a : α), Eq.{succ u1} α (Finset.sup.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1)) s (fun (b : ι) => SDiff.sdiff.{u1} α (BooleanAlgebra.toHasSdiff.{u1} α _inst_1) a (f b))) (SDiff.sdiff.{u1} α (BooleanAlgebra.toHasSdiff.{u1} α _inst_1) a (Finset.inf.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1)))) (GeneralizedHeytingAlgebra.toOrderTop.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α (BiheytingAlgebra.toHeytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))) s f))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : BooleanAlgebra.{u1} α] (s : Finset.{u2} ι) (f : ι -> α) (a : α), Eq.{succ u1} α (Finset.sup.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))))) (BooleanAlgebra.toBoundedOrder.{u1} α _inst_1)) s (fun (b : ι) => SDiff.sdiff.{u1} α (BooleanAlgebra.toSDiff.{u1} α _inst_1) a (f b))) (SDiff.sdiff.{u1} α (BooleanAlgebra.toSDiff.{u1} α _inst_1) a (Finset.inf.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))))) (BooleanAlgebra.toBoundedOrder.{u1} α _inst_1)) s f))
Case conversion may be inaccurate. Consider using '#align finset.sup_sdiff_left Finset.sup_sdiff_leftₓ'. -/
theorem sup_sdiff_left (s : Finset ι) (f : ι → α) (a : α) :
    (s.sup fun b => a \ f b) = a \ s.inf f :=
  by
  refine' Finset.cons_induction_on s _ fun b t _ h => _
  · rw [sup_empty, inf_empty, sdiff_top]
  · rw [sup_cons, inf_cons, h, sdiff_inf]
#align finset.sup_sdiff_left Finset.sup_sdiff_left

/- warning: finset.inf_sdiff_left -> Finset.inf_sdiff_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : BooleanAlgebra.{u1} α] {s : Finset.{u2} ι}, (Finset.Nonempty.{u2} ι s) -> (forall (f : ι -> α) (a : α), Eq.{succ u1} α (Finset.inf.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1)))) (GeneralizedHeytingAlgebra.toOrderTop.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α (BiheytingAlgebra.toHeytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))) s (fun (b : ι) => SDiff.sdiff.{u1} α (BooleanAlgebra.toHasSdiff.{u1} α _inst_1) a (f b))) (SDiff.sdiff.{u1} α (BooleanAlgebra.toHasSdiff.{u1} α _inst_1) a (Finset.sup.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1)) s f)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : BooleanAlgebra.{u1} α] {s : Finset.{u2} ι}, (Finset.Nonempty.{u2} ι s) -> (forall (f : ι -> α) (a : α), Eq.{succ u1} α (Finset.inf.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))))) (BooleanAlgebra.toBoundedOrder.{u1} α _inst_1)) s (fun (b : ι) => SDiff.sdiff.{u1} α (BooleanAlgebra.toSDiff.{u1} α _inst_1) a (f b))) (SDiff.sdiff.{u1} α (BooleanAlgebra.toSDiff.{u1} α _inst_1) a (Finset.sup.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))))) (BooleanAlgebra.toBoundedOrder.{u1} α _inst_1)) s f)))
Case conversion may be inaccurate. Consider using '#align finset.inf_sdiff_left Finset.inf_sdiff_leftₓ'. -/
theorem inf_sdiff_left (hs : s.Nonempty) (f : ι → α) (a : α) :
    (s.inf fun b => a \ f b) = a \ s.sup f :=
  by
  induction' hs using Finset.Nonempty.cons_induction with b b t _ _ h
  · rw [sup_singleton, inf_singleton]
  · rw [sup_cons, inf_cons, h, sdiff_sup]
#align finset.inf_sdiff_left Finset.inf_sdiff_left

/- warning: finset.inf_sdiff_right -> Finset.inf_sdiff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : BooleanAlgebra.{u1} α] {s : Finset.{u2} ι}, (Finset.Nonempty.{u2} ι s) -> (forall (f : ι -> α) (a : α), Eq.{succ u1} α (Finset.inf.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1)))) (GeneralizedHeytingAlgebra.toOrderTop.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α (BiheytingAlgebra.toHeytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))) s (fun (b : ι) => SDiff.sdiff.{u1} α (BooleanAlgebra.toHasSdiff.{u1} α _inst_1) (f b) a)) (SDiff.sdiff.{u1} α (BooleanAlgebra.toHasSdiff.{u1} α _inst_1) (Finset.inf.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1)))) (GeneralizedHeytingAlgebra.toOrderTop.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α (BiheytingAlgebra.toHeytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))) s f) a))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : BooleanAlgebra.{u1} α] {s : Finset.{u2} ι}, (Finset.Nonempty.{u2} ι s) -> (forall (f : ι -> α) (a : α), Eq.{succ u1} α (Finset.inf.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))))) (BooleanAlgebra.toBoundedOrder.{u1} α _inst_1)) s (fun (b : ι) => SDiff.sdiff.{u1} α (BooleanAlgebra.toSDiff.{u1} α _inst_1) (f b) a)) (SDiff.sdiff.{u1} α (BooleanAlgebra.toSDiff.{u1} α _inst_1) (Finset.inf.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))))) (BooleanAlgebra.toBoundedOrder.{u1} α _inst_1)) s f) a))
Case conversion may be inaccurate. Consider using '#align finset.inf_sdiff_right Finset.inf_sdiff_rightₓ'. -/
theorem inf_sdiff_right (hs : s.Nonempty) (f : ι → α) (a : α) :
    (s.inf fun b => f b \ a) = s.inf f \ a :=
  by
  induction' hs using Finset.Nonempty.cons_induction with b b t _ _ h
  · rw [inf_singleton, inf_singleton]
  · rw [inf_cons, inf_cons, h, inf_sdiff]
#align finset.inf_sdiff_right Finset.inf_sdiff_right

/- warning: finset.inf_himp_right -> Finset.inf_himp_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : BooleanAlgebra.{u1} α] (s : Finset.{u2} ι) (f : ι -> α) (a : α), Eq.{succ u1} α (Finset.inf.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1)))) (GeneralizedHeytingAlgebra.toOrderTop.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α (BiheytingAlgebra.toHeytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))) s (fun (b : ι) => HImp.himp.{u1} α (BooleanAlgebra.toHasHimp.{u1} α _inst_1) (f b) a)) (HImp.himp.{u1} α (BooleanAlgebra.toHasHimp.{u1} α _inst_1) (Finset.sup.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1)) s f) a)
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : BooleanAlgebra.{u1} α] (s : Finset.{u2} ι) (f : ι -> α) (a : α), Eq.{succ u1} α (Finset.inf.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))))) (BooleanAlgebra.toBoundedOrder.{u1} α _inst_1)) s (fun (b : ι) => HImp.himp.{u1} α (BooleanAlgebra.toHImp.{u1} α _inst_1) (f b) a)) (HImp.himp.{u1} α (BooleanAlgebra.toHImp.{u1} α _inst_1) (Finset.sup.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))))) (BooleanAlgebra.toBoundedOrder.{u1} α _inst_1)) s f) a)
Case conversion may be inaccurate. Consider using '#align finset.inf_himp_right Finset.inf_himp_rightₓ'. -/
theorem inf_himp_right (s : Finset ι) (f : ι → α) (a : α) :
    (s.inf fun b => f b ⇨ a) = s.sup f ⇨ a :=
  @sup_sdiff_left αᵒᵈ _ _ _ _ _
#align finset.inf_himp_right Finset.inf_himp_right

/- warning: finset.sup_himp_right -> Finset.sup_himp_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : BooleanAlgebra.{u1} α] {s : Finset.{u2} ι}, (Finset.Nonempty.{u2} ι s) -> (forall (f : ι -> α) (a : α), Eq.{succ u1} α (Finset.sup.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1)) s (fun (b : ι) => HImp.himp.{u1} α (BooleanAlgebra.toHasHimp.{u1} α _inst_1) (f b) a)) (HImp.himp.{u1} α (BooleanAlgebra.toHasHimp.{u1} α _inst_1) (Finset.inf.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1)))) (GeneralizedHeytingAlgebra.toOrderTop.{u1} α (HeytingAlgebra.toGeneralizedHeytingAlgebra.{u1} α (BiheytingAlgebra.toHeytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))) s f) a))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : BooleanAlgebra.{u1} α] {s : Finset.{u2} ι}, (Finset.Nonempty.{u2} ι s) -> (forall (f : ι -> α) (a : α), Eq.{succ u1} α (Finset.sup.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))))) (BooleanAlgebra.toBoundedOrder.{u1} α _inst_1)) s (fun (b : ι) => HImp.himp.{u1} α (BooleanAlgebra.toHImp.{u1} α _inst_1) (f b) a)) (HImp.himp.{u1} α (BooleanAlgebra.toHImp.{u1} α _inst_1) (Finset.inf.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))))) (BooleanAlgebra.toBoundedOrder.{u1} α _inst_1)) s f) a))
Case conversion may be inaccurate. Consider using '#align finset.sup_himp_right Finset.sup_himp_rightₓ'. -/
theorem sup_himp_right (hs : s.Nonempty) (f : ι → α) (a : α) :
    (s.sup fun b => f b ⇨ a) = s.inf f ⇨ a :=
  @inf_sdiff_left αᵒᵈ _ _ _ hs _ _
#align finset.sup_himp_right Finset.sup_himp_right

/- warning: finset.sup_himp_left -> Finset.sup_himp_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : BooleanAlgebra.{u1} α] {s : Finset.{u2} ι}, (Finset.Nonempty.{u2} ι s) -> (forall (f : ι -> α) (a : α), Eq.{succ u1} α (Finset.sup.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1)) s (fun (b : ι) => HImp.himp.{u1} α (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a (f b))) (HImp.himp.{u1} α (BooleanAlgebra.toHasHimp.{u1} α _inst_1) a (Finset.sup.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} α _inst_1)) s f)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : BooleanAlgebra.{u1} α] {s : Finset.{u2} ι}, (Finset.Nonempty.{u2} ι s) -> (forall (f : ι -> α) (a : α), Eq.{succ u1} α (Finset.sup.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))))) (BooleanAlgebra.toBoundedOrder.{u1} α _inst_1)) s (fun (b : ι) => HImp.himp.{u1} α (BooleanAlgebra.toHImp.{u1} α _inst_1) a (f b))) (HImp.himp.{u1} α (BooleanAlgebra.toHImp.{u1} α _inst_1) a (Finset.sup.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1))))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} α (BiheytingAlgebra.toCoheytingAlgebra.{u1} α (BooleanAlgebra.toBiheytingAlgebra.{u1} α _inst_1)))))))) (BooleanAlgebra.toBoundedOrder.{u1} α _inst_1)) s f)))
Case conversion may be inaccurate. Consider using '#align finset.sup_himp_left Finset.sup_himp_leftₓ'. -/
theorem sup_himp_left (hs : s.Nonempty) (f : ι → α) (a : α) :
    (s.sup fun b => a ⇨ f b) = a ⇨ s.sup f :=
  @inf_sdiff_right αᵒᵈ _ _ _ hs _ _
#align finset.sup_himp_left Finset.sup_himp_left

#print Finset.compl_sup /-
@[simp]
protected theorem compl_sup (s : Finset ι) (f : ι → α) : s.sup fᶜ = s.inf fun i => f iᶜ :=
  map_finset_sup (OrderIso.compl α) _ _
#align finset.compl_sup Finset.compl_sup
-/

#print Finset.compl_inf /-
@[simp]
protected theorem compl_inf (s : Finset ι) (f : ι → α) : s.inf fᶜ = s.sup fun i => f iᶜ :=
  map_finset_inf (OrderIso.compl α) _ _
#align finset.compl_inf Finset.compl_inf
-/

end BooleanAlgebra

section LinearOrder

variable [LinearOrder α]

section OrderBot

variable [OrderBot α] {s : Finset ι} {f : ι → α} {a : α}

/- warning: finset.comp_sup_eq_sup_comp_of_is_total -> Finset.comp_sup_eq_sup_comp_of_is_total is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Type.{u3}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))] {s : Finset.{u3} ι} {f : ι -> α} [_inst_3 : SemilatticeSup.{u2} β] [_inst_4 : OrderBot.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3)))] (g : α -> β), (Monotone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3)) g) -> (Eq.{succ u2} β (g (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) _inst_2))) (Bot.bot.{u2} β (OrderBot.toHasBot.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) _inst_4))) -> (Eq.{succ u2} β (g (Finset.sup.{u1, u3} α ι (Lattice.toSemilatticeSup.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)) _inst_2 s f)) (Finset.sup.{u2, u3} β ι _inst_3 _inst_4 s (Function.comp.{succ u3, succ u1, succ u2} ι α β g f)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))))] {s : Finset.{u1} ι} {f : ι -> α} [_inst_3 : SemilatticeSup.{u3} β] [_inst_4 : OrderBot.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (SemilatticeSup.toPartialOrder.{u3} β _inst_3)))] (g : α -> β), (Monotone.{u2, u3} α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) (PartialOrder.toPreorder.{u3} β (SemilatticeSup.toPartialOrder.{u3} β _inst_3)) g) -> (Eq.{succ u3} β (g (Bot.bot.{u2} α (OrderBot.toBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) _inst_2))) (Bot.bot.{u3} β (OrderBot.toBot.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (SemilatticeSup.toPartialOrder.{u3} β _inst_3))) _inst_4))) -> (Eq.{succ u3} β (g (Finset.sup.{u2, u1} α ι (Lattice.toSemilatticeSup.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))) _inst_2 s f)) (Finset.sup.{u3, u1} β ι _inst_3 _inst_4 s (Function.comp.{succ u1, succ u2, succ u3} ι α β g f)))
Case conversion may be inaccurate. Consider using '#align finset.comp_sup_eq_sup_comp_of_is_total Finset.comp_sup_eq_sup_comp_of_is_totalₓ'. -/
theorem comp_sup_eq_sup_comp_of_is_total [SemilatticeSup β] [OrderBot β] (g : α → β)
    (mono_g : Monotone g) (bot : g ⊥ = ⊥) : g (s.sup f) = s.sup (g ∘ f) :=
  comp_sup_eq_sup_comp g mono_g.map_sup bot
#align finset.comp_sup_eq_sup_comp_of_is_total Finset.comp_sup_eq_sup_comp_of_is_total

/- warning: finset.le_sup_iff -> Finset.le_sup_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))] {s : Finset.{u2} ι} {f : ι -> α} {a : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) _inst_2)) a) -> (Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a (Finset.sup.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)) _inst_2 s f)) (Exists.{succ u2} ι (fun (b : ι) => Exists.{0} (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) b s) (fun (H : Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) b s) => LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a (f b)))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))))] {s : Finset.{u1} ι} {f : ι -> α} {a : α}, (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) (Bot.bot.{u2} α (OrderBot.toBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) _inst_2)) a) -> (Iff (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) a (Finset.sup.{u2, u1} α ι (Lattice.toSemilatticeSup.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))) _inst_2 s f)) (Exists.{succ u1} ι (fun (b : ι) => And (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) b s) (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) a (f b)))))
Case conversion may be inaccurate. Consider using '#align finset.le_sup_iff Finset.le_sup_iffₓ'. -/
@[simp]
protected theorem le_sup_iff (ha : ⊥ < a) : a ≤ s.sup f ↔ ∃ b ∈ s, a ≤ f b :=
  ⟨Finset.cons_induction_on s (fun h => absurd h (not_le_of_lt ha)) fun c t hc ih => by
      simpa using
        @Or.ndrec _ _ (∃ b, (b = c ∨ b ∈ t) ∧ a ≤ f b) (fun h => ⟨c, Or.inl rfl, h⟩) fun h =>
          let ⟨b, hb, hle⟩ := ih h
          ⟨b, Or.inr hb, hle⟩,
    fun ⟨b, hb, hle⟩ => trans hle (le_sup hb)⟩
#align finset.le_sup_iff Finset.le_sup_iff

/- warning: finset.lt_sup_iff -> Finset.lt_sup_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))] {s : Finset.{u2} ι} {f : ι -> α} {a : α}, Iff (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a (Finset.sup.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)) _inst_2 s f)) (Exists.{succ u2} ι (fun (b : ι) => Exists.{0} (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) b s) (fun (H : Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) b s) => LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a (f b))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))))] {s : Finset.{u1} ι} {f : ι -> α} {a : α}, Iff (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) a (Finset.sup.{u2, u1} α ι (Lattice.toSemilatticeSup.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))) _inst_2 s f)) (Exists.{succ u1} ι (fun (b : ι) => And (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) b s) (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) a (f b))))
Case conversion may be inaccurate. Consider using '#align finset.lt_sup_iff Finset.lt_sup_iffₓ'. -/
@[simp]
protected theorem lt_sup_iff : a < s.sup f ↔ ∃ b ∈ s, a < f b :=
  ⟨Finset.cons_induction_on s (fun h => absurd h not_lt_bot) fun c t hc ih => by
      simpa using
        @Or.ndrec _ _ (∃ b, (b = c ∨ b ∈ t) ∧ a < f b) (fun h => ⟨c, Or.inl rfl, h⟩) fun h =>
          let ⟨b, hb, hlt⟩ := ih h
          ⟨b, Or.inr hb, hlt⟩,
    fun ⟨b, hb, hlt⟩ => lt_of_lt_of_le hlt (le_sup hb)⟩
#align finset.lt_sup_iff Finset.lt_sup_iff

/- warning: finset.sup_lt_iff -> Finset.sup_lt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))] {s : Finset.{u2} ι} {f : ι -> α} {a : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) _inst_2)) a) -> (Iff (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (Finset.sup.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)) _inst_2 s f) a) (forall (b : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) b s) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (f b) a)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))))] {s : Finset.{u1} ι} {f : ι -> α} {a : α}, (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) (Bot.bot.{u2} α (OrderBot.toBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) _inst_2)) a) -> (Iff (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) (Finset.sup.{u2, u1} α ι (Lattice.toSemilatticeSup.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))) _inst_2 s f) a) (forall (b : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) b s) -> (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) (f b) a)))
Case conversion may be inaccurate. Consider using '#align finset.sup_lt_iff Finset.sup_lt_iffₓ'. -/
@[simp]
protected theorem sup_lt_iff (ha : ⊥ < a) : s.sup f < a ↔ ∀ b ∈ s, f b < a :=
  ⟨fun hs b hb => lt_of_le_of_lt (le_sup hb) hs,
    Finset.cons_induction_on s (fun _ => ha) fun c t hc => by
      simpa only [sup_cons, sup_lt_iff, mem_cons, forall_eq_or_imp] using And.imp_right⟩
#align finset.sup_lt_iff Finset.sup_lt_iff

end OrderBot

section OrderTop

variable [OrderTop α] {s : Finset ι} {f : ι → α} {a : α}

/- warning: finset.comp_inf_eq_inf_comp_of_is_total -> Finset.comp_inf_eq_inf_comp_of_is_total is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Type.{u3}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))] {s : Finset.{u3} ι} {f : ι -> α} [_inst_3 : SemilatticeInf.{u2} β] [_inst_4 : OrderTop.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β _inst_3)))] (g : α -> β), (Monotone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β _inst_3)) g) -> (Eq.{succ u2} β (g (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) _inst_2))) (Top.top.{u2} β (OrderTop.toHasTop.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β _inst_3))) _inst_4))) -> (Eq.{succ u2} β (g (Finset.inf.{u1, u3} α ι (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)) _inst_2 s f)) (Finset.inf.{u2, u3} β ι _inst_3 _inst_4 s (Function.comp.{succ u3, succ u1, succ u2} ι α β g f)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] [_inst_2 : OrderTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))))] {s : Finset.{u1} ι} {f : ι -> α} [_inst_3 : SemilatticeInf.{u3} β] [_inst_4 : OrderTop.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β _inst_3)))] (g : α -> β), (Monotone.{u2, u3} α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β _inst_3)) g) -> (Eq.{succ u3} β (g (Top.top.{u2} α (OrderTop.toTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) _inst_2))) (Top.top.{u3} β (OrderTop.toTop.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β _inst_3))) _inst_4))) -> (Eq.{succ u3} β (g (Finset.inf.{u2, u1} α ι (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))) _inst_2 s f)) (Finset.inf.{u3, u1} β ι _inst_3 _inst_4 s (Function.comp.{succ u1, succ u2, succ u3} ι α β g f)))
Case conversion may be inaccurate. Consider using '#align finset.comp_inf_eq_inf_comp_of_is_total Finset.comp_inf_eq_inf_comp_of_is_totalₓ'. -/
theorem comp_inf_eq_inf_comp_of_is_total [SemilatticeInf β] [OrderTop β] (g : α → β)
    (mono_g : Monotone g) (top : g ⊤ = ⊤) : g (s.inf f) = s.inf (g ∘ f) :=
  comp_inf_eq_inf_comp g mono_g.map_inf top
#align finset.comp_inf_eq_inf_comp_of_is_total Finset.comp_inf_eq_inf_comp_of_is_total

/- warning: finset.inf_le_iff -> Finset.inf_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))] {s : Finset.{u2} ι} {f : ι -> α} {a : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) _inst_2))) -> (Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (Finset.inf.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)) _inst_2 s f) a) (Exists.{succ u2} ι (fun (b : ι) => Exists.{0} (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) b s) (fun (H : Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) b s) => LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (f b) a))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] [_inst_2 : OrderTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))))] {s : Finset.{u1} ι} {f : ι -> α} {a : α}, (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) a (Top.top.{u2} α (OrderTop.toTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) _inst_2))) -> (Iff (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) (Finset.inf.{u2, u1} α ι (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))) _inst_2 s f) a) (Exists.{succ u1} ι (fun (b : ι) => And (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) b s) (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) (f b) a))))
Case conversion may be inaccurate. Consider using '#align finset.inf_le_iff Finset.inf_le_iffₓ'. -/
@[simp]
protected theorem inf_le_iff (ha : a < ⊤) : s.inf f ≤ a ↔ ∃ b ∈ s, f b ≤ a :=
  @Finset.le_sup_iff αᵒᵈ _ _ _ _ _ _ ha
#align finset.inf_le_iff Finset.inf_le_iff

/- warning: finset.inf_lt_iff -> Finset.inf_lt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))] {s : Finset.{u2} ι} {f : ι -> α} {a : α}, Iff (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (Finset.inf.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)) _inst_2 s f) a) (Exists.{succ u2} ι (fun (b : ι) => Exists.{0} (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) b s) (fun (H : Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) b s) => LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (f b) a)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] [_inst_2 : OrderTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))))] {s : Finset.{u1} ι} {f : ι -> α} {a : α}, Iff (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) (Finset.inf.{u2, u1} α ι (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))) _inst_2 s f) a) (Exists.{succ u1} ι (fun (b : ι) => And (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) b s) (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) (f b) a)))
Case conversion may be inaccurate. Consider using '#align finset.inf_lt_iff Finset.inf_lt_iffₓ'. -/
@[simp]
protected theorem inf_lt_iff : s.inf f < a ↔ ∃ b ∈ s, f b < a :=
  @Finset.lt_sup_iff αᵒᵈ _ _ _ _ _ _
#align finset.inf_lt_iff Finset.inf_lt_iff

/- warning: finset.lt_inf_iff -> Finset.lt_inf_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))] {s : Finset.{u2} ι} {f : ι -> α} {a : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) _inst_2))) -> (Iff (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a (Finset.inf.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)) _inst_2 s f)) (forall (b : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) b s) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a (f b))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] [_inst_2 : OrderTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))))] {s : Finset.{u1} ι} {f : ι -> α} {a : α}, (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) a (Top.top.{u2} α (OrderTop.toTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) _inst_2))) -> (Iff (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) a (Finset.inf.{u2, u1} α ι (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))) _inst_2 s f)) (forall (b : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) b s) -> (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) a (f b))))
Case conversion may be inaccurate. Consider using '#align finset.lt_inf_iff Finset.lt_inf_iffₓ'. -/
@[simp]
protected theorem lt_inf_iff (ha : a < ⊤) : a < s.inf f ↔ ∀ b ∈ s, a < f b :=
  @Finset.sup_lt_iff αᵒᵈ _ _ _ _ _ _ ha
#align finset.lt_inf_iff Finset.lt_inf_iff

end OrderTop

end LinearOrder

/- warning: finset.inf_eq_infi -> Finset.inf_eq_iInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u2} β] (s : Finset.{u1} α) (f : α -> β), Eq.{succ u2} β (Finset.inf.{u2, u1} β α (Lattice.toSemilatticeInf.{u2} β (CompleteLattice.toLattice.{u2} β _inst_1)) (BoundedOrder.toOrderTop.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (CompleteLattice.toLattice.{u2} β _inst_1))))) (CompleteLattice.toBoundedOrder.{u2} β _inst_1)) s f) (iInf.{u2, succ u1} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) α (fun (a : α) => iInf.{u2, 0} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => f a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u2} β] (s : Finset.{u1} α) (f : α -> β), Eq.{succ u2} β (Finset.inf.{u2, u1} β α (Lattice.toSemilatticeInf.{u2} β (CompleteLattice.toLattice.{u2} β _inst_1)) (BoundedOrder.toOrderTop.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (CompleteLattice.toLattice.{u2} β _inst_1))))) (CompleteLattice.toBoundedOrder.{u2} β _inst_1)) s f) (iInf.{u2, succ u1} β (CompleteLattice.toInfSet.{u2} β _inst_1) α (fun (a : α) => iInf.{u2, 0} β (CompleteLattice.toInfSet.{u2} β _inst_1) (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) => f a)))
Case conversion may be inaccurate. Consider using '#align finset.inf_eq_infi Finset.inf_eq_iInfₓ'. -/
theorem inf_eq_iInf [CompleteLattice β] (s : Finset α) (f : α → β) : s.inf f = ⨅ a ∈ s, f a :=
  @sup_eq_iSup _ βᵒᵈ _ _ _
#align finset.inf_eq_infi Finset.inf_eq_iInf

/- warning: finset.inf_id_eq_Inf -> Finset.inf_id_eq_sInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (s : Finset.{u1} α), Eq.{succ u1} α (Finset.inf.{u1, u1} α α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) (BoundedOrder.toOrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) s (id.{succ u1} α)) (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (s : Finset.{u1} α), Eq.{succ u1} α (Finset.inf.{u1, u1} α α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) s (id.{succ u1} α)) (InfSet.sInf.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Finset.toSet.{u1} α s))
Case conversion may be inaccurate. Consider using '#align finset.inf_id_eq_Inf Finset.inf_id_eq_sInfₓ'. -/
theorem inf_id_eq_sInf [CompleteLattice α] (s : Finset α) : s.inf id = sInf s :=
  @sup_id_eq_sSup αᵒᵈ _ _
#align finset.inf_id_eq_Inf Finset.inf_id_eq_sInf

/- warning: finset.inf_id_set_eq_sInter -> Finset.inf_id_set_eq_sInter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Finset.{u1} (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Finset.inf.{u1, u1} (Set.{u1} α) (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (CompleteLattice.toLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (Set.orderTop.{u1} α) s (id.{succ u1} (Set.{u1} α))) (Set.sInter.{u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} (Set.{u1} α)) (Set.{u1} (Set.{u1} α)) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} (Set.{u1} α)) (Set.{u1} (Set.{u1} α)) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} (Set.{u1} α)) (Set.{u1} (Set.{u1} α)) (Finset.Set.hasCoeT.{u1} (Set.{u1} α)))) s))
but is expected to have type
  forall {α : Type.{u1}} (s : Finset.{u1} (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Finset.inf.{u1, u1} (Set.{u1} α) (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (CompleteLattice.toLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (Set.instOrderTopSetInstLESet.{u1} α) s (id.{succ u1} (Set.{u1} α))) (Set.sInter.{u1} α (Finset.toSet.{u1} (Set.{u1} α) s))
Case conversion may be inaccurate. Consider using '#align finset.inf_id_set_eq_sInter Finset.inf_id_set_eq_sInterₓ'. -/
theorem inf_id_set_eq_sInter (s : Finset (Set α)) : s.inf id = ⋂₀ ↑s :=
  inf_id_eq_sInf _
#align finset.inf_id_set_eq_sInter Finset.inf_id_set_eq_sInter

/- warning: finset.inf_set_eq_bInter -> Finset.inf_set_eq_iInter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Finset.{u1} α) (f : α -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Finset.inf.{u2, u1} (Set.{u2} β) α (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (CompleteLattice.toLattice.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β)))))) (Set.orderTop.{u2} β) s f) (Set.iInter.{u2, succ u1} β α (fun (x : α) => Set.iInter.{u2, 0} β (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) => f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Finset.{u2} α) (f : α -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Finset.inf.{u1, u2} (Set.{u1} β) α (Lattice.toSemilatticeInf.{u1} (Set.{u1} β) (CompleteLattice.toLattice.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β)))))) (Set.instOrderTopSetInstLESet.{u1} β) s f) (Set.iInter.{u1, succ u2} β α (fun (x : α) => Set.iInter.{u1, 0} β (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) => f x)))
Case conversion may be inaccurate. Consider using '#align finset.inf_set_eq_bInter Finset.inf_set_eq_iInterₓ'. -/
@[simp]
theorem inf_set_eq_iInter (s : Finset α) (f : α → Set β) : s.inf f = ⋂ x ∈ s, f x :=
  inf_eq_iInf _ _
#align finset.inf_set_eq_bInter Finset.inf_set_eq_iInter

/- warning: finset.inf_eq_Inf_image -> Finset.inf_eq_sInf_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u2} β] (s : Finset.{u1} α) (f : α -> β), Eq.{succ u2} β (Finset.inf.{u2, u1} β α (Lattice.toSemilatticeInf.{u2} β (CompleteLattice.toLattice.{u2} β _inst_1)) (BoundedOrder.toOrderTop.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (CompleteLattice.toLattice.{u2} β _inst_1))))) (CompleteLattice.toBoundedOrder.{u2} β _inst_1)) s f) (InfSet.sInf.{u2} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) (Set.image.{u1, u2} α β f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u2} β] (s : Finset.{u1} α) (f : α -> β), Eq.{succ u2} β (Finset.inf.{u2, u1} β α (Lattice.toSemilatticeInf.{u2} β (CompleteLattice.toLattice.{u2} β _inst_1)) (BoundedOrder.toOrderTop.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (CompleteLattice.toLattice.{u2} β _inst_1))))) (CompleteLattice.toBoundedOrder.{u2} β _inst_1)) s f) (InfSet.sInf.{u2} β (CompleteLattice.toInfSet.{u2} β _inst_1) (Set.image.{u1, u2} α β f (Finset.toSet.{u1} α s)))
Case conversion may be inaccurate. Consider using '#align finset.inf_eq_Inf_image Finset.inf_eq_sInf_imageₓ'. -/
theorem inf_eq_sInf_image [CompleteLattice β] (s : Finset α) (f : α → β) :
    s.inf f = sInf (f '' s) :=
  @sup_eq_sSup_image _ βᵒᵈ _ _ _
#align finset.inf_eq_Inf_image Finset.inf_eq_sInf_image

section Sup'

variable [SemilatticeSup α]

#print Finset.sup_of_mem /-
theorem sup_of_mem {s : Finset β} (f : β → α) {b : β} (h : b ∈ s) :
    ∃ a : α, s.sup (coe ∘ f : β → WithBot α) = ↑a :=
  Exists.imp (fun a => Exists.fst) (@le_sup (WithBot α) _ _ _ _ _ _ h (f b) rfl)
#align finset.sup_of_mem Finset.sup_of_mem
-/

#print Finset.sup' /-
/-- Given nonempty finset `s` then `s.sup' H f` is the supremum of its image under `f` in (possibly
unbounded) join-semilattice `α`, where `H` is a proof of nonemptiness. If `α` has a bottom element
you may instead use `finset.sup` which does not require `s` nonempty. -/
def sup' (s : Finset β) (H : s.Nonempty) (f : β → α) : α :=
  WithBot.unbot (s.sup (coe ∘ f)) (by simpa using H)
#align finset.sup' Finset.sup'
-/

variable {s : Finset β} (H : s.Nonempty) (f : β → α)

/- warning: finset.coe_sup' -> Finset.coe_sup' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] {s : Finset.{u2} β} (H : Finset.Nonempty.{u2} β s) (f : β -> α), Eq.{succ u1} (WithBot.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) (Finset.sup'.{u1, u2} α β _inst_1 s H f)) (Finset.sup.{u1, u2} (WithBot.{u1} α) β (WithBot.semilatticeSup.{u1} α _inst_1) (WithBot.orderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) s (Function.comp.{succ u2, succ u1, succ u1} β α (WithBot.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α)))) f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SemilatticeSup.{u2} α] {s : Finset.{u1} β} (H : Finset.Nonempty.{u1} β s) (f : β -> α), Eq.{succ u2} (WithBot.{u2} α) (WithBot.some.{u2} α (Finset.sup'.{u2, u1} α β _inst_1 s H f)) (Finset.sup.{u2, u1} (WithBot.{u2} α) β (WithBot.semilatticeSup.{u2} α _inst_1) (WithBot.orderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1)))) s (Function.comp.{succ u1, succ u2, succ u2} β α (WithBot.{u2} α) (WithBot.some.{u2} α) f))
Case conversion may be inaccurate. Consider using '#align finset.coe_sup' Finset.coe_sup'ₓ'. -/
@[simp]
theorem coe_sup' : ((s.sup' H f : α) : WithBot α) = s.sup (coe ∘ f) := by
  rw [sup', WithBot.coe_unbot]
#align finset.coe_sup' Finset.coe_sup'

/- warning: finset.sup'_cons -> Finset.sup'_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] {s : Finset.{u2} β} (H : Finset.Nonempty.{u2} β s) (f : β -> α) {b : β} {hb : Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s)} {h : Finset.Nonempty.{u2} β (Finset.cons.{u2} β b s hb)}, Eq.{succ u1} α (Finset.sup'.{u1, u2} α β _inst_1 (Finset.cons.{u2} β b s hb) h f) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1) (f b) (Finset.sup'.{u1, u2} α β _inst_1 s H f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] {s : Finset.{u2} β} (H : Finset.Nonempty.{u2} β s) (f : β -> α) {b : β} {hb : Not (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b s)} {h : Finset.Nonempty.{u2} β (Finset.cons.{u2} β b s hb)}, Eq.{succ u1} α (Finset.sup'.{u1, u2} α β _inst_1 (Finset.cons.{u2} β b s hb) h f) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_1) (f b) (Finset.sup'.{u1, u2} α β _inst_1 s H f))
Case conversion may be inaccurate. Consider using '#align finset.sup'_cons Finset.sup'_consₓ'. -/
@[simp]
theorem sup'_cons {b : β} {hb : b ∉ s} {h : (cons b s hb).Nonempty} :
    (cons b s hb).sup' h f = f b ⊔ s.sup' H f :=
  by
  rw [← WithBot.coe_eq_coe]
  simp only [coe_sup', sup_cons, WithBot.coe_sup]
#align finset.sup'_cons Finset.sup'_cons

/- warning: finset.sup'_insert -> Finset.sup'_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] {s : Finset.{u2} β} (H : Finset.Nonempty.{u2} β s) (f : β -> α) [_inst_2 : DecidableEq.{succ u2} β] {b : β} {h : Finset.Nonempty.{u2} β (Insert.insert.{u2, u2} β (Finset.{u2} β) (Finset.hasInsert.{u2} β (fun (a : β) (b : β) => _inst_2 a b)) b s)}, Eq.{succ u1} α (Finset.sup'.{u1, u2} α β _inst_1 (Insert.insert.{u2, u2} β (Finset.{u2} β) (Finset.hasInsert.{u2} β (fun (a : β) (b : β) => _inst_2 a b)) b s) h f) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1) (f b) (Finset.sup'.{u1, u2} α β _inst_1 s H f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] {s : Finset.{u2} β} (H : Finset.Nonempty.{u2} β s) (f : β -> α) [_inst_2 : DecidableEq.{succ u2} β] {b : β} {h : Finset.Nonempty.{u2} β (Insert.insert.{u2, u2} β (Finset.{u2} β) (Finset.instInsertFinset.{u2} β (fun (a : β) (b : β) => _inst_2 a b)) b s)}, Eq.{succ u1} α (Finset.sup'.{u1, u2} α β _inst_1 (Insert.insert.{u2, u2} β (Finset.{u2} β) (Finset.instInsertFinset.{u2} β (fun (a : β) (b : β) => _inst_2 a b)) b s) h f) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_1) (f b) (Finset.sup'.{u1, u2} α β _inst_1 s H f))
Case conversion may be inaccurate. Consider using '#align finset.sup'_insert Finset.sup'_insertₓ'. -/
@[simp]
theorem sup'_insert [DecidableEq β] {b : β} {h : (insert b s).Nonempty} :
    (insert b s).sup' h f = f b ⊔ s.sup' H f :=
  by
  rw [← WithBot.coe_eq_coe]
  simp only [coe_sup', sup_insert, WithBot.coe_sup]
#align finset.sup'_insert Finset.sup'_insert

#print Finset.sup'_singleton /-
@[simp]
theorem sup'_singleton {b : β} {h : ({b} : Finset β).Nonempty} : ({b} : Finset β).sup' h f = f b :=
  rfl
#align finset.sup'_singleton Finset.sup'_singleton
-/

/- warning: finset.sup'_le -> Finset.sup'_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] {s : Finset.{u2} β} (H : Finset.Nonempty.{u2} β s) (f : β -> α) {a : α}, (forall (b : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) (f b) a)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) (Finset.sup'.{u1, u2} α β _inst_1 s H f) a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] {s : Finset.{u2} β} (H : Finset.Nonempty.{u2} β s) (f : β -> α) {a : α}, (forall (b : β), (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) (f b) a)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) (Finset.sup'.{u1, u2} α β _inst_1 s H f) a)
Case conversion may be inaccurate. Consider using '#align finset.sup'_le Finset.sup'_leₓ'. -/
theorem sup'_le {a : α} (hs : ∀ b ∈ s, f b ≤ a) : s.sup' H f ≤ a :=
  by
  rw [← WithBot.coe_le_coe, coe_sup']
  exact Finset.sup_le fun b h => WithBot.coe_le_coe.2 <| hs b h
#align finset.sup'_le Finset.sup'_le

/- warning: finset.le_sup' -> Finset.le_sup' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] {s : Finset.{u2} β} (f : β -> α) {b : β} (h : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) (f b) (Finset.sup'.{u1, u2} α β _inst_1 s (Exists.intro.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s) b h) f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] {s : Finset.{u2} β} (f : β -> α) {b : β} (h : Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b s), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) (f b) (Finset.sup'.{u1, u2} α β _inst_1 s (Exists.intro.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) x s) b h) f)
Case conversion may be inaccurate. Consider using '#align finset.le_sup' Finset.le_sup'ₓ'. -/
theorem le_sup' {b : β} (h : b ∈ s) : f b ≤ s.sup' ⟨b, h⟩ f :=
  by
  rw [← WithBot.coe_le_coe, coe_sup']
  exact le_sup h
#align finset.le_sup' Finset.le_sup'

/- warning: finset.le_sup'_of_le -> Finset.le_sup'_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] {s : Finset.{u2} β} (f : β -> α) {a : α} {b : β} (hb : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s), (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) a (f b)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) a (Finset.sup'.{u1, u2} α β _inst_1 s (Exists.intro.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s) b hb) f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] {s : Finset.{u2} β} (f : β -> α) {a : α} {b : β} (hb : Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b s), (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) a (f b)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) a (Finset.sup'.{u1, u2} α β _inst_1 s (Exists.intro.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) x s) b hb) f))
Case conversion may be inaccurate. Consider using '#align finset.le_sup'_of_le Finset.le_sup'_of_leₓ'. -/
theorem le_sup'_of_le {a : α} {b : β} (hb : b ∈ s) (h : a ≤ f b) : a ≤ s.sup' ⟨b, hb⟩ f :=
  h.trans <| le_sup' _ hb
#align finset.le_sup'_of_le Finset.le_sup'_of_le

/- warning: finset.sup'_const -> Finset.sup'_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] {s : Finset.{u2} β} (H : Finset.Nonempty.{u2} β s) (a : α), Eq.{succ u1} α (Finset.sup'.{u1, u2} α β _inst_1 s H (fun (b : β) => a)) a
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SemilatticeSup.{u2} α] {s : Finset.{u1} β} (H : Finset.Nonempty.{u1} β s) (a : α), Eq.{succ u2} α (Finset.sup'.{u2, u1} α β _inst_1 s H (fun (b : β) => a)) a
Case conversion may be inaccurate. Consider using '#align finset.sup'_const Finset.sup'_constₓ'. -/
@[simp]
theorem sup'_const (a : α) : (s.sup' H fun b => a) = a :=
  by
  apply le_antisymm
  · apply sup'_le
    intros
    exact le_rfl
  · apply le_sup' (fun b => a) H.some_spec
#align finset.sup'_const Finset.sup'_const

/- warning: finset.sup'_le_iff -> Finset.sup'_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] {s : Finset.{u2} β} (H : Finset.Nonempty.{u2} β s) (f : β -> α) {a : α}, Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) (Finset.sup'.{u1, u2} α β _inst_1 s H f) a) (forall (b : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) (f b) a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SemilatticeSup.{u2} α] {s : Finset.{u1} β} (H : Finset.Nonempty.{u1} β s) (f : β -> α) {a : α}, Iff (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1))) (Finset.sup'.{u2, u1} α β _inst_1 s H f) a) (forall (b : β), (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) b s) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1))) (f b) a))
Case conversion may be inaccurate. Consider using '#align finset.sup'_le_iff Finset.sup'_le_iffₓ'. -/
@[simp]
theorem sup'_le_iff {a : α} : s.sup' H f ≤ a ↔ ∀ b ∈ s, f b ≤ a :=
  Iff.intro (fun h b hb => trans (le_sup' f hb) h) (sup'_le H f)
#align finset.sup'_le_iff Finset.sup'_le_iff

/- warning: finset.sup'_bUnion -> Finset.sup'_biUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SemilatticeSup.{u1} α] (f : β -> α) [_inst_2 : DecidableEq.{succ u2} β] {s : Finset.{u3} γ} (Hs : Finset.Nonempty.{u3} γ s) {t : γ -> (Finset.{u2} β)} (Ht : forall (b : γ), Finset.Nonempty.{u2} β (t b)), Eq.{succ u1} α (Finset.sup'.{u1, u2} α β _inst_1 (Finset.biUnion.{u3, u2} γ β (fun (a : β) (b : β) => _inst_2 a b) s t) (Finset.Nonempty.biUnion.{u3, u2} γ β (fun (a : β) (b : β) => _inst_2 a b) s t Hs (fun (b : γ) (_x : Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) b s) => Ht b)) f) (Finset.sup'.{u1, u3} α γ _inst_1 s Hs (fun (b : γ) => Finset.sup'.{u1, u2} α β _inst_1 (t b) (Ht b) f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] (f : β -> α) [_inst_2 : DecidableEq.{succ u3} β] {s : Finset.{u2} γ} (Hs : Finset.Nonempty.{u2} γ s) {t : γ -> (Finset.{u3} β)} (Ht : forall (b : γ), Finset.Nonempty.{u3} β (t b)), Eq.{succ u1} α (Finset.sup'.{u1, u3} α β _inst_1 (Finset.biUnion.{u2, u3} γ β (fun (a : β) (b : β) => _inst_2 a b) s t) (Finset.Nonempty.biUnion.{u3, u2} γ β (fun (a : β) (b : β) => _inst_2 a b) s t Hs (fun (b : γ) (_x : Membership.mem.{u2, u2} γ (Finset.{u2} γ) (Finset.instMembershipFinset.{u2} γ) b s) => Ht b)) f) (Finset.sup'.{u1, u2} α γ _inst_1 s Hs (fun (b : γ) => Finset.sup'.{u1, u3} α β _inst_1 (t b) (Ht b) f))
Case conversion may be inaccurate. Consider using '#align finset.sup'_bUnion Finset.sup'_biUnionₓ'. -/
theorem sup'_biUnion [DecidableEq β] {s : Finset γ} (Hs : s.Nonempty) {t : γ → Finset β}
    (Ht : ∀ b, (t b).Nonempty) :
    (s.biUnion t).sup' (Hs.biUnion fun b _ => Ht b) f = s.sup' Hs fun b => (t b).sup' (Ht b) f :=
  eq_of_forall_ge_iff fun c => by simp [@forall_swap _ β]
#align finset.sup'_bUnion Finset.sup'_biUnion

/- warning: finset.comp_sup'_eq_sup'_comp -> Finset.comp_sup'_eq_sup'_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : SemilatticeSup.{u3} γ] {s : Finset.{u2} β} (H : Finset.Nonempty.{u2} β s) {f : β -> α} (g : α -> γ), (forall (x : α) (y : α), Eq.{succ u3} γ (g (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1) x y)) (Sup.sup.{u3} γ (SemilatticeSup.toHasSup.{u3} γ _inst_2) (g x) (g y))) -> (Eq.{succ u3} γ (g (Finset.sup'.{u1, u2} α β _inst_1 s H f)) (Finset.sup'.{u3, u2} γ β _inst_2 s H (Function.comp.{succ u2, succ u1, succ u3} β α γ g f)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : SemilatticeSup.{u3} γ] {s : Finset.{u2} β} (H : Finset.Nonempty.{u2} β s) {f : β -> α} (g : α -> γ), (forall (x : α) (y : α), Eq.{succ u3} γ (g (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_1) x y)) (Sup.sup.{u3} γ (SemilatticeSup.toSup.{u3} γ _inst_2) (g x) (g y))) -> (Eq.{succ u3} γ (g (Finset.sup'.{u1, u2} α β _inst_1 s H f)) (Finset.sup'.{u3, u2} γ β _inst_2 s H (Function.comp.{succ u2, succ u1, succ u3} β α γ g f)))
Case conversion may be inaccurate. Consider using '#align finset.comp_sup'_eq_sup'_comp Finset.comp_sup'_eq_sup'_compₓ'. -/
theorem comp_sup'_eq_sup'_comp [SemilatticeSup γ] {s : Finset β} (H : s.Nonempty) {f : β → α}
    (g : α → γ) (g_sup : ∀ x y, g (x ⊔ y) = g x ⊔ g y) : g (s.sup' H f) = s.sup' H (g ∘ f) :=
  by
  rw [← WithBot.coe_eq_coe, coe_sup']
  let g' := WithBot.map g
  show g' ↑(s.sup' H f) = s.sup fun a => g' ↑(f a)
  rw [coe_sup']
  refine' comp_sup_eq_sup_comp g' _ rfl
  intro f₁ f₂
  induction f₁ using WithBot.recBotCoe
  · rw [bot_sup_eq]
    exact bot_sup_eq.symm
  · induction f₂ using WithBot.recBotCoe
    · rfl
    · exact congr_arg coe (g_sup f₁ f₂)
#align finset.comp_sup'_eq_sup'_comp Finset.comp_sup'_eq_sup'_comp

/- warning: finset.sup'_induction -> Finset.sup'_induction is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] {s : Finset.{u2} β} (H : Finset.Nonempty.{u2} β s) (f : β -> α) {p : α -> Prop}, (forall (a₁ : α), (p a₁) -> (forall (a₂ : α), (p a₂) -> (p (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1) a₁ a₂)))) -> (forall (b : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s) -> (p (f b))) -> (p (Finset.sup'.{u1, u2} α β _inst_1 s H f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SemilatticeSup.{u2} α] {s : Finset.{u1} β} (H : Finset.Nonempty.{u1} β s) (f : β -> α) {p : α -> Prop}, (forall (a₁ : α), (p a₁) -> (forall (a₂ : α), (p a₂) -> (p (Sup.sup.{u2} α (SemilatticeSup.toSup.{u2} α _inst_1) a₁ a₂)))) -> (forall (b : β), (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) b s) -> (p (f b))) -> (p (Finset.sup'.{u2, u1} α β _inst_1 s H f))
Case conversion may be inaccurate. Consider using '#align finset.sup'_induction Finset.sup'_inductionₓ'. -/
theorem sup'_induction {p : α → Prop} (hp : ∀ a₁, p a₁ → ∀ a₂, p a₂ → p (a₁ ⊔ a₂))
    (hs : ∀ b ∈ s, p (f b)) : p (s.sup' H f) :=
  by
  show @WithBot.recBotCoe α (fun _ => Prop) True p ↑(s.sup' H f)
  rw [coe_sup']
  refine' sup_induction trivial _ hs
  rintro (_ | a₁) h₁ a₂ h₂
  · rw [WithBot.none_eq_bot, bot_sup_eq]
    exact h₂
  cases a₂
  exacts[h₁, hp a₁ h₁ a₂ h₂]
#align finset.sup'_induction Finset.sup'_induction

/- warning: finset.sup'_mem -> Finset.sup'_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] (s : Set.{u1} α), (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1) x y) s))) -> (forall {ι : Type.{u2}} (t : Finset.{u2} ι) (H : Finset.Nonempty.{u2} ι t) (p : ι -> α), (forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i t) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (p i) s)) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Finset.sup'.{u1, u2} α ι _inst_1 t H p) s))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : SemilatticeSup.{u2} α] (s : Set.{u2} α), (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (forall (y : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) y s) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (Sup.sup.{u2} α (SemilatticeSup.toSup.{u2} α _inst_1) x y) s))) -> (forall {ι : Type.{u1}} (t : Finset.{u1} ι) (H : Finset.Nonempty.{u1} ι t) (p : ι -> α), (forall (i : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i t) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (p i) s)) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (Finset.sup'.{u2, u1} α ι _inst_1 t H p) s))
Case conversion may be inaccurate. Consider using '#align finset.sup'_mem Finset.sup'_memₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » s) -/
theorem sup'_mem (s : Set α) (w : ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s), x ⊔ y ∈ s) {ι : Type _}
    (t : Finset ι) (H : t.Nonempty) (p : ι → α) (h : ∀ i ∈ t, p i ∈ s) : t.sup' H p ∈ s :=
  sup'_induction H p w h
#align finset.sup'_mem Finset.sup'_mem

#print Finset.sup'_congr /-
@[congr]
theorem sup'_congr {t : Finset β} {f g : β → α} (h₁ : s = t) (h₂ : ∀ x ∈ s, f x = g x) :
    s.sup' H f = t.sup' (h₁ ▸ H) g := by
  subst s
  refine' eq_of_forall_ge_iff fun c => _
  simp (config := { contextual := true }) only [sup'_le_iff, h₂]
#align finset.sup'_congr Finset.sup'_congr
-/

#print Finset.sup'_map /-
@[simp]
theorem sup'_map {s : Finset γ} {f : γ ↪ β} (g : β → α) (hs : (s.map f).Nonempty)
    (hs' : s.Nonempty := Finset.map_nonempty.mp hs) : (s.map f).sup' hs g = s.sup' hs' (g ∘ f) := by
  rw [← WithBot.coe_eq_coe, coe_sup', sup_map, coe_sup']
#align finset.sup'_map Finset.sup'_map
-/

end Sup'

section Inf'

variable [SemilatticeInf α]

#print Finset.inf_of_mem /-
theorem inf_of_mem {s : Finset β} (f : β → α) {b : β} (h : b ∈ s) :
    ∃ a : α, s.inf (coe ∘ f : β → WithTop α) = ↑a :=
  @sup_of_mem αᵒᵈ _ _ _ f _ h
#align finset.inf_of_mem Finset.inf_of_mem
-/

#print Finset.inf' /-
/-- Given nonempty finset `s` then `s.inf' H f` is the infimum of its image under `f` in (possibly
unbounded) meet-semilattice `α`, where `H` is a proof of nonemptiness. If `α` has a top element you
may instead use `finset.inf` which does not require `s` nonempty. -/
def inf' (s : Finset β) (H : s.Nonempty) (f : β → α) : α :=
  WithTop.untop (s.inf (coe ∘ f)) (by simpa using H)
#align finset.inf' Finset.inf'
-/

variable {s : Finset β} (H : s.Nonempty) (f : β → α) {a : α} {b : β}

/- warning: finset.coe_inf' -> Finset.coe_inf' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] {s : Finset.{u2} β} (H : Finset.Nonempty.{u2} β s) (f : β -> α), Eq.{succ u1} (WithTop.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) (Finset.inf'.{u1, u2} α β _inst_1 s H f)) (Finset.inf.{u1, u2} (WithTop.{u1} α) β (WithTop.semilatticeInf.{u1} α _inst_1) (WithTop.orderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) s (Function.comp.{succ u2, succ u1, succ u1} β α (WithTop.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α)))) f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SemilatticeInf.{u2} α] {s : Finset.{u1} β} (H : Finset.Nonempty.{u1} β s) (f : β -> α), Eq.{succ u2} (WithTop.{u2} α) (WithTop.some.{u2} α (Finset.inf'.{u2, u1} α β _inst_1 s H f)) (Finset.inf.{u2, u1} (WithTop.{u2} α) β (WithTop.semilatticeInf.{u2} α _inst_1) (WithTop.orderTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1)))) s (Function.comp.{succ u1, succ u2, succ u2} β α (WithTop.{u2} α) (WithTop.some.{u2} α) f))
Case conversion may be inaccurate. Consider using '#align finset.coe_inf' Finset.coe_inf'ₓ'. -/
@[simp]
theorem coe_inf' : ((s.inf' H f : α) : WithTop α) = s.inf (coe ∘ f) :=
  @coe_sup' αᵒᵈ _ _ _ H f
#align finset.coe_inf' Finset.coe_inf'

/- warning: finset.inf'_cons -> Finset.inf'_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] {s : Finset.{u2} β} (H : Finset.Nonempty.{u2} β s) (f : β -> α) {b : β} {hb : Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s)} {h : Finset.Nonempty.{u2} β (Finset.cons.{u2} β b s hb)}, Eq.{succ u1} α (Finset.inf'.{u1, u2} α β _inst_1 (Finset.cons.{u2} β b s hb) h f) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1) (f b) (Finset.inf'.{u1, u2} α β _inst_1 s H f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] {s : Finset.{u2} β} (H : Finset.Nonempty.{u2} β s) (f : β -> α) {b : β} {hb : Not (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b s)} {h : Finset.Nonempty.{u2} β (Finset.cons.{u2} β b s hb)}, Eq.{succ u1} α (Finset.inf'.{u1, u2} α β _inst_1 (Finset.cons.{u2} β b s hb) h f) (Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_1) (f b) (Finset.inf'.{u1, u2} α β _inst_1 s H f))
Case conversion may be inaccurate. Consider using '#align finset.inf'_cons Finset.inf'_consₓ'. -/
@[simp]
theorem inf'_cons {b : β} {hb : b ∉ s} {h : (cons b s hb).Nonempty} :
    (cons b s hb).inf' h f = f b ⊓ s.inf' H f :=
  @sup'_cons αᵒᵈ _ _ _ H f _ _ h
#align finset.inf'_cons Finset.inf'_cons

/- warning: finset.inf'_insert -> Finset.inf'_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] {s : Finset.{u2} β} (H : Finset.Nonempty.{u2} β s) (f : β -> α) [_inst_2 : DecidableEq.{succ u2} β] {b : β} {h : Finset.Nonempty.{u2} β (Insert.insert.{u2, u2} β (Finset.{u2} β) (Finset.hasInsert.{u2} β (fun (a : β) (b : β) => _inst_2 a b)) b s)}, Eq.{succ u1} α (Finset.inf'.{u1, u2} α β _inst_1 (Insert.insert.{u2, u2} β (Finset.{u2} β) (Finset.hasInsert.{u2} β (fun (a : β) (b : β) => _inst_2 a b)) b s) h f) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1) (f b) (Finset.inf'.{u1, u2} α β _inst_1 s H f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] {s : Finset.{u2} β} (H : Finset.Nonempty.{u2} β s) (f : β -> α) [_inst_2 : DecidableEq.{succ u2} β] {b : β} {h : Finset.Nonempty.{u2} β (Insert.insert.{u2, u2} β (Finset.{u2} β) (Finset.instInsertFinset.{u2} β (fun (a : β) (b : β) => _inst_2 a b)) b s)}, Eq.{succ u1} α (Finset.inf'.{u1, u2} α β _inst_1 (Insert.insert.{u2, u2} β (Finset.{u2} β) (Finset.instInsertFinset.{u2} β (fun (a : β) (b : β) => _inst_2 a b)) b s) h f) (Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_1) (f b) (Finset.inf'.{u1, u2} α β _inst_1 s H f))
Case conversion may be inaccurate. Consider using '#align finset.inf'_insert Finset.inf'_insertₓ'. -/
@[simp]
theorem inf'_insert [DecidableEq β] {b : β} {h : (insert b s).Nonempty} :
    (insert b s).inf' h f = f b ⊓ s.inf' H f :=
  @sup'_insert αᵒᵈ _ _ _ H f _ _ h
#align finset.inf'_insert Finset.inf'_insert

#print Finset.inf'_singleton /-
@[simp]
theorem inf'_singleton {b : β} {h : ({b} : Finset β).Nonempty} : ({b} : Finset β).inf' h f = f b :=
  rfl
#align finset.inf'_singleton Finset.inf'_singleton
-/

/- warning: finset.le_inf' -> Finset.le_inf' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] {s : Finset.{u2} β} (H : Finset.Nonempty.{u2} β s) (f : β -> α) {a : α}, (forall (b : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) a (f b))) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) a (Finset.inf'.{u1, u2} α β _inst_1 s H f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] {s : Finset.{u2} β} (H : Finset.Nonempty.{u2} β s) (f : β -> α) {a : α}, (forall (b : β), (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) a (f b))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) a (Finset.inf'.{u1, u2} α β _inst_1 s H f))
Case conversion may be inaccurate. Consider using '#align finset.le_inf' Finset.le_inf'ₓ'. -/
theorem le_inf' (hs : ∀ b ∈ s, a ≤ f b) : a ≤ s.inf' H f :=
  @sup'_le αᵒᵈ _ _ _ H f _ hs
#align finset.le_inf' Finset.le_inf'

/- warning: finset.inf'_le -> Finset.inf'_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] {s : Finset.{u2} β} (f : β -> α) {b : β} (h : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) (Finset.inf'.{u1, u2} α β _inst_1 s (Exists.intro.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s) b h) f) (f b)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] {s : Finset.{u2} β} (f : β -> α) {b : β} (h : Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b s), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) (Finset.inf'.{u1, u2} α β _inst_1 s (Exists.intro.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) x s) b h) f) (f b)
Case conversion may be inaccurate. Consider using '#align finset.inf'_le Finset.inf'_leₓ'. -/
theorem inf'_le (h : b ∈ s) : s.inf' ⟨b, h⟩ f ≤ f b :=
  @le_sup' αᵒᵈ _ _ _ f _ h
#align finset.inf'_le Finset.inf'_le

/- warning: finset.inf'_le_of_le -> Finset.inf'_le_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] {s : Finset.{u2} β} (f : β -> α) {a : α} {b : β} (hb : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s), (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) (f b) a) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) (Finset.inf'.{u1, u2} α β _inst_1 s (Exists.intro.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s) b hb) f) a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] {s : Finset.{u2} β} (f : β -> α) {a : β} {b : α} (hb : Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) a s), (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) (f a) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) (Finset.inf'.{u1, u2} α β _inst_1 s (Exists.intro.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) x s) a hb) f) b)
Case conversion may be inaccurate. Consider using '#align finset.inf'_le_of_le Finset.inf'_le_of_leₓ'. -/
theorem inf'_le_of_le (hb : b ∈ s) (h : f b ≤ a) : s.inf' ⟨b, hb⟩ f ≤ a :=
  (inf'_le _ hb).trans h
#align finset.inf'_le_of_le Finset.inf'_le_of_le

/- warning: finset.inf'_const -> Finset.inf'_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] {s : Finset.{u2} β} (H : Finset.Nonempty.{u2} β s) (a : α), Eq.{succ u1} α (Finset.inf'.{u1, u2} α β _inst_1 s H (fun (b : β) => a)) a
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SemilatticeInf.{u2} α] {s : Finset.{u1} β} (H : Finset.Nonempty.{u1} β s) (a : α), Eq.{succ u2} α (Finset.inf'.{u2, u1} α β _inst_1 s H (fun (b : β) => a)) a
Case conversion may be inaccurate. Consider using '#align finset.inf'_const Finset.inf'_constₓ'. -/
@[simp]
theorem inf'_const (a : α) : (s.inf' H fun b => a) = a :=
  @sup'_const αᵒᵈ _ _ _ H _
#align finset.inf'_const Finset.inf'_const

/- warning: finset.le_inf'_iff -> Finset.le_inf'_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] {s : Finset.{u2} β} (H : Finset.Nonempty.{u2} β s) (f : β -> α) {a : α}, Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) a (Finset.inf'.{u1, u2} α β _inst_1 s H f)) (forall (b : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) a (f b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SemilatticeInf.{u2} α] {s : Finset.{u1} β} (H : Finset.Nonempty.{u1} β s) (f : β -> α) {a : α}, Iff (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1))) a (Finset.inf'.{u2, u1} α β _inst_1 s H f)) (forall (b : β), (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) b s) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1))) a (f b)))
Case conversion may be inaccurate. Consider using '#align finset.le_inf'_iff Finset.le_inf'_iffₓ'. -/
@[simp]
theorem le_inf'_iff : a ≤ s.inf' H f ↔ ∀ b ∈ s, a ≤ f b :=
  @sup'_le_iff αᵒᵈ _ _ _ H f _
#align finset.le_inf'_iff Finset.le_inf'_iff

/- warning: finset.inf'_bUnion -> Finset.inf'_biUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SemilatticeInf.{u1} α] (f : β -> α) [_inst_2 : DecidableEq.{succ u2} β] {s : Finset.{u3} γ} (Hs : Finset.Nonempty.{u3} γ s) {t : γ -> (Finset.{u2} β)} (Ht : forall (b : γ), Finset.Nonempty.{u2} β (t b)), Eq.{succ u1} α (Finset.inf'.{u1, u2} α β _inst_1 (Finset.biUnion.{u3, u2} γ β (fun (a : β) (b : β) => _inst_2 a b) s t) (Finset.Nonempty.biUnion.{u3, u2} γ β (fun (a : β) (b : β) => _inst_2 a b) s t Hs (fun (b : γ) (_x : Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) b s) => Ht b)) f) (Finset.inf'.{u1, u3} α γ _inst_1 s Hs (fun (b : γ) => Finset.inf'.{u1, u2} α β _inst_1 (t b) (Ht b) f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] (f : β -> α) [_inst_2 : DecidableEq.{succ u3} β] {s : Finset.{u2} γ} (Hs : Finset.Nonempty.{u2} γ s) {t : γ -> (Finset.{u3} β)} (Ht : forall (b : γ), Finset.Nonempty.{u3} β (t b)), Eq.{succ u1} α (Finset.inf'.{u1, u3} α β _inst_1 (Finset.biUnion.{u2, u3} γ β (fun (a : β) (b : β) => _inst_2 a b) s t) (Finset.Nonempty.biUnion.{u3, u2} γ β (fun (a : β) (b : β) => _inst_2 a b) s t Hs (fun (b : γ) (_x : Membership.mem.{u2, u2} γ (Finset.{u2} γ) (Finset.instMembershipFinset.{u2} γ) b s) => Ht b)) f) (Finset.inf'.{u1, u2} α γ _inst_1 s Hs (fun (b : γ) => Finset.inf'.{u1, u3} α β _inst_1 (t b) (Ht b) f))
Case conversion may be inaccurate. Consider using '#align finset.inf'_bUnion Finset.inf'_biUnionₓ'. -/
theorem inf'_biUnion [DecidableEq β] {s : Finset γ} (Hs : s.Nonempty) {t : γ → Finset β}
    (Ht : ∀ b, (t b).Nonempty) :
    (s.biUnion t).inf' (Hs.biUnion fun b _ => Ht b) f = s.inf' Hs fun b => (t b).inf' (Ht b) f :=
  @sup'_biUnion αᵒᵈ _ _ _ _ _ _ Hs _ Ht
#align finset.inf'_bUnion Finset.inf'_biUnion

/- warning: finset.comp_inf'_eq_inf'_comp -> Finset.comp_inf'_eq_inf'_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : SemilatticeInf.{u3} γ] {s : Finset.{u2} β} (H : Finset.Nonempty.{u2} β s) {f : β -> α} (g : α -> γ), (forall (x : α) (y : α), Eq.{succ u3} γ (g (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1) x y)) (Inf.inf.{u3} γ (SemilatticeInf.toHasInf.{u3} γ _inst_2) (g x) (g y))) -> (Eq.{succ u3} γ (g (Finset.inf'.{u1, u2} α β _inst_1 s H f)) (Finset.inf'.{u3, u2} γ β _inst_2 s H (Function.comp.{succ u2, succ u1, succ u3} β α γ g f)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : SemilatticeInf.{u3} γ] {s : Finset.{u2} β} (H : Finset.Nonempty.{u2} β s) {f : β -> α} (g : α -> γ), (forall (x : α) (y : α), Eq.{succ u3} γ (g (Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_1) x y)) (Inf.inf.{u3} γ (SemilatticeInf.toInf.{u3} γ _inst_2) (g x) (g y))) -> (Eq.{succ u3} γ (g (Finset.inf'.{u1, u2} α β _inst_1 s H f)) (Finset.inf'.{u3, u2} γ β _inst_2 s H (Function.comp.{succ u2, succ u1, succ u3} β α γ g f)))
Case conversion may be inaccurate. Consider using '#align finset.comp_inf'_eq_inf'_comp Finset.comp_inf'_eq_inf'_compₓ'. -/
theorem comp_inf'_eq_inf'_comp [SemilatticeInf γ] {s : Finset β} (H : s.Nonempty) {f : β → α}
    (g : α → γ) (g_inf : ∀ x y, g (x ⊓ y) = g x ⊓ g y) : g (s.inf' H f) = s.inf' H (g ∘ f) :=
  @comp_sup'_eq_sup'_comp αᵒᵈ _ γᵒᵈ _ _ _ H f g g_inf
#align finset.comp_inf'_eq_inf'_comp Finset.comp_inf'_eq_inf'_comp

/- warning: finset.inf'_induction -> Finset.inf'_induction is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] {s : Finset.{u2} β} (H : Finset.Nonempty.{u2} β s) (f : β -> α) {p : α -> Prop}, (forall (a₁ : α), (p a₁) -> (forall (a₂ : α), (p a₂) -> (p (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1) a₁ a₂)))) -> (forall (b : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s) -> (p (f b))) -> (p (Finset.inf'.{u1, u2} α β _inst_1 s H f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SemilatticeInf.{u2} α] {s : Finset.{u1} β} (H : Finset.Nonempty.{u1} β s) (f : β -> α) {p : α -> Prop}, (forall (a₁ : α), (p a₁) -> (forall (a₂ : α), (p a₂) -> (p (Inf.inf.{u2} α (SemilatticeInf.toInf.{u2} α _inst_1) a₁ a₂)))) -> (forall (b : β), (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) b s) -> (p (f b))) -> (p (Finset.inf'.{u2, u1} α β _inst_1 s H f))
Case conversion may be inaccurate. Consider using '#align finset.inf'_induction Finset.inf'_inductionₓ'. -/
theorem inf'_induction {p : α → Prop} (hp : ∀ a₁, p a₁ → ∀ a₂, p a₂ → p (a₁ ⊓ a₂))
    (hs : ∀ b ∈ s, p (f b)) : p (s.inf' H f) :=
  @sup'_induction αᵒᵈ _ _ _ H f _ hp hs
#align finset.inf'_induction Finset.inf'_induction

/- warning: finset.inf'_mem -> Finset.inf'_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] (s : Set.{u1} α), (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1) x y) s))) -> (forall {ι : Type.{u2}} (t : Finset.{u2} ι) (H : Finset.Nonempty.{u2} ι t) (p : ι -> α), (forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i t) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (p i) s)) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Finset.inf'.{u1, u2} α ι _inst_1 t H p) s))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : SemilatticeInf.{u2} α] (s : Set.{u2} α), (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (forall (y : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) y s) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (Inf.inf.{u2} α (SemilatticeInf.toInf.{u2} α _inst_1) x y) s))) -> (forall {ι : Type.{u1}} (t : Finset.{u1} ι) (H : Finset.Nonempty.{u1} ι t) (p : ι -> α), (forall (i : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i t) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (p i) s)) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (Finset.inf'.{u2, u1} α ι _inst_1 t H p) s))
Case conversion may be inaccurate. Consider using '#align finset.inf'_mem Finset.inf'_memₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » s) -/
theorem inf'_mem (s : Set α) (w : ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s), x ⊓ y ∈ s) {ι : Type _}
    (t : Finset ι) (H : t.Nonempty) (p : ι → α) (h : ∀ i ∈ t, p i ∈ s) : t.inf' H p ∈ s :=
  inf'_induction H p w h
#align finset.inf'_mem Finset.inf'_mem

#print Finset.inf'_congr /-
@[congr]
theorem inf'_congr {t : Finset β} {f g : β → α} (h₁ : s = t) (h₂ : ∀ x ∈ s, f x = g x) :
    s.inf' H f = t.inf' (h₁ ▸ H) g :=
  @sup'_congr αᵒᵈ _ _ _ H _ _ _ h₁ h₂
#align finset.inf'_congr Finset.inf'_congr
-/

#print Finset.inf'_map /-
@[simp]
theorem inf'_map {s : Finset γ} {f : γ ↪ β} (g : β → α) (hs : (s.map f).Nonempty)
    (hs' : s.Nonempty := Finset.map_nonempty.mp hs) : (s.map f).inf' hs g = s.inf' hs' (g ∘ f) :=
  @sup'_map αᵒᵈ _ _ _ _ _ _ hs hs'
#align finset.inf'_map Finset.inf'_map
-/

end Inf'

section Sup

variable [SemilatticeSup α] [OrderBot α]

/- warning: finset.sup'_eq_sup -> Finset.sup'_eq_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} (H : Finset.Nonempty.{u2} β s) (f : β -> α), Eq.{succ u1} α (Finset.sup'.{u1, u2} α β _inst_1 s H f) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} (H : Finset.Nonempty.{u2} β s) (f : β -> α), Eq.{succ u1} α (Finset.sup'.{u1, u2} α β _inst_1 s H f) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s f)
Case conversion may be inaccurate. Consider using '#align finset.sup'_eq_sup Finset.sup'_eq_supₓ'. -/
theorem sup'_eq_sup {s : Finset β} (H : s.Nonempty) (f : β → α) : s.sup' H f = s.sup f :=
  le_antisymm (sup'_le H f fun b => le_sup) (Finset.sup_le fun b => le_sup' f)
#align finset.sup'_eq_sup Finset.sup'_eq_sup

/- warning: finset.sup_closed_of_sup_closed -> Finset.sup_closed_of_sup_closed is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {s : Set.{u1} α} (t : Finset.{u1} α), (Finset.Nonempty.{u1} α t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) t) s) -> (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1) a b) s))) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Finset.sup.{u1, u1} α α _inst_1 _inst_2 t (id.{succ u1} α)) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {s : Set.{u1} α} (t : Finset.{u1} α), (Finset.Nonempty.{u1} α t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Finset.toSet.{u1} α t) s) -> (forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_1) a b) s))) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (Finset.sup.{u1, u1} α α _inst_1 _inst_2 t (id.{succ u1} α)) s)
Case conversion may be inaccurate. Consider using '#align finset.sup_closed_of_sup_closed Finset.sup_closed_of_sup_closedₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (a b «expr ∈ » s) -/
theorem sup_closed_of_sup_closed {s : Set α} (t : Finset α) (htne : t.Nonempty) (h_subset : ↑t ⊆ s)
    (h : ∀ (a) (_ : a ∈ s) (b) (_ : b ∈ s), a ⊔ b ∈ s) : t.sup id ∈ s :=
  sup'_eq_sup htne id ▸ sup'_induction _ _ h h_subset
#align finset.sup_closed_of_sup_closed Finset.sup_closed_of_sup_closed

/- warning: finset.coe_sup_of_nonempty -> Finset.coe_sup_of_nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β}, (Finset.Nonempty.{u2} β s) -> (forall (f : β -> α), Eq.{succ u1} (WithBot.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s f)) (Finset.sup.{u1, u2} (WithBot.{u1} α) β (WithBot.semilatticeSup.{u1} α _inst_1) (WithBot.orderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) s (Function.comp.{succ u2, succ u1, succ u1} β α (WithBot.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α)))) f)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β}, (Finset.Nonempty.{u2} β s) -> (forall (f : β -> α), Eq.{succ u1} (WithBot.{u1} α) (WithBot.some.{u1} α (Finset.sup.{u1, u2} α β _inst_1 _inst_2 s f)) (Finset.sup.{u1, u2} (WithBot.{u1} α) β (WithBot.semilatticeSup.{u1} α _inst_1) (WithBot.orderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) s (Function.comp.{succ u2, succ u1, succ u1} β α (WithBot.{u1} α) (WithBot.some.{u1} α) f)))
Case conversion may be inaccurate. Consider using '#align finset.coe_sup_of_nonempty Finset.coe_sup_of_nonemptyₓ'. -/
theorem coe_sup_of_nonempty {s : Finset β} (h : s.Nonempty) (f : β → α) :
    (↑(s.sup f) : WithBot α) = s.sup (coe ∘ f) := by simp only [← sup'_eq_sup h, coe_sup' h]
#align finset.coe_sup_of_nonempty Finset.coe_sup_of_nonempty

end Sup

section Inf

variable [SemilatticeInf α] [OrderTop α]

/- warning: finset.inf'_eq_inf -> Finset.inf'_eq_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} (H : Finset.Nonempty.{u2} β s) (f : β -> α), Eq.{succ u1} α (Finset.inf'.{u1, u2} α β _inst_1 s H f) (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β} (H : Finset.Nonempty.{u2} β s) (f : β -> α), Eq.{succ u1} α (Finset.inf'.{u1, u2} α β _inst_1 s H f) (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s f)
Case conversion may be inaccurate. Consider using '#align finset.inf'_eq_inf Finset.inf'_eq_infₓ'. -/
theorem inf'_eq_inf {s : Finset β} (H : s.Nonempty) (f : β → α) : s.inf' H f = s.inf f :=
  @sup'_eq_sup αᵒᵈ _ _ _ _ H f
#align finset.inf'_eq_inf Finset.inf'_eq_inf

/- warning: finset.inf_closed_of_inf_closed -> Finset.inf_closed_of_inf_closed is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Set.{u1} α} (t : Finset.{u1} α), (Finset.Nonempty.{u1} α t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) t) s) -> (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1) a b) s))) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Finset.inf.{u1, u1} α α _inst_1 _inst_2 t (id.{succ u1} α)) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Set.{u1} α} (t : Finset.{u1} α), (Finset.Nonempty.{u1} α t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Finset.toSet.{u1} α t) s) -> (forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_1) a b) s))) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (Finset.inf.{u1, u1} α α _inst_1 _inst_2 t (id.{succ u1} α)) s)
Case conversion may be inaccurate. Consider using '#align finset.inf_closed_of_inf_closed Finset.inf_closed_of_inf_closedₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (a b «expr ∈ » s) -/
theorem inf_closed_of_inf_closed {s : Set α} (t : Finset α) (htne : t.Nonempty) (h_subset : ↑t ⊆ s)
    (h : ∀ (a) (_ : a ∈ s) (b) (_ : b ∈ s), a ⊓ b ∈ s) : t.inf id ∈ s :=
  @sup_closed_of_sup_closed αᵒᵈ _ _ _ t htne h_subset h
#align finset.inf_closed_of_inf_closed Finset.inf_closed_of_inf_closed

/- warning: finset.coe_inf_of_nonempty -> Finset.coe_inf_of_nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β}, (Finset.Nonempty.{u2} β s) -> (forall (f : β -> α), Eq.{succ u1} (WithTop.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s f)) (Finset.inf.{u1, u2} (WithTop.{u1} α) β (WithTop.semilatticeInf.{u1} α _inst_1) (WithTop.orderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) s (fun (i : β) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) (f i))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] {s : Finset.{u2} β}, (Finset.Nonempty.{u2} β s) -> (forall (f : β -> α), Eq.{succ u1} (WithTop.{u1} α) (WithTop.some.{u1} α (Finset.inf.{u1, u2} α β _inst_1 _inst_2 s f)) (Finset.inf.{u1, u2} (WithTop.{u1} α) β (WithTop.semilatticeInf.{u1} α _inst_1) (WithTop.orderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) s (Function.comp.{succ u2, succ u1, succ u1} β α (WithTop.{u1} α) (WithTop.some.{u1} α) f)))
Case conversion may be inaccurate. Consider using '#align finset.coe_inf_of_nonempty Finset.coe_inf_of_nonemptyₓ'. -/
theorem coe_inf_of_nonempty {s : Finset β} (h : s.Nonempty) (f : β → α) :
    (↑(s.inf f) : WithTop α) = s.inf fun i => f i :=
  @coe_sup_of_nonempty αᵒᵈ _ _ _ _ h f
#align finset.coe_inf_of_nonempty Finset.coe_inf_of_nonempty

end Inf

section Sup

variable {C : β → Type _} [∀ b : β, SemilatticeSup (C b)] [∀ b : β, OrderBot (C b)]

/- warning: finset.sup_apply -> Finset.sup_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {C : β -> Type.{u3}} [_inst_1 : forall (b : β), SemilatticeSup.{u3} (C b)] [_inst_2 : forall (b : β), OrderBot.{u3} (C b) (Preorder.toHasLe.{u3} (C b) (PartialOrder.toPreorder.{u3} (C b) (SemilatticeSup.toPartialOrder.{u3} (C b) (_inst_1 b))))] (s : Finset.{u1} α) (f : α -> (forall (b : β), C b)) (b : β), Eq.{succ u3} (C b) (Finset.sup.{max u2 u3, u1} (forall (b : β), C b) α (Pi.semilatticeSup.{u2, u3} β (fun (b : β) => C b) (fun (i : β) => _inst_1 i)) (Pi.orderBot.{u2, u3} β (fun (b : β) => C b) (fun (i : β) => Preorder.toHasLe.{u3} ((fun (i : β) => (fun (i : β) => (fun (i : β) => (fun (b : β) => C b) i) i) i) i) ((fun (i : β) => PartialOrder.toPreorder.{u3} ((fun (i : β) => (fun (b : β) => C b) i) i) ((fun (_x : β) => PartialOrder.mk.{u3} ((fun (i : β) => (fun (i : β) => (fun (b : β) => C b) i) i) _x) (SemilatticeSup.Le.{u3} ((fun (i : β) => (fun (i : β) => (fun (b : β) => C b) i) i) _x) ((fun (i : β) => _inst_1 i) _x)) (SemilatticeSup.Lt.{u3} ((fun (i : β) => (fun (i : β) => (fun (b : β) => C b) i) i) _x) ((fun (i : β) => _inst_1 i) _x)) (Pi.SemilatticeSup._proof_1.{u2, u3} β (fun (b : β) => C b) (fun (i : β) => _inst_1 i) _x) (Pi.SemilatticeSup._proof_2.{u2, u3} β (fun (b : β) => C b) (fun (i : β) => _inst_1 i) _x) (Pi.SemilatticeSup._proof_3.{u2, u3} β (fun (b : β) => C b) (fun (i : β) => _inst_1 i) _x) (Pi.SemilatticeSup._proof_4.{u2, u3} β (fun (b : β) => C b) (fun (i : β) => _inst_1 i) _x)) i)) i)) (fun (i : β) => _inst_2 i)) s f b) (Finset.sup.{u3, u1} (C b) α (_inst_1 b) (_inst_2 b) s (fun (a : α) => f a b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {C : β -> Type.{u3}} [_inst_1 : forall (b : β), SemilatticeSup.{u3} (C b)] [_inst_2 : forall (b : β), OrderBot.{u3} (C b) (Preorder.toLE.{u3} (C b) (PartialOrder.toPreorder.{u3} (C b) (SemilatticeSup.toPartialOrder.{u3} (C b) (_inst_1 b))))] (s : Finset.{u2} α) (f : α -> (forall (b : β), C b)) (b : β), Eq.{succ u3} (C b) (Finset.sup.{max u1 u3, u2} (forall (b : β), C b) α (Pi.semilatticeSup.{u1, u3} β (fun (b : β) => C b) (fun (i : β) => _inst_1 i)) (Pi.orderBot.{u1, u3} β (fun (b : β) => C b) (fun (i : β) => Preorder.toLE.{u3} ((fun (i : β) => (fun (i : β) => (fun (i : β) => C i) i) i) i) ((fun (i : β) => PartialOrder.toPreorder.{u3} ((fun (i : β) => (fun (b : β) => C b) i) i) ((fun (_x : β) => SemilatticeSup.toPartialOrder.{u3} ((fun (b : β) => C b) _x) ((fun (i : β) => _inst_1 i) _x)) i)) i)) (fun (i : β) => _inst_2 i)) s f b) (Finset.sup.{u3, u2} (C b) α (_inst_1 b) (_inst_2 b) s (fun (a : α) => f a b))
Case conversion may be inaccurate. Consider using '#align finset.sup_apply Finset.sup_applyₓ'. -/
@[simp]
protected theorem sup_apply (s : Finset α) (f : α → ∀ b : β, C b) (b : β) :
    s.sup f b = s.sup fun a => f a b :=
  comp_sup_eq_sup_comp (fun x : ∀ b : β, C b => x b) (fun i j => rfl) rfl
#align finset.sup_apply Finset.sup_apply

end Sup

section Inf

variable {C : β → Type _} [∀ b : β, SemilatticeInf (C b)] [∀ b : β, OrderTop (C b)]

/- warning: finset.inf_apply -> Finset.inf_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {C : β -> Type.{u3}} [_inst_1 : forall (b : β), SemilatticeInf.{u3} (C b)] [_inst_2 : forall (b : β), OrderTop.{u3} (C b) (Preorder.toHasLe.{u3} (C b) (PartialOrder.toPreorder.{u3} (C b) (SemilatticeInf.toPartialOrder.{u3} (C b) (_inst_1 b))))] (s : Finset.{u1} α) (f : α -> (forall (b : β), C b)) (b : β), Eq.{succ u3} (C b) (Finset.inf.{max u2 u3, u1} (forall (b : β), C b) α (Pi.semilatticeInf.{u2, u3} β (fun (b : β) => C b) (fun (i : β) => _inst_1 i)) (Pi.orderTop.{u2, u3} β (fun (b : β) => C b) (fun (i : β) => Preorder.toHasLe.{u3} ((fun (i : β) => (fun (i : β) => (fun (i : β) => (fun (b : β) => C b) i) i) i) i) ((fun (i : β) => PartialOrder.toPreorder.{u3} ((fun (i : β) => (fun (b : β) => C b) i) i) ((fun (_x : β) => PartialOrder.mk.{u3} ((fun (i : β) => (fun (i : β) => (fun (b : β) => C b) i) i) _x) (SemilatticeInf.Le.{u3} ((fun (i : β) => (fun (i : β) => (fun (b : β) => C b) i) i) _x) ((fun (i : β) => _inst_1 i) _x)) (SemilatticeInf.Lt.{u3} ((fun (i : β) => (fun (i : β) => (fun (b : β) => C b) i) i) _x) ((fun (i : β) => _inst_1 i) _x)) (Pi.SemilatticeInf._proof_1.{u2, u3} β (fun (b : β) => C b) (fun (i : β) => _inst_1 i) _x) (Pi.SemilatticeInf._proof_2.{u2, u3} β (fun (b : β) => C b) (fun (i : β) => _inst_1 i) _x) (Pi.SemilatticeInf._proof_3.{u2, u3} β (fun (b : β) => C b) (fun (i : β) => _inst_1 i) _x) (Pi.SemilatticeInf._proof_4.{u2, u3} β (fun (b : β) => C b) (fun (i : β) => _inst_1 i) _x)) i)) i)) (fun (i : β) => _inst_2 i)) s f b) (Finset.inf.{u3, u1} (C b) α (_inst_1 b) (_inst_2 b) s (fun (a : α) => f a b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {C : β -> Type.{u3}} [_inst_1 : forall (b : β), SemilatticeInf.{u3} (C b)] [_inst_2 : forall (b : β), OrderTop.{u3} (C b) (Preorder.toLE.{u3} (C b) (PartialOrder.toPreorder.{u3} (C b) (SemilatticeInf.toPartialOrder.{u3} (C b) (_inst_1 b))))] (s : Finset.{u2} α) (f : α -> (forall (b : β), C b)) (b : β), Eq.{succ u3} (C b) (Finset.inf.{max u1 u3, u2} (forall (b : β), C b) α (Pi.semilatticeInf.{u1, u3} β (fun (b : β) => C b) (fun (i : β) => _inst_1 i)) (Pi.orderTop.{u1, u3} β (fun (b : β) => C b) (fun (i : β) => Preorder.toLE.{u3} ((fun (i : β) => (fun (i : β) => (fun (i : β) => C i) i) i) i) ((fun (i : β) => PartialOrder.toPreorder.{u3} ((fun (i : β) => (fun (b : β) => C b) i) i) ((fun (_x : β) => SemilatticeInf.toPartialOrder.{u3} ((fun (b : β) => C b) _x) ((fun (i : β) => _inst_1 i) _x)) i)) i)) (fun (i : β) => _inst_2 i)) s f b) (Finset.inf.{u3, u2} (C b) α (_inst_1 b) (_inst_2 b) s (fun (a : α) => f a b))
Case conversion may be inaccurate. Consider using '#align finset.inf_apply Finset.inf_applyₓ'. -/
@[simp]
protected theorem inf_apply (s : Finset α) (f : α → ∀ b : β, C b) (b : β) :
    s.inf f b = s.inf fun a => f a b :=
  @Finset.sup_apply _ _ (fun b => (C b)ᵒᵈ) _ _ s f b
#align finset.inf_apply Finset.inf_apply

end Inf

section Sup'

variable {C : β → Type _} [∀ b : β, SemilatticeSup (C b)]

/- warning: finset.sup'_apply -> Finset.sup'_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {C : β -> Type.{u3}} [_inst_1 : forall (b : β), SemilatticeSup.{u3} (C b)] {s : Finset.{u1} α} (H : Finset.Nonempty.{u1} α s) (f : α -> (forall (b : β), C b)) (b : β), Eq.{succ u3} (C b) (Finset.sup'.{max u2 u3, u1} (forall (b : β), C b) α (Pi.semilatticeSup.{u2, u3} β (fun (b : β) => C b) (fun (i : β) => _inst_1 i)) s H f b) (Finset.sup'.{u3, u1} (C b) α (_inst_1 b) s H (fun (a : α) => f a b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {C : β -> Type.{u3}} [_inst_1 : forall (b : β), SemilatticeSup.{u3} (C b)] {s : Finset.{u2} α} (H : Finset.Nonempty.{u2} α s) (f : α -> (forall (b : β), C b)) (b : β), Eq.{succ u3} (C b) (Finset.sup'.{max u1 u3, u2} (forall (b : β), C b) α (Pi.semilatticeSup.{u1, u3} β (fun (b : β) => C b) (fun (i : β) => _inst_1 i)) s H f b) (Finset.sup'.{u3, u2} (C b) α (_inst_1 b) s H (fun (a : α) => f a b))
Case conversion may be inaccurate. Consider using '#align finset.sup'_apply Finset.sup'_applyₓ'. -/
@[simp]
protected theorem sup'_apply {s : Finset α} (H : s.Nonempty) (f : α → ∀ b : β, C b) (b : β) :
    s.sup' H f b = s.sup' H fun a => f a b :=
  comp_sup'_eq_sup'_comp H (fun x : ∀ b : β, C b => x b) fun i j => rfl
#align finset.sup'_apply Finset.sup'_apply

end Sup'

section Inf'

variable {C : β → Type _} [∀ b : β, SemilatticeInf (C b)]

/- warning: finset.inf'_apply -> Finset.inf'_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {C : β -> Type.{u3}} [_inst_1 : forall (b : β), SemilatticeInf.{u3} (C b)] {s : Finset.{u1} α} (H : Finset.Nonempty.{u1} α s) (f : α -> (forall (b : β), C b)) (b : β), Eq.{succ u3} (C b) (Finset.inf'.{max u2 u3, u1} (forall (b : β), C b) α (Pi.semilatticeInf.{u2, u3} β (fun (b : β) => C b) (fun (i : β) => _inst_1 i)) s H f b) (Finset.inf'.{u3, u1} (C b) α (_inst_1 b) s H (fun (a : α) => f a b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {C : β -> Type.{u3}} [_inst_1 : forall (b : β), SemilatticeInf.{u3} (C b)] {s : Finset.{u2} α} (H : Finset.Nonempty.{u2} α s) (f : α -> (forall (b : β), C b)) (b : β), Eq.{succ u3} (C b) (Finset.inf'.{max u1 u3, u2} (forall (b : β), C b) α (Pi.semilatticeInf.{u1, u3} β (fun (b : β) => C b) (fun (i : β) => _inst_1 i)) s H f b) (Finset.inf'.{u3, u2} (C b) α (_inst_1 b) s H (fun (a : α) => f a b))
Case conversion may be inaccurate. Consider using '#align finset.inf'_apply Finset.inf'_applyₓ'. -/
@[simp]
protected theorem inf'_apply {s : Finset α} (H : s.Nonempty) (f : α → ∀ b : β, C b) (b : β) :
    s.inf' H f b = s.inf' H fun a => f a b :=
  @Finset.sup'_apply _ _ (fun b => (C b)ᵒᵈ) _ _ H f b
#align finset.inf'_apply Finset.inf'_apply

end Inf'

/- warning: finset.to_dual_sup' -> Finset.toDual_sup' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] {s : Finset.{u2} ι} (hs : Finset.Nonempty.{u2} ι s) (f : ι -> α), Eq.{succ u1} (OrderDual.{u1} α) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) => α -> (OrderDual.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (OrderDual.{u1} α)) (OrderDual.toDual.{u1} α) (Finset.sup'.{u1, u2} α ι _inst_1 s hs f)) (Finset.inf'.{u1, u2} (OrderDual.{u1} α) ι (OrderDual.semilatticeInf.{u1} α _inst_1) s hs (Function.comp.{succ u2, succ u1, succ u1} ι α (OrderDual.{u1} α) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) => α -> (OrderDual.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (OrderDual.{u1} α)) (OrderDual.toDual.{u1} α)) f))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : SemilatticeSup.{u2} α] {s : Finset.{u1} ι} (hs : Finset.Nonempty.{u1} ι s) (f : ι -> α), Eq.{succ u2} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => OrderDual.{u2} α) (Finset.sup'.{u2, u1} α ι _inst_1 s hs f)) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => OrderDual.{u2} α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α) (Finset.sup'.{u2, u1} α ι _inst_1 s hs f)) (Finset.inf'.{u2, u1} (OrderDual.{u2} α) ι (OrderDual.semilatticeInf.{u2} α _inst_1) s hs (Function.comp.{succ u1, succ u2, succ u2} ι α (OrderDual.{u2} α) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => OrderDual.{u2} α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α)) f))
Case conversion may be inaccurate. Consider using '#align finset.to_dual_sup' Finset.toDual_sup'ₓ'. -/
@[simp]
theorem toDual_sup' [SemilatticeSup α] {s : Finset ι} (hs : s.Nonempty) (f : ι → α) :
    toDual (s.sup' hs f) = s.inf' hs (toDual ∘ f) :=
  rfl
#align finset.to_dual_sup' Finset.toDual_sup'

/- warning: finset.to_dual_inf' -> Finset.toDual_inf' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] {s : Finset.{u2} ι} (hs : Finset.Nonempty.{u2} ι s) (f : ι -> α), Eq.{succ u1} (OrderDual.{u1} α) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) => α -> (OrderDual.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (OrderDual.{u1} α)) (OrderDual.toDual.{u1} α) (Finset.inf'.{u1, u2} α ι _inst_1 s hs f)) (Finset.sup'.{u1, u2} (OrderDual.{u1} α) ι (OrderDual.semilatticeSup.{u1} α _inst_1) s hs (Function.comp.{succ u2, succ u1, succ u1} ι α (OrderDual.{u1} α) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) => α -> (OrderDual.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (OrderDual.{u1} α)) (OrderDual.toDual.{u1} α)) f))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : SemilatticeInf.{u2} α] {s : Finset.{u1} ι} (hs : Finset.Nonempty.{u1} ι s) (f : ι -> α), Eq.{succ u2} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => OrderDual.{u2} α) (Finset.inf'.{u2, u1} α ι _inst_1 s hs f)) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => OrderDual.{u2} α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α) (Finset.inf'.{u2, u1} α ι _inst_1 s hs f)) (Finset.sup'.{u2, u1} (OrderDual.{u2} α) ι (OrderDual.semilatticeSup.{u2} α _inst_1) s hs (Function.comp.{succ u1, succ u2, succ u2} ι α (OrderDual.{u2} α) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => OrderDual.{u2} α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α)) f))
Case conversion may be inaccurate. Consider using '#align finset.to_dual_inf' Finset.toDual_inf'ₓ'. -/
@[simp]
theorem toDual_inf' [SemilatticeInf α] {s : Finset ι} (hs : s.Nonempty) (f : ι → α) :
    toDual (s.inf' hs f) = s.sup' hs (toDual ∘ f) :=
  rfl
#align finset.to_dual_inf' Finset.toDual_inf'

/- warning: finset.of_dual_sup' -> Finset.ofDual_sup' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] {s : Finset.{u2} ι} (hs : Finset.Nonempty.{u2} ι s) (f : ι -> (OrderDual.{u1} α)), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) => (OrderDual.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.ofDual.{u1} α) (Finset.sup'.{u1, u2} (OrderDual.{u1} α) ι (OrderDual.semilatticeSup.{u1} α _inst_1) s hs f)) (Finset.inf'.{u1, u2} α ι _inst_1 s hs (Function.comp.{succ u2, succ u1, succ u1} ι (OrderDual.{u1} α) α (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) => (OrderDual.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.ofDual.{u1} α)) f))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : SemilatticeInf.{u2} α] {s : Finset.{u1} ι} (hs : Finset.Nonempty.{u1} ι s) (f : ι -> (OrderDual.{u2} α)), Eq.{succ u2} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : OrderDual.{u2} α) => α) (Finset.sup'.{u2, u1} (OrderDual.{u2} α) ι (OrderDual.semilatticeSup.{u2} α _inst_1) s hs f)) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.{u2} α) (fun (_x : OrderDual.{u2} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : OrderDual.{u2} α) => α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.ofDual.{u2} α) (Finset.sup'.{u2, u1} (OrderDual.{u2} α) ι (OrderDual.semilatticeSup.{u2} α _inst_1) s hs f)) (Finset.inf'.{u2, u1} α ι _inst_1 s hs (Function.comp.{succ u1, succ u2, succ u2} ι (OrderDual.{u2} α) α (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.{u2} α) (fun (_x : OrderDual.{u2} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : OrderDual.{u2} α) => α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.ofDual.{u2} α)) f))
Case conversion may be inaccurate. Consider using '#align finset.of_dual_sup' Finset.ofDual_sup'ₓ'. -/
@[simp]
theorem ofDual_sup' [SemilatticeInf α] {s : Finset ι} (hs : s.Nonempty) (f : ι → αᵒᵈ) :
    ofDual (s.sup' hs f) = s.inf' hs (ofDual ∘ f) :=
  rfl
#align finset.of_dual_sup' Finset.ofDual_sup'

/- warning: finset.of_dual_inf' -> Finset.ofDual_inf' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] {s : Finset.{u2} ι} (hs : Finset.Nonempty.{u2} ι s) (f : ι -> (OrderDual.{u1} α)), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) => (OrderDual.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.ofDual.{u1} α) (Finset.inf'.{u1, u2} (OrderDual.{u1} α) ι (OrderDual.semilatticeInf.{u1} α _inst_1) s hs f)) (Finset.sup'.{u1, u2} α ι _inst_1 s hs (Function.comp.{succ u2, succ u1, succ u1} ι (OrderDual.{u1} α) α (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) => (OrderDual.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.ofDual.{u1} α)) f))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : SemilatticeSup.{u2} α] {s : Finset.{u1} ι} (hs : Finset.Nonempty.{u1} ι s) (f : ι -> (OrderDual.{u2} α)), Eq.{succ u2} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : OrderDual.{u2} α) => α) (Finset.inf'.{u2, u1} (OrderDual.{u2} α) ι (OrderDual.semilatticeInf.{u2} α _inst_1) s hs f)) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.{u2} α) (fun (_x : OrderDual.{u2} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : OrderDual.{u2} α) => α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.ofDual.{u2} α) (Finset.inf'.{u2, u1} (OrderDual.{u2} α) ι (OrderDual.semilatticeInf.{u2} α _inst_1) s hs f)) (Finset.sup'.{u2, u1} α ι _inst_1 s hs (Function.comp.{succ u1, succ u2, succ u2} ι (OrderDual.{u2} α) α (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.{u2} α) (fun (_x : OrderDual.{u2} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : OrderDual.{u2} α) => α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.ofDual.{u2} α)) f))
Case conversion may be inaccurate. Consider using '#align finset.of_dual_inf' Finset.ofDual_inf'ₓ'. -/
@[simp]
theorem ofDual_inf' [SemilatticeSup α] {s : Finset ι} (hs : s.Nonempty) (f : ι → αᵒᵈ) :
    ofDual (s.inf' hs f) = s.sup' hs (ofDual ∘ f) :=
  rfl
#align finset.of_dual_inf' Finset.ofDual_inf'

section LinearOrder

variable [LinearOrder α] {s : Finset ι} (H : s.Nonempty) {f : ι → α} {a : α}

/- warning: finset.le_sup'_iff -> Finset.le_sup'_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] {s : Finset.{u2} ι} (H : Finset.Nonempty.{u2} ι s) {f : ι -> α} {a : α}, Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a (Finset.sup'.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)) s H f)) (Exists.{succ u2} ι (fun (b : ι) => Exists.{0} (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) b s) (fun (H : Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) b s) => LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a (f b))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] {s : Finset.{u1} ι} (H : Finset.Nonempty.{u1} ι s) {f : ι -> α} {a : α}, Iff (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) a (Finset.sup'.{u2, u1} α ι (Lattice.toSemilatticeSup.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))) s H f)) (Exists.{succ u1} ι (fun (b : ι) => And (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) b s) (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) a (f b))))
Case conversion may be inaccurate. Consider using '#align finset.le_sup'_iff Finset.le_sup'_iffₓ'. -/
@[simp]
theorem le_sup'_iff : a ≤ s.sup' H f ↔ ∃ b ∈ s, a ≤ f b :=
  by
  rw [← WithBot.coe_le_coe, coe_sup', Finset.le_sup_iff (WithBot.bot_lt_coe a)]
  exact bex_congr fun b hb => WithBot.coe_le_coe
#align finset.le_sup'_iff Finset.le_sup'_iff

/- warning: finset.lt_sup'_iff -> Finset.lt_sup'_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] {s : Finset.{u2} ι} (H : Finset.Nonempty.{u2} ι s) {f : ι -> α} {a : α}, Iff (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a (Finset.sup'.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)) s H f)) (Exists.{succ u2} ι (fun (b : ι) => Exists.{0} (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) b s) (fun (H : Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) b s) => LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a (f b))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] {s : Finset.{u1} ι} (H : Finset.Nonempty.{u1} ι s) {f : ι -> α} {a : α}, Iff (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) a (Finset.sup'.{u2, u1} α ι (Lattice.toSemilatticeSup.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))) s H f)) (Exists.{succ u1} ι (fun (b : ι) => And (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) b s) (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) a (f b))))
Case conversion may be inaccurate. Consider using '#align finset.lt_sup'_iff Finset.lt_sup'_iffₓ'. -/
@[simp]
theorem lt_sup'_iff : a < s.sup' H f ↔ ∃ b ∈ s, a < f b :=
  by
  rw [← WithBot.coe_lt_coe, coe_sup', Finset.lt_sup_iff]
  exact bex_congr fun b hb => WithBot.coe_lt_coe
#align finset.lt_sup'_iff Finset.lt_sup'_iff

/- warning: finset.sup'_lt_iff -> Finset.sup'_lt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] {s : Finset.{u2} ι} (H : Finset.Nonempty.{u2} ι s) {f : ι -> α} {a : α}, Iff (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (Finset.sup'.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)) s H f) a) (forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (f i) a))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] {s : Finset.{u1} ι} (H : Finset.Nonempty.{u1} ι s) {f : ι -> α} {a : α}, Iff (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) (Finset.sup'.{u2, u1} α ι (Lattice.toSemilatticeSup.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))) s H f) a) (forall (i : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) -> (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) (f i) a))
Case conversion may be inaccurate. Consider using '#align finset.sup'_lt_iff Finset.sup'_lt_iffₓ'. -/
@[simp]
theorem sup'_lt_iff : s.sup' H f < a ↔ ∀ i ∈ s, f i < a :=
  by
  rw [← WithBot.coe_lt_coe, coe_sup', Finset.sup_lt_iff (WithBot.bot_lt_coe a)]
  exact ball_congr fun b hb => WithBot.coe_lt_coe
#align finset.sup'_lt_iff Finset.sup'_lt_iff

/- warning: finset.inf'_le_iff -> Finset.inf'_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] {s : Finset.{u2} ι} (H : Finset.Nonempty.{u2} ι s) {f : ι -> α} {a : α}, Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (Finset.inf'.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)) s H f) a) (Exists.{succ u2} ι (fun (i : ι) => Exists.{0} (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) => LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (f i) a)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] {s : Finset.{u1} ι} (H : Finset.Nonempty.{u1} ι s) {f : ι -> α} {a : α}, Iff (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) (Finset.inf'.{u2, u1} α ι (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))) s H f) a) (Exists.{succ u1} ι (fun (i : ι) => And (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) (f i) a)))
Case conversion may be inaccurate. Consider using '#align finset.inf'_le_iff Finset.inf'_le_iffₓ'. -/
@[simp]
theorem inf'_le_iff : s.inf' H f ≤ a ↔ ∃ i ∈ s, f i ≤ a :=
  @le_sup'_iff αᵒᵈ _ _ _ H f _
#align finset.inf'_le_iff Finset.inf'_le_iff

/- warning: finset.inf'_lt_iff -> Finset.inf'_lt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] {s : Finset.{u2} ι} (H : Finset.Nonempty.{u2} ι s) {f : ι -> α} {a : α}, Iff (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (Finset.inf'.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)) s H f) a) (Exists.{succ u2} ι (fun (i : ι) => Exists.{0} (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) => LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (f i) a)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] {s : Finset.{u1} ι} (H : Finset.Nonempty.{u1} ι s) {f : ι -> α} {a : α}, Iff (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) (Finset.inf'.{u2, u1} α ι (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))) s H f) a) (Exists.{succ u1} ι (fun (i : ι) => And (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) (f i) a)))
Case conversion may be inaccurate. Consider using '#align finset.inf'_lt_iff Finset.inf'_lt_iffₓ'. -/
@[simp]
theorem inf'_lt_iff : s.inf' H f < a ↔ ∃ i ∈ s, f i < a :=
  @lt_sup'_iff αᵒᵈ _ _ _ H f _
#align finset.inf'_lt_iff Finset.inf'_lt_iff

/- warning: finset.lt_inf'_iff -> Finset.lt_inf'_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] {s : Finset.{u2} ι} (H : Finset.Nonempty.{u2} ι s) {f : ι -> α} {a : α}, Iff (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a (Finset.inf'.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)) s H f)) (forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a (f i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] {s : Finset.{u1} ι} (H : Finset.Nonempty.{u1} ι s) {f : ι -> α} {a : α}, Iff (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) a (Finset.inf'.{u2, u1} α ι (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))) s H f)) (forall (i : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) -> (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) a (f i)))
Case conversion may be inaccurate. Consider using '#align finset.lt_inf'_iff Finset.lt_inf'_iffₓ'. -/
@[simp]
theorem lt_inf'_iff : a < s.inf' H f ↔ ∀ i ∈ s, a < f i :=
  @sup'_lt_iff αᵒᵈ _ _ _ H f _
#align finset.lt_inf'_iff Finset.lt_inf'_iff

#print Finset.exists_mem_eq_sup' /-
theorem exists_mem_eq_sup' (f : ι → α) : ∃ i, i ∈ s ∧ s.sup' H f = f i :=
  by
  refine' H.cons_induction (fun c => _) fun c s hc hs ih => _
  · exact ⟨c, mem_singleton_self c, rfl⟩
  · rcases ih with ⟨b, hb, h'⟩
    rw [sup'_cons hs, h']
    cases' total_of (· ≤ ·) (f b) (f c) with h h
    · exact ⟨c, mem_cons.2 (Or.inl rfl), sup_eq_left.2 h⟩
    · exact ⟨b, mem_cons.2 (Or.inr hb), sup_eq_right.2 h⟩
#align finset.exists_mem_eq_sup' Finset.exists_mem_eq_sup'
-/

#print Finset.exists_mem_eq_inf' /-
theorem exists_mem_eq_inf' (f : ι → α) : ∃ i, i ∈ s ∧ s.inf' H f = f i :=
  @exists_mem_eq_sup' αᵒᵈ _ _ _ H f
#align finset.exists_mem_eq_inf' Finset.exists_mem_eq_inf'
-/

/- warning: finset.exists_mem_eq_sup -> Finset.exists_mem_eq_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))] (s : Finset.{u2} ι), (Finset.Nonempty.{u2} ι s) -> (forall (f : ι -> α), Exists.{succ u2} ι (fun (i : ι) => And (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) (Eq.{succ u1} α (Finset.sup.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)) _inst_2 s f) (f i))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))))] (s : Finset.{u1} ι), (Finset.Nonempty.{u1} ι s) -> (forall (f : ι -> α), Exists.{succ u1} ι (fun (i : ι) => And (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) (Eq.{succ u2} α (Finset.sup.{u2, u1} α ι (Lattice.toSemilatticeSup.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))) _inst_2 s f) (f i))))
Case conversion may be inaccurate. Consider using '#align finset.exists_mem_eq_sup Finset.exists_mem_eq_supₓ'. -/
theorem exists_mem_eq_sup [OrderBot α] (s : Finset ι) (h : s.Nonempty) (f : ι → α) :
    ∃ i, i ∈ s ∧ s.sup f = f i :=
  sup'_eq_sup h f ▸ exists_mem_eq_sup' h f
#align finset.exists_mem_eq_sup Finset.exists_mem_eq_sup

/- warning: finset.exists_mem_eq_inf -> Finset.exists_mem_eq_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))] (s : Finset.{u2} ι), (Finset.Nonempty.{u2} ι s) -> (forall (f : ι -> α), Exists.{succ u2} ι (fun (i : ι) => And (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) (Eq.{succ u1} α (Finset.inf.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)) _inst_2 s f) (f i))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] [_inst_2 : OrderTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))))] (s : Finset.{u1} ι), (Finset.Nonempty.{u1} ι s) -> (forall (f : ι -> α), Exists.{succ u1} ι (fun (i : ι) => And (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) (Eq.{succ u2} α (Finset.inf.{u2, u1} α ι (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))) _inst_2 s f) (f i))))
Case conversion may be inaccurate. Consider using '#align finset.exists_mem_eq_inf Finset.exists_mem_eq_infₓ'. -/
theorem exists_mem_eq_inf [OrderTop α] (s : Finset ι) (h : s.Nonempty) (f : ι → α) :
    ∃ i, i ∈ s ∧ s.inf f = f i :=
  @exists_mem_eq_sup αᵒᵈ _ _ _ _ h f
#align finset.exists_mem_eq_inf Finset.exists_mem_eq_inf

end LinearOrder

/-! ### max and min of finite sets -/


section MaxMin

variable [LinearOrder α]

#print Finset.max /-
/-- Let `s` be a finset in a linear order. Then `s.max` is the maximum of `s` if `s` is not empty,
and `⊥` otherwise. It belongs to `with_bot α`. If you want to get an element of `α`, see
`s.max'`. -/
protected def max (s : Finset α) : WithBot α :=
  sup s coe
#align finset.max Finset.max
-/

#print Finset.max_eq_sup_coe /-
theorem max_eq_sup_coe {s : Finset α} : s.max = s.sup coe :=
  rfl
#align finset.max_eq_sup_coe Finset.max_eq_sup_coe
-/

#print Finset.max_eq_sup_withBot /-
theorem max_eq_sup_withBot (s : Finset α) : s.max = sup s coe :=
  rfl
#align finset.max_eq_sup_with_bot Finset.max_eq_sup_withBot
-/

#print Finset.max_empty /-
@[simp]
theorem max_empty : (∅ : Finset α).max = ⊥ :=
  rfl
#align finset.max_empty Finset.max_empty
-/

/- warning: finset.max_insert -> Finset.max_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {s : Finset.{u1} α}, Eq.{succ u1} (WithBot.{u1} α) (Finset.max.{u1} α _inst_1 (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => Eq.decidable.{u1} α _inst_1 a b)) a s)) (LinearOrder.max.{u1} (WithBot.{u1} α) (WithBot.linearOrder.{u1} α _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) a) (Finset.max.{u1} α _inst_1 s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {s : Finset.{u1} α}, Eq.{succ u1} (WithBot.{u1} α) (Finset.max.{u1} α _inst_1 (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => instDecidableEq.{u1} α _inst_1 a b)) a s)) (Max.max.{u1} (WithBot.{u1} α) (LinearOrder.toMax.{u1} (WithBot.{u1} α) (WithBot.linearOrder.{u1} α _inst_1)) (WithBot.some.{u1} α a) (Finset.max.{u1} α _inst_1 s))
Case conversion may be inaccurate. Consider using '#align finset.max_insert Finset.max_insertₓ'. -/
@[simp]
theorem max_insert {a : α} {s : Finset α} : (insert a s).max = max a s.max :=
  fold_insert_idem
#align finset.max_insert Finset.max_insert

#print Finset.max_singleton /-
@[simp]
theorem max_singleton {a : α} : Finset.max {a} = (a : WithBot α) :=
  by
  rw [← insert_emptyc_eq]
  exact max_insert
#align finset.max_singleton Finset.max_singleton
-/

#print Finset.max_of_mem /-
theorem max_of_mem {s : Finset α} {a : α} (h : a ∈ s) : ∃ b : α, s.max = b :=
  (@le_sup (WithBot α) _ _ _ _ _ _ h _ rfl).imp fun b => Exists.fst
#align finset.max_of_mem Finset.max_of_mem
-/

#print Finset.max_of_nonempty /-
theorem max_of_nonempty {s : Finset α} (h : s.Nonempty) : ∃ a : α, s.max = a :=
  let ⟨a, ha⟩ := h
  max_of_mem ha
#align finset.max_of_nonempty Finset.max_of_nonempty
-/

#print Finset.max_eq_bot /-
theorem max_eq_bot {s : Finset α} : s.max = ⊥ ↔ s = ∅ :=
  ⟨fun h =>
    s.eq_empty_or_nonempty.elim id fun H =>
      by
      let ⟨a, ha⟩ := max_of_nonempty H
      rw [h] at ha <;> cases ha,
    fun h => h.symm ▸ max_empty⟩
#align finset.max_eq_bot Finset.max_eq_bot
-/

#print Finset.mem_of_max /-
theorem mem_of_max {s : Finset α} : ∀ {a : α}, s.max = a → a ∈ s :=
  Finset.induction_on s (fun _ H => by cases H)
    fun b s _ (ih : ∀ {a : α}, s.max = a → a ∈ s) a (h : (insert b s).max = a) =>
    by
    by_cases p : b = a
    · induction p
      exact mem_insert_self b s
    · cases' max_choice (↑b) s.max with q q <;> rw [max_insert, q] at h
      · cases h
        cases p rfl
      · exact mem_insert_of_mem (ih h)
#align finset.mem_of_max Finset.mem_of_max
-/

/- warning: finset.le_max -> Finset.le_max is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {s : Finset.{u1} α}, (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (LE.le.{u1} (WithBot.{u1} α) (Preorder.toHasLe.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) a) (Finset.max.{u1} α _inst_1 s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {s : Finset.{u1} α}, (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (LE.le.{u1} (WithBot.{u1} α) (Preorder.toLE.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))))) (WithBot.some.{u1} α a) (Finset.max.{u1} α _inst_1 s))
Case conversion may be inaccurate. Consider using '#align finset.le_max Finset.le_maxₓ'. -/
theorem le_max {a : α} {s : Finset α} (as : a ∈ s) : ↑a ≤ s.max :=
  le_sup as
#align finset.le_max Finset.le_max

/- warning: finset.not_mem_of_max_lt_coe -> Finset.not_mem_of_max_lt_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {s : Finset.{u1} α}, (LT.lt.{u1} (WithBot.{u1} α) (Preorder.toHasLt.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) (Finset.max.{u1} α _inst_1 s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) a)) -> (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {s : Finset.{u1} α}, (LT.lt.{u1} (WithBot.{u1} α) (Preorder.toLT.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))))) (Finset.max.{u1} α _inst_1 s) (WithBot.some.{u1} α a)) -> (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s))
Case conversion may be inaccurate. Consider using '#align finset.not_mem_of_max_lt_coe Finset.not_mem_of_max_lt_coeₓ'. -/
theorem not_mem_of_max_lt_coe {a : α} {s : Finset α} (h : s.max < a) : a ∉ s :=
  mt le_max h.not_le
#align finset.not_mem_of_max_lt_coe Finset.not_mem_of_max_lt_coe

/- warning: finset.le_max_of_eq -> Finset.le_max_of_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {s : Finset.{u1} α} {a : α} {b : α}, (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (Eq.{succ u1} (WithBot.{u1} α) (Finset.max.{u1} α _inst_1 s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) b)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {s : Finset.{u1} α} {a : α} {b : α}, (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (Eq.{succ u1} (WithBot.{u1} α) (Finset.max.{u1} α _inst_1 s) (WithBot.some.{u1} α b)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) a b)
Case conversion may be inaccurate. Consider using '#align finset.le_max_of_eq Finset.le_max_of_eqₓ'. -/
theorem le_max_of_eq {s : Finset α} {a b : α} (h₁ : a ∈ s) (h₂ : s.max = b) : a ≤ b :=
  WithBot.coe_le_coe.mp <| (le_max h₁).trans h₂.le
#align finset.le_max_of_eq Finset.le_max_of_eq

/- warning: finset.not_mem_of_max_lt -> Finset.not_mem_of_max_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {s : Finset.{u1} α} {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) b a) -> (Eq.{succ u1} (WithBot.{u1} α) (Finset.max.{u1} α _inst_1 s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) b)) -> (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {s : Finset.{u1} α} {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) b a) -> (Eq.{succ u1} (WithBot.{u1} α) (Finset.max.{u1} α _inst_1 s) (WithBot.some.{u1} α b)) -> (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s))
Case conversion may be inaccurate. Consider using '#align finset.not_mem_of_max_lt Finset.not_mem_of_max_ltₓ'. -/
theorem not_mem_of_max_lt {s : Finset α} {a b : α} (h₁ : b < a) (h₂ : s.max = ↑b) : a ∉ s :=
  Finset.not_mem_of_max_lt_coe <| h₂.trans_lt <| WithBot.coe_lt_coe.mpr h₁
#align finset.not_mem_of_max_lt Finset.not_mem_of_max_lt

/- warning: finset.max_mono -> Finset.max_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s t) -> (LE.le.{u1} (WithBot.{u1} α) (Preorder.toHasLe.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) (Finset.max.{u1} α _inst_1 s) (Finset.max.{u1} α _inst_1 t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) s t) -> (LE.le.{u1} (WithBot.{u1} α) (Preorder.toLE.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))))) (Finset.max.{u1} α _inst_1 s) (Finset.max.{u1} α _inst_1 t))
Case conversion may be inaccurate. Consider using '#align finset.max_mono Finset.max_monoₓ'. -/
theorem max_mono {s t : Finset α} (st : s ⊆ t) : s.max ≤ t.max :=
  sup_mono st
#align finset.max_mono Finset.max_mono

/- warning: finset.max_le -> Finset.max_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {M : WithBot.{u1} α} {s : Finset.{u1} α}, (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (LE.le.{u1} (WithBot.{u1} α) (Preorder.toHasLe.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) a) M)) -> (LE.le.{u1} (WithBot.{u1} α) (Preorder.toHasLe.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) (Finset.max.{u1} α _inst_1 s) M)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {M : WithBot.{u1} α} {s : Finset.{u1} α}, (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (LE.le.{u1} (WithBot.{u1} α) (Preorder.toLE.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))))) (WithBot.some.{u1} α a) M)) -> (LE.le.{u1} (WithBot.{u1} α) (Preorder.toLE.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))))) (Finset.max.{u1} α _inst_1 s) M)
Case conversion may be inaccurate. Consider using '#align finset.max_le Finset.max_leₓ'. -/
protected theorem max_le {M : WithBot α} {s : Finset α} (st : ∀ a ∈ s, (a : WithBot α) ≤ M) :
    s.max ≤ M :=
  Finset.sup_le st
#align finset.max_le Finset.max_le

#print Finset.min /-
/-- Let `s` be a finset in a linear order. Then `s.min` is the minimum of `s` if `s` is not empty,
and `⊤` otherwise. It belongs to `with_top α`. If you want to get an element of `α`, see
`s.min'`. -/
protected def min (s : Finset α) : WithTop α :=
  inf s coe
#align finset.min Finset.min
-/

#print Finset.min_eq_inf_withTop /-
theorem min_eq_inf_withTop (s : Finset α) : s.min = inf s coe :=
  rfl
#align finset.min_eq_inf_with_top Finset.min_eq_inf_withTop
-/

#print Finset.min_empty /-
@[simp]
theorem min_empty : (∅ : Finset α).min = ⊤ :=
  rfl
#align finset.min_empty Finset.min_empty
-/

/- warning: finset.min_insert -> Finset.min_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {s : Finset.{u1} α}, Eq.{succ u1} (WithTop.{u1} α) (Finset.min.{u1} α _inst_1 (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => Eq.decidable.{u1} α _inst_1 a b)) a s)) (LinearOrder.min.{u1} (WithTop.{u1} α) (WithTop.linearOrder.{u1} α _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) a) (Finset.min.{u1} α _inst_1 s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {s : Finset.{u1} α}, Eq.{succ u1} (WithTop.{u1} α) (Finset.min.{u1} α _inst_1 (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => instDecidableEq.{u1} α _inst_1 a b)) a s)) (Min.min.{u1} (WithTop.{u1} α) (LinearOrder.toMin.{u1} (WithTop.{u1} α) (WithTop.linearOrder.{u1} α _inst_1)) (WithTop.some.{u1} α a) (Finset.min.{u1} α _inst_1 s))
Case conversion may be inaccurate. Consider using '#align finset.min_insert Finset.min_insertₓ'. -/
@[simp]
theorem min_insert {a : α} {s : Finset α} : (insert a s).min = min (↑a) s.min :=
  fold_insert_idem
#align finset.min_insert Finset.min_insert

#print Finset.min_singleton /-
@[simp]
theorem min_singleton {a : α} : Finset.min {a} = (a : WithTop α) :=
  by
  rw [← insert_emptyc_eq]
  exact min_insert
#align finset.min_singleton Finset.min_singleton
-/

#print Finset.min_of_mem /-
theorem min_of_mem {s : Finset α} {a : α} (h : a ∈ s) : ∃ b : α, s.min = b :=
  (@inf_le (WithTop α) _ _ _ _ _ _ h _ rfl).imp fun b => Exists.fst
#align finset.min_of_mem Finset.min_of_mem
-/

#print Finset.min_of_nonempty /-
theorem min_of_nonempty {s : Finset α} (h : s.Nonempty) : ∃ a : α, s.min = a :=
  let ⟨a, ha⟩ := h
  min_of_mem ha
#align finset.min_of_nonempty Finset.min_of_nonempty
-/

#print Finset.min_eq_top /-
theorem min_eq_top {s : Finset α} : s.min = ⊤ ↔ s = ∅ :=
  ⟨fun h =>
    s.eq_empty_or_nonempty.elim id fun H =>
      by
      let ⟨a, ha⟩ := min_of_nonempty H
      rw [h] at ha <;> cases ha,
    fun h => h.symm ▸ min_empty⟩
#align finset.min_eq_top Finset.min_eq_top
-/

#print Finset.mem_of_min /-
theorem mem_of_min {s : Finset α} : ∀ {a : α}, s.min = a → a ∈ s :=
  @mem_of_max αᵒᵈ _ s
#align finset.mem_of_min Finset.mem_of_min
-/

/- warning: finset.min_le -> Finset.min_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {s : Finset.{u1} α}, (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (LE.le.{u1} (WithTop.{u1} α) (Preorder.toHasLe.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) (Finset.min.{u1} α _inst_1 s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {s : Finset.{u1} α}, (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (LE.le.{u1} (WithTop.{u1} α) (Preorder.toLE.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))))) (Finset.min.{u1} α _inst_1 s) (WithTop.some.{u1} α a))
Case conversion may be inaccurate. Consider using '#align finset.min_le Finset.min_leₓ'. -/
theorem min_le {a : α} {s : Finset α} (as : a ∈ s) : s.min ≤ a :=
  inf_le as
#align finset.min_le Finset.min_le

/- warning: finset.not_mem_of_coe_lt_min -> Finset.not_mem_of_coe_lt_min is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {s : Finset.{u1} α}, (LT.lt.{u1} (WithTop.{u1} α) (Preorder.toHasLt.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) a) (Finset.min.{u1} α _inst_1 s)) -> (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {s : Finset.{u1} α}, (LT.lt.{u1} (WithTop.{u1} α) (Preorder.toLT.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))))) (WithTop.some.{u1} α a) (Finset.min.{u1} α _inst_1 s)) -> (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s))
Case conversion may be inaccurate. Consider using '#align finset.not_mem_of_coe_lt_min Finset.not_mem_of_coe_lt_minₓ'. -/
theorem not_mem_of_coe_lt_min {a : α} {s : Finset α} (h : ↑a < s.min) : a ∉ s :=
  mt min_le h.not_le
#align finset.not_mem_of_coe_lt_min Finset.not_mem_of_coe_lt_min

/- warning: finset.min_le_of_eq -> Finset.min_le_of_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {s : Finset.{u1} α} {a : α} {b : α}, (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) b s) -> (Eq.{succ u1} (WithTop.{u1} α) (Finset.min.{u1} α _inst_1 s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) a)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {s : Finset.{u1} α} {a : α} {b : α}, (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) b s) -> (Eq.{succ u1} (WithTop.{u1} α) (Finset.min.{u1} α _inst_1 s) (WithTop.some.{u1} α a)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) a b)
Case conversion may be inaccurate. Consider using '#align finset.min_le_of_eq Finset.min_le_of_eqₓ'. -/
theorem min_le_of_eq {s : Finset α} {a b : α} (h₁ : b ∈ s) (h₂ : s.min = a) : a ≤ b :=
  WithTop.coe_le_coe.mp <| h₂.ge.trans (min_le h₁)
#align finset.min_le_of_eq Finset.min_le_of_eq

/- warning: finset.not_mem_of_lt_min -> Finset.not_mem_of_lt_min is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {s : Finset.{u1} α} {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a b) -> (Eq.{succ u1} (WithTop.{u1} α) (Finset.min.{u1} α _inst_1 s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) b)) -> (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {s : Finset.{u1} α} {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) a b) -> (Eq.{succ u1} (WithTop.{u1} α) (Finset.min.{u1} α _inst_1 s) (WithTop.some.{u1} α b)) -> (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s))
Case conversion may be inaccurate. Consider using '#align finset.not_mem_of_lt_min Finset.not_mem_of_lt_minₓ'. -/
theorem not_mem_of_lt_min {s : Finset α} {a b : α} (h₁ : a < b) (h₂ : s.min = ↑b) : a ∉ s :=
  Finset.not_mem_of_coe_lt_min <| (WithTop.coe_lt_coe.mpr h₁).trans_eq h₂.symm
#align finset.not_mem_of_lt_min Finset.not_mem_of_lt_min

/- warning: finset.min_mono -> Finset.min_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s t) -> (LE.le.{u1} (WithTop.{u1} α) (Preorder.toHasLe.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) (Finset.min.{u1} α _inst_1 t) (Finset.min.{u1} α _inst_1 s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) s t) -> (LE.le.{u1} (WithTop.{u1} α) (Preorder.toLE.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))))) (Finset.min.{u1} α _inst_1 t) (Finset.min.{u1} α _inst_1 s))
Case conversion may be inaccurate. Consider using '#align finset.min_mono Finset.min_monoₓ'. -/
theorem min_mono {s t : Finset α} (st : s ⊆ t) : t.min ≤ s.min :=
  inf_mono st
#align finset.min_mono Finset.min_mono

/- warning: finset.le_min -> Finset.le_min is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {m : WithTop.{u1} α} {s : Finset.{u1} α}, (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (LE.le.{u1} (WithTop.{u1} α) (Preorder.toHasLe.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) m ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) a))) -> (LE.le.{u1} (WithTop.{u1} α) (Preorder.toHasLe.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) m (Finset.min.{u1} α _inst_1 s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {m : WithTop.{u1} α} {s : Finset.{u1} α}, (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (LE.le.{u1} (WithTop.{u1} α) (Preorder.toLE.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))))) m (WithTop.some.{u1} α a))) -> (LE.le.{u1} (WithTop.{u1} α) (Preorder.toLE.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))))) m (Finset.min.{u1} α _inst_1 s))
Case conversion may be inaccurate. Consider using '#align finset.le_min Finset.le_minₓ'. -/
protected theorem le_min {m : WithTop α} {s : Finset α} (st : ∀ a : α, a ∈ s → m ≤ a) : m ≤ s.min :=
  Finset.le_inf st
#align finset.le_min Finset.le_min

#print Finset.min' /-
/-- Given a nonempty finset `s` in a linear order `α`, then `s.min' h` is its minimum, as an
element of `α`, where `h` is a proof of nonemptiness. Without this assumption, use instead `s.min`,
taking values in `with_top α`. -/
def min' (s : Finset α) (H : s.Nonempty) : α :=
  inf' s H id
#align finset.min' Finset.min'
-/

#print Finset.max' /-
/-- Given a nonempty finset `s` in a linear order `α`, then `s.max' h` is its maximum, as an
element of `α`, where `h` is a proof of nonemptiness. Without this assumption, use instead `s.max`,
taking values in `with_bot α`. -/
def max' (s : Finset α) (H : s.Nonempty) : α :=
  sup' s H id
#align finset.max' Finset.max'
-/

variable (s : Finset α) (H : s.Nonempty) {x : α}

#print Finset.min'_mem /-
theorem min'_mem : s.min' H ∈ s :=
  mem_of_min <| by simp [min', Finset.min]
#align finset.min'_mem Finset.min'_mem
-/

/- warning: finset.min'_le -> Finset.min'_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (s : Finset.{u1} α) (x : α) (H2 : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (Finset.min'.{u1} α _inst_1 s (Exists.intro.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) x H2)) x
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (s : Finset.{u1} α) (x : α) (H2 : Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (Finset.min'.{u1} α _inst_1 s (Exists.intro.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s) x H2)) x
Case conversion may be inaccurate. Consider using '#align finset.min'_le Finset.min'_leₓ'. -/
theorem min'_le (x) (H2 : x ∈ s) : s.min' ⟨x, H2⟩ ≤ x :=
  min_le_of_eq H2 (WithTop.coe_untop _ _).symm
#align finset.min'_le Finset.min'_le

/- warning: finset.le_min' -> Finset.le_min' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (s : Finset.{u1} α) (H : Finset.Nonempty.{u1} α s) (x : α), (forall (y : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) x y)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) x (Finset.min'.{u1} α _inst_1 s H))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (s : Finset.{u1} α) (H : Finset.Nonempty.{u1} α s) (x : α), (forall (y : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) y s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x y)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x (Finset.min'.{u1} α _inst_1 s H))
Case conversion may be inaccurate. Consider using '#align finset.le_min' Finset.le_min'ₓ'. -/
theorem le_min' (x) (H2 : ∀ y ∈ s, x ≤ y) : x ≤ s.min' H :=
  H2 _ <| min'_mem _ _
#align finset.le_min' Finset.le_min'

#print Finset.isLeast_min' /-
theorem isLeast_min' : IsLeast (↑s) (s.min' H) :=
  ⟨min'_mem _ _, min'_le _⟩
#align finset.is_least_min' Finset.isLeast_min'
-/

/- warning: finset.le_min'_iff -> Finset.le_min'_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (s : Finset.{u1} α) (H : Finset.Nonempty.{u1} α s) {x : α}, Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) x (Finset.min'.{u1} α _inst_1 s H)) (forall (y : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) x y))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (s : Finset.{u1} α) (H : Finset.Nonempty.{u1} α s) {x : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x (Finset.min'.{u1} α _inst_1 s H)) (forall (y : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) y s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x y))
Case conversion may be inaccurate. Consider using '#align finset.le_min'_iff Finset.le_min'_iffₓ'. -/
@[simp]
theorem le_min'_iff {x} : x ≤ s.min' H ↔ ∀ y ∈ s, x ≤ y :=
  le_isGLB_iff (isLeast_min' s H).IsGLB
#align finset.le_min'_iff Finset.le_min'_iff

#print Finset.min'_singleton /-
/-- `{a}.min' _` is `a`. -/
@[simp]
theorem min'_singleton (a : α) : ({a} : Finset α).min' (singleton_nonempty _) = a := by simp [min']
#align finset.min'_singleton Finset.min'_singleton
-/

#print Finset.max'_mem /-
theorem max'_mem : s.max' H ∈ s :=
  mem_of_max <| by simp [max', Finset.max]
#align finset.max'_mem Finset.max'_mem
-/

/- warning: finset.le_max' -> Finset.le_max' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (s : Finset.{u1} α) (x : α) (H2 : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) x (Finset.max'.{u1} α _inst_1 s (Exists.intro.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) x H2))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (s : Finset.{u1} α) (x : α) (H2 : Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x (Finset.max'.{u1} α _inst_1 s (Exists.intro.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s) x H2))
Case conversion may be inaccurate. Consider using '#align finset.le_max' Finset.le_max'ₓ'. -/
theorem le_max' (x) (H2 : x ∈ s) : x ≤ s.max' ⟨x, H2⟩ :=
  le_max_of_eq H2 (WithBot.coe_unbot _ _).symm
#align finset.le_max' Finset.le_max'

/- warning: finset.max'_le -> Finset.max'_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (s : Finset.{u1} α) (H : Finset.Nonempty.{u1} α s) (x : α), (forall (y : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) y x)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (Finset.max'.{u1} α _inst_1 s H) x)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (s : Finset.{u1} α) (H : Finset.Nonempty.{u1} α s) (x : α), (forall (y : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) y s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) y x)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (Finset.max'.{u1} α _inst_1 s H) x)
Case conversion may be inaccurate. Consider using '#align finset.max'_le Finset.max'_leₓ'. -/
theorem max'_le (x) (H2 : ∀ y ∈ s, y ≤ x) : s.max' H ≤ x :=
  H2 _ <| max'_mem _ _
#align finset.max'_le Finset.max'_le

#print Finset.isGreatest_max' /-
theorem isGreatest_max' : IsGreatest (↑s) (s.max' H) :=
  ⟨max'_mem _ _, le_max' _⟩
#align finset.is_greatest_max' Finset.isGreatest_max'
-/

/- warning: finset.max'_le_iff -> Finset.max'_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (s : Finset.{u1} α) (H : Finset.Nonempty.{u1} α s) {x : α}, Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (Finset.max'.{u1} α _inst_1 s H) x) (forall (y : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) y x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (s : Finset.{u1} α) (H : Finset.Nonempty.{u1} α s) {x : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (Finset.max'.{u1} α _inst_1 s H) x) (forall (y : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) y s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) y x))
Case conversion may be inaccurate. Consider using '#align finset.max'_le_iff Finset.max'_le_iffₓ'. -/
@[simp]
theorem max'_le_iff {x} : s.max' H ≤ x ↔ ∀ y ∈ s, y ≤ x :=
  isLUB_le_iff (isGreatest_max' s H).IsLUB
#align finset.max'_le_iff Finset.max'_le_iff

/- warning: finset.max'_lt_iff -> Finset.max'_lt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (s : Finset.{u1} α) (H : Finset.Nonempty.{u1} α s) {x : α}, Iff (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (Finset.max'.{u1} α _inst_1 s H) x) (forall (y : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y s) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) y x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (s : Finset.{u1} α) (H : Finset.Nonempty.{u1} α s) {x : α}, Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (Finset.max'.{u1} α _inst_1 s H) x) (forall (y : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) y s) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) y x))
Case conversion may be inaccurate. Consider using '#align finset.max'_lt_iff Finset.max'_lt_iffₓ'. -/
@[simp]
theorem max'_lt_iff {x} : s.max' H < x ↔ ∀ y ∈ s, y < x :=
  ⟨fun Hlt y hy => (s.le_max' y hy).trans_lt Hlt, fun H => H _ <| s.max'_mem _⟩
#align finset.max'_lt_iff Finset.max'_lt_iff

/- warning: finset.lt_min'_iff -> Finset.lt_min'_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (s : Finset.{u1} α) (H : Finset.Nonempty.{u1} α s) {x : α}, Iff (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) x (Finset.min'.{u1} α _inst_1 s H)) (forall (y : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y s) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) x y))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (s : Finset.{u1} α) (H : Finset.Nonempty.{u1} α s) {x : α}, Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x (Finset.min'.{u1} α _inst_1 s H)) (forall (y : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) y s) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x y))
Case conversion may be inaccurate. Consider using '#align finset.lt_min'_iff Finset.lt_min'_iffₓ'. -/
@[simp]
theorem lt_min'_iff : x < s.min' H ↔ ∀ y ∈ s, x < y :=
  @max'_lt_iff αᵒᵈ _ _ H _
#align finset.lt_min'_iff Finset.lt_min'_iff

#print Finset.max'_eq_sup' /-
theorem max'_eq_sup' : s.max' H = s.sup' H id :=
  eq_of_forall_ge_iff fun a => (max'_le_iff _ _).trans (sup'_le_iff _ _).symm
#align finset.max'_eq_sup' Finset.max'_eq_sup'
-/

#print Finset.min'_eq_inf' /-
theorem min'_eq_inf' : s.min' H = s.inf' H id :=
  @max'_eq_sup' αᵒᵈ _ s H
#align finset.min'_eq_inf' Finset.min'_eq_inf'
-/

#print Finset.max'_singleton /-
/-- `{a}.max' _` is `a`. -/
@[simp]
theorem max'_singleton (a : α) : ({a} : Finset α).max' (singleton_nonempty _) = a := by simp [max']
#align finset.max'_singleton Finset.max'_singleton
-/

/- warning: finset.min'_lt_max' -> Finset.min'_lt_max' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (s : Finset.{u1} α) {i : α} {j : α} (H1 : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i s), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) j s) -> (Ne.{succ u1} α i j) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (Finset.min'.{u1} α _inst_1 s (Exists.intro.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) i H1)) (Finset.max'.{u1} α _inst_1 s (Exists.intro.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) i H1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (s : Finset.{u1} α) {i : α} {j : α} (H1 : Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) i s), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) j s) -> (Ne.{succ u1} α i j) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (Finset.min'.{u1} α _inst_1 s (Exists.intro.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s) i H1)) (Finset.max'.{u1} α _inst_1 s (Exists.intro.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s) i H1)))
Case conversion may be inaccurate. Consider using '#align finset.min'_lt_max' Finset.min'_lt_max'ₓ'. -/
theorem min'_lt_max' {i j} (H1 : i ∈ s) (H2 : j ∈ s) (H3 : i ≠ j) :
    s.min' ⟨i, H1⟩ < s.max' ⟨i, H1⟩ :=
  isGLB_lt_isLUB_of_ne (s.isLeast_min' _).IsGLB (s.isGreatest_max' _).IsLUB H1 H2 H3
#align finset.min'_lt_max' Finset.min'_lt_max'

/- warning: finset.min'_lt_max'_of_card -> Finset.min'_lt_max'_of_card is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (s : Finset.{u1} α) (h₂ : LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (Finset.card.{u1} α s)), LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (Finset.min'.{u1} α _inst_1 s (Iff.mp (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (Finset.card.{u1} α s)) (Finset.Nonempty.{u1} α s) (Finset.card_pos.{u1} α s) (lt_trans.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (Finset.card.{u1} α s) (zero_lt_one.{0} Nat Nat.hasZero Nat.hasOne (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)) (OrderedSemiring.zeroLEOneClass.{0} Nat Nat.orderedSemiring) (NeZero.one.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) Nat.nontrivial)) h₂))) (Finset.max'.{u1} α _inst_1 s (Iff.mp (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (Finset.card.{u1} α s)) (Finset.Nonempty.{u1} α s) (Finset.card_pos.{u1} α s) (lt_trans.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (Finset.card.{u1} α s) (zero_lt_one.{0} Nat Nat.hasZero Nat.hasOne (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)) (OrderedSemiring.zeroLEOneClass.{0} Nat Nat.orderedSemiring) (NeZero.one.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) Nat.nontrivial)) h₂)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (s : Finset.{u1} α) (h₂ : LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (Finset.card.{u1} α s)), LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (Finset.min'.{u1} α _inst_1 s (Iff.mp (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (Finset.card.{u1} α s)) (Finset.Nonempty.{u1} α s) (Finset.card_pos.{u1} α s) (lt_trans.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (OfNat.ofNat.{0} Nat 1 (One.toOfNat1.{0} Nat (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring))) (Finset.card.{u1} α s) (zero_lt_one.{0} Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring) (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring) (OrderedSemiring.zeroLEOneClass.{0} Nat Nat.orderedSemiring) (NeZero.succ Nat.zero)) h₂))) (Finset.max'.{u1} α _inst_1 s (Iff.mp (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (Finset.card.{u1} α s)) (Finset.Nonempty.{u1} α s) (Finset.card_pos.{u1} α s) (lt_trans.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (OfNat.ofNat.{0} Nat 1 (One.toOfNat1.{0} Nat (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring))) (Finset.card.{u1} α s) (zero_lt_one.{0} Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring) (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring) (OrderedSemiring.zeroLEOneClass.{0} Nat Nat.orderedSemiring) (NeZero.succ Nat.zero)) h₂)))
Case conversion may be inaccurate. Consider using '#align finset.min'_lt_max'_of_card Finset.min'_lt_max'_of_cardₓ'. -/
/-- If there's more than 1 element, the min' is less than the max'. An alternate version of
`min'_lt_max'` which is sometimes more convenient.
-/
theorem min'_lt_max'_of_card (h₂ : 1 < card s) :
    s.min' (Finset.card_pos.mp <| lt_trans zero_lt_one h₂) <
      s.max' (Finset.card_pos.mp <| lt_trans zero_lt_one h₂) :=
  by
  rcases one_lt_card.1 h₂ with ⟨a, ha, b, hb, hab⟩
  exact s.min'_lt_max' ha hb hab
#align finset.min'_lt_max'_of_card Finset.min'_lt_max'_of_card

#print Finset.map_ofDual_min /-
theorem map_ofDual_min (s : Finset αᵒᵈ) : s.min.map ofDual = (s.image ofDual).max :=
  by
  rw [max_eq_sup_with_bot, sup_image]
  exact congr_fun Option.map_id _
#align finset.map_of_dual_min Finset.map_ofDual_min
-/

#print Finset.map_ofDual_max /-
theorem map_ofDual_max (s : Finset αᵒᵈ) : s.max.map ofDual = (s.image ofDual).min :=
  by
  rw [min_eq_inf_with_top, inf_image]
  exact congr_fun Option.map_id _
#align finset.map_of_dual_max Finset.map_ofDual_max
-/

#print Finset.map_toDual_min /-
theorem map_toDual_min (s : Finset α) : s.min.map toDual = (s.image toDual).max :=
  by
  rw [max_eq_sup_with_bot, sup_image]
  exact congr_fun Option.map_id _
#align finset.map_to_dual_min Finset.map_toDual_min
-/

#print Finset.map_toDual_max /-
theorem map_toDual_max (s : Finset α) : s.max.map toDual = (s.image toDual).min :=
  by
  rw [min_eq_inf_with_top, inf_image]
  exact congr_fun Option.map_id _
#align finset.map_to_dual_max Finset.map_toDual_max
-/

#print Finset.ofDual_min' /-
theorem ofDual_min' {s : Finset αᵒᵈ} (hs : s.Nonempty) :
    ofDual (min' s hs) = max' (s.image ofDual) (hs.image _) :=
  by
  convert rfl
  exact image_id
#align finset.of_dual_min' Finset.ofDual_min'
-/

#print Finset.ofDual_max' /-
theorem ofDual_max' {s : Finset αᵒᵈ} (hs : s.Nonempty) :
    ofDual (max' s hs) = min' (s.image ofDual) (hs.image _) :=
  by
  convert rfl
  exact image_id
#align finset.of_dual_max' Finset.ofDual_max'
-/

#print Finset.toDual_min' /-
theorem toDual_min' {s : Finset α} (hs : s.Nonempty) :
    toDual (min' s hs) = max' (s.image toDual) (hs.image _) :=
  by
  convert rfl
  exact image_id
#align finset.to_dual_min' Finset.toDual_min'
-/

#print Finset.toDual_max' /-
theorem toDual_max' {s : Finset α} (hs : s.Nonempty) :
    toDual (max' s hs) = min' (s.image toDual) (hs.image _) :=
  by
  convert rfl
  exact image_id
#align finset.to_dual_max' Finset.toDual_max'
-/

/- warning: finset.max'_subset -> Finset.max'_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} (H : Finset.Nonempty.{u1} α s) (hst : HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s t), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (Finset.max'.{u1} α _inst_1 s H) (Finset.max'.{u1} α _inst_1 t (Finset.Nonempty.mono.{u1} α s t hst H))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} (H : Finset.Nonempty.{u1} α s) (hst : HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) s t), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (Finset.max'.{u1} α _inst_1 s H) (Finset.max'.{u1} α _inst_1 t (Finset.Nonempty.mono.{u1} α s t hst H))
Case conversion may be inaccurate. Consider using '#align finset.max'_subset Finset.max'_subsetₓ'. -/
theorem max'_subset {s t : Finset α} (H : s.Nonempty) (hst : s ⊆ t) :
    s.max' H ≤ t.max' (H.mono hst) :=
  le_max' _ _ (hst (s.max'_mem H))
#align finset.max'_subset Finset.max'_subset

/- warning: finset.min'_subset -> Finset.min'_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} (H : Finset.Nonempty.{u1} α s) (hst : HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s t), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (Finset.min'.{u1} α _inst_1 t (Finset.Nonempty.mono.{u1} α s t hst H)) (Finset.min'.{u1} α _inst_1 s H)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} (H : Finset.Nonempty.{u1} α s) (hst : HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) s t), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (Finset.min'.{u1} α _inst_1 t (Finset.Nonempty.mono.{u1} α s t hst H)) (Finset.min'.{u1} α _inst_1 s H)
Case conversion may be inaccurate. Consider using '#align finset.min'_subset Finset.min'_subsetₓ'. -/
theorem min'_subset {s t : Finset α} (H : s.Nonempty) (hst : s ⊆ t) :
    t.min' (H.mono hst) ≤ s.min' H :=
  min'_le _ _ (hst (s.min'_mem H))
#align finset.min'_subset Finset.min'_subset

/- warning: finset.max'_insert -> Finset.max'_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (s : Finset.{u1} α) (H : Finset.Nonempty.{u1} α s), Eq.{succ u1} α (Finset.max'.{u1} α _inst_1 (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => Eq.decidable.{u1} α _inst_1 a b)) a s) (Finset.insert_nonempty.{u1} α (fun (a : α) (b : α) => Eq.decidable.{u1} α _inst_1 a b) a s)) (LinearOrder.max.{u1} α _inst_1 (Finset.max'.{u1} α _inst_1 s H) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (s : Finset.{u1} α) (H : Finset.Nonempty.{u1} α s), Eq.{succ u1} α (Finset.max'.{u1} α _inst_1 (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => instDecidableEq.{u1} α _inst_1 a b)) a s) (Finset.insert_nonempty.{u1} α (fun (a : α) (b : α) => instDecidableEq.{u1} α _inst_1 a b) a s)) (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) (Finset.max'.{u1} α _inst_1 s H) a)
Case conversion may be inaccurate. Consider using '#align finset.max'_insert Finset.max'_insertₓ'. -/
theorem max'_insert (a : α) (s : Finset α) (H : s.Nonempty) :
    (insert a s).max' (s.insert_nonempty a) = max (s.max' H) a :=
  (isGreatest_max' _ _).unique <| by
    rw [coe_insert, max_comm]
    exact (is_greatest_max' _ _).insert _
#align finset.max'_insert Finset.max'_insert

/- warning: finset.min'_insert -> Finset.min'_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (s : Finset.{u1} α) (H : Finset.Nonempty.{u1} α s), Eq.{succ u1} α (Finset.min'.{u1} α _inst_1 (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => Eq.decidable.{u1} α _inst_1 a b)) a s) (Finset.insert_nonempty.{u1} α (fun (a : α) (b : α) => Eq.decidable.{u1} α _inst_1 a b) a s)) (LinearOrder.min.{u1} α _inst_1 (Finset.min'.{u1} α _inst_1 s H) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (a : α) (s : Finset.{u1} α) (H : Finset.Nonempty.{u1} α s), Eq.{succ u1} α (Finset.min'.{u1} α _inst_1 (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => instDecidableEq.{u1} α _inst_1 a b)) a s) (Finset.insert_nonempty.{u1} α (fun (a : α) (b : α) => instDecidableEq.{u1} α _inst_1 a b) a s)) (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) (Finset.min'.{u1} α _inst_1 s H) a)
Case conversion may be inaccurate. Consider using '#align finset.min'_insert Finset.min'_insertₓ'. -/
theorem min'_insert (a : α) (s : Finset α) (H : s.Nonempty) :
    (insert a s).min' (s.insert_nonempty a) = min (s.min' H) a :=
  (isLeast_min' _ _).unique <| by
    rw [coe_insert, min_comm]
    exact (is_least_min' _ _).insert _
#align finset.min'_insert Finset.min'_insert

/- warning: finset.lt_max'_of_mem_erase_max' -> Finset.lt_max'_of_mem_erase_max' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (s : Finset.{u1} α) (H : Finset.Nonempty.{u1} α s) [_inst_2 : DecidableEq.{succ u1} α] {a : α}, (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (Finset.erase.{u1} α (fun (a : α) (b : α) => _inst_2 a b) s (Finset.max'.{u1} α _inst_1 s H))) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a (Finset.max'.{u1} α _inst_1 s H))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (s : Finset.{u1} α) (H : Finset.Nonempty.{u1} α s) [_inst_2 : DecidableEq.{succ u1} α] {a : α}, (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a (Finset.erase.{u1} α (fun (a : α) (b : α) => _inst_2 a b) s (Finset.max'.{u1} α _inst_1 s H))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) a (Finset.max'.{u1} α _inst_1 s H))
Case conversion may be inaccurate. Consider using '#align finset.lt_max'_of_mem_erase_max' Finset.lt_max'_of_mem_erase_max'ₓ'. -/
theorem lt_max'_of_mem_erase_max' [DecidableEq α] {a : α} (ha : a ∈ s.eraseₓ (s.max' H)) :
    a < s.max' H :=
  lt_of_le_of_ne (le_max' _ _ (mem_of_mem_erase ha)) <| ne_of_mem_of_not_mem ha <| not_mem_erase _ _
#align finset.lt_max'_of_mem_erase_max' Finset.lt_max'_of_mem_erase_max'

/- warning: finset.min'_lt_of_mem_erase_min' -> Finset.min'_lt_of_mem_erase_min' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (s : Finset.{u1} α) (H : Finset.Nonempty.{u1} α s) [_inst_2 : DecidableEq.{succ u1} α] {a : α}, (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (Finset.erase.{u1} α (fun (a : α) (b : α) => _inst_2 a b) s (Finset.min'.{u1} α _inst_1 s H))) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (Finset.min'.{u1} α _inst_1 s H) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (s : Finset.{u1} α) (H : Finset.Nonempty.{u1} α s) [_inst_2 : DecidableEq.{succ u1} α] {a : α}, (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a (Finset.erase.{u1} α (fun (a : α) (b : α) => _inst_2 a b) s (Finset.min'.{u1} α _inst_1 s H))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (Finset.min'.{u1} α _inst_1 s H) a)
Case conversion may be inaccurate. Consider using '#align finset.min'_lt_of_mem_erase_min' Finset.min'_lt_of_mem_erase_min'ₓ'. -/
theorem min'_lt_of_mem_erase_min' [DecidableEq α] {a : α} (ha : a ∈ s.eraseₓ (s.min' H)) :
    s.min' H < a :=
  @lt_max'_of_mem_erase_max' αᵒᵈ _ s H _ a ha
#align finset.min'_lt_of_mem_erase_min' Finset.min'_lt_of_mem_erase_min'

#print Finset.max'_image /-
@[simp]
theorem max'_image [LinearOrder β] {f : α → β} (hf : Monotone f) (s : Finset α)
    (h : (s.image f).Nonempty) : (s.image f).max' h = f (s.max' ((Nonempty.image_iff f).mp h)) :=
  by
  refine'
    le_antisymm (max'_le _ _ _ fun y hy => _) (le_max' _ _ (mem_image.mpr ⟨_, max'_mem _ _, rfl⟩))
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
  exact hf (le_max' _ _ hx)
#align finset.max'_image Finset.max'_image
-/

#print Finset.min'_image /-
@[simp]
theorem min'_image [LinearOrder β] {f : α → β} (hf : Monotone f) (s : Finset α)
    (h : (s.image f).Nonempty) : (s.image f).min' h = f (s.min' ((Nonempty.image_iff f).mp h)) :=
  by
  convert@max'_image αᵒᵈ βᵒᵈ _ _ (fun a : αᵒᵈ => to_dual (f (of_dual a))) (by simpa) _ _ <;>
    convert h
  rw [nonempty.image_iff]
#align finset.min'_image Finset.min'_image
-/

#print Finset.coe_max' /-
theorem coe_max' {s : Finset α} (hs : s.Nonempty) : ↑(s.max' hs) = s.max :=
  coe_sup' hs id
#align finset.coe_max' Finset.coe_max'
-/

#print Finset.coe_min' /-
theorem coe_min' {s : Finset α} (hs : s.Nonempty) : ↑(s.min' hs) = s.min :=
  coe_inf' hs id
#align finset.coe_min' Finset.coe_min'
-/

/- warning: finset.max_mem_image_coe -> Finset.max_mem_image_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {s : Finset.{u1} α}, (Finset.Nonempty.{u1} α s) -> (Membership.Mem.{u1, u1} (WithBot.{u1} α) (Finset.{u1} (WithBot.{u1} α)) (Finset.hasMem.{u1} (WithBot.{u1} α)) (Finset.max.{u1} α _inst_1 s) (Finset.image.{u1, u1} α (WithBot.{u1} α) (fun (a : WithBot.{u1} α) (b : WithBot.{u1} α) => Option.decidableEq.{u1} α (fun (a : α) (b : α) => Eq.decidable.{u1} α _inst_1 a b) a b) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α)))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {s : Finset.{u1} α}, (Finset.Nonempty.{u1} α s) -> (Membership.mem.{u1, u1} (WithBot.{u1} α) (Finset.{u1} (WithBot.{u1} α)) (Finset.instMembershipFinset.{u1} (WithBot.{u1} α)) (Finset.max.{u1} α _inst_1 s) (Finset.image.{u1, u1} α (WithBot.{u1} α) (fun (a : WithBot.{u1} α) (b : WithBot.{u1} α) => WithBot.decidableEq.{u1} α (fun (a : α) (b : α) => instDecidableEq.{u1} α _inst_1 a b) a b) (WithBot.some.{u1} α) s))
Case conversion may be inaccurate. Consider using '#align finset.max_mem_image_coe Finset.max_mem_image_coeₓ'. -/
theorem max_mem_image_coe {s : Finset α} (hs : s.Nonempty) :
    s.max ∈ (s.image coe : Finset (WithBot α)) :=
  mem_image.2 ⟨max' s hs, max'_mem _ _, coe_max' hs⟩
#align finset.max_mem_image_coe Finset.max_mem_image_coe

/- warning: finset.min_mem_image_coe -> Finset.min_mem_image_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {s : Finset.{u1} α}, (Finset.Nonempty.{u1} α s) -> (Membership.Mem.{u1, u1} (WithTop.{u1} α) (Finset.{u1} (WithTop.{u1} α)) (Finset.hasMem.{u1} (WithTop.{u1} α)) (Finset.min.{u1} α _inst_1 s) (Finset.image.{u1, u1} α (WithTop.{u1} α) (fun (a : WithTop.{u1} α) (b : WithTop.{u1} α) => Option.decidableEq.{u1} α (fun (a : α) (b : α) => Eq.decidable.{u1} α _inst_1 a b) a b) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α)))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {s : Finset.{u1} α}, (Finset.Nonempty.{u1} α s) -> (Membership.mem.{u1, u1} (WithTop.{u1} α) (Finset.{u1} (WithTop.{u1} α)) (Finset.instMembershipFinset.{u1} (WithTop.{u1} α)) (Finset.min.{u1} α _inst_1 s) (Finset.image.{u1, u1} α (WithTop.{u1} α) (fun (a : WithTop.{u1} α) (b : WithTop.{u1} α) => WithTop.decidableEq.{u1} α (fun (a : α) (b : α) => instDecidableEq.{u1} α _inst_1 a b) a b) (WithTop.some.{u1} α) s))
Case conversion may be inaccurate. Consider using '#align finset.min_mem_image_coe Finset.min_mem_image_coeₓ'. -/
theorem min_mem_image_coe {s : Finset α} (hs : s.Nonempty) :
    s.min ∈ (s.image coe : Finset (WithTop α)) :=
  mem_image.2 ⟨min' s hs, min'_mem _ _, coe_min' hs⟩
#align finset.min_mem_image_coe Finset.min_mem_image_coe

/- warning: finset.max_mem_insert_bot_image_coe -> Finset.max_mem_insert_bot_image_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (s : Finset.{u1} α), Membership.Mem.{u1, u1} (WithBot.{u1} α) (Finset.{u1} (WithBot.{u1} α)) (Finset.hasMem.{u1} (WithBot.{u1} α)) (Finset.max.{u1} α _inst_1 s) (Insert.insert.{u1, u1} (WithBot.{u1} α) (Finset.{u1} (WithBot.{u1} α)) (Finset.hasInsert.{u1} (WithBot.{u1} α) (fun (a : WithBot.{u1} α) (b : WithBot.{u1} α) => Option.decidableEq.{u1} α (fun (a : α) (b : α) => Eq.decidable.{u1} α _inst_1 a b) a b)) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α)) (Finset.image.{u1, u1} α (WithBot.{u1} α) (fun (a : WithBot.{u1} α) (b : WithBot.{u1} α) => Option.decidableEq.{u1} α (fun (a : α) (b : α) => Eq.decidable.{u1} α _inst_1 a b) a b) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α)))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (s : Finset.{u1} α), Membership.mem.{u1, u1} (WithBot.{u1} α) (Finset.{u1} (WithBot.{u1} α)) (Finset.instMembershipFinset.{u1} (WithBot.{u1} α)) (Finset.max.{u1} α _inst_1 s) (Insert.insert.{u1, u1} (WithBot.{u1} α) (Finset.{u1} (WithBot.{u1} α)) (Finset.instInsertFinset.{u1} (WithBot.{u1} α) (fun (a : WithBot.{u1} α) (b : WithBot.{u1} α) => WithBot.decidableEq.{u1} α (fun (a : α) (b : α) => instDecidableEq.{u1} α _inst_1 a b) a b)) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.bot.{u1} α)) (Finset.image.{u1, u1} α (WithBot.{u1} α) (fun (a : WithBot.{u1} α) (b : WithBot.{u1} α) => WithBot.decidableEq.{u1} α (fun (a : α) (b : α) => instDecidableEq.{u1} α _inst_1 a b) a b) (WithBot.some.{u1} α) s))
Case conversion may be inaccurate. Consider using '#align finset.max_mem_insert_bot_image_coe Finset.max_mem_insert_bot_image_coeₓ'. -/
theorem max_mem_insert_bot_image_coe (s : Finset α) :
    s.max ∈ (insert ⊥ (s.image coe) : Finset (WithBot α)) :=
  mem_insert.2 <| s.eq_empty_or_nonempty.imp max_eq_bot.2 max_mem_image_coe
#align finset.max_mem_insert_bot_image_coe Finset.max_mem_insert_bot_image_coe

/- warning: finset.min_mem_insert_top_image_coe -> Finset.min_mem_insert_top_image_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (s : Finset.{u1} α), Membership.Mem.{u1, u1} (WithTop.{u1} α) (Finset.{u1} (WithTop.{u1} α)) (Finset.hasMem.{u1} (WithTop.{u1} α)) (Finset.min.{u1} α _inst_1 s) (Insert.insert.{u1, u1} (WithTop.{u1} α) (Finset.{u1} (WithTop.{u1} α)) (Finset.hasInsert.{u1} (WithTop.{u1} α) (fun (a : WithTop.{u1} α) (b : WithTop.{u1} α) => Option.decidableEq.{u1} α (fun (a : α) (b : α) => Eq.decidable.{u1} α _inst_1 a b) a b)) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α)) (Finset.image.{u1, u1} α (WithTop.{u1} α) (fun (a : WithTop.{u1} α) (b : WithTop.{u1} α) => Option.decidableEq.{u1} α (fun (a : α) (b : α) => Eq.decidable.{u1} α _inst_1 a b) a b) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α)))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (s : Finset.{u1} α), Membership.mem.{u1, u1} (WithTop.{u1} α) (Finset.{u1} (WithTop.{u1} α)) (Finset.instMembershipFinset.{u1} (WithTop.{u1} α)) (Finset.min.{u1} α _inst_1 s) (Insert.insert.{u1, u1} (WithTop.{u1} α) (Finset.{u1} (WithTop.{u1} α)) (Finset.instInsertFinset.{u1} (WithTop.{u1} α) (fun (a : WithTop.{u1} α) (b : WithTop.{u1} α) => WithTop.decidableEq.{u1} α (fun (a : α) (b : α) => instDecidableEq.{u1} α _inst_1 a b) a b)) (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α)) (Finset.image.{u1, u1} α (WithTop.{u1} α) (fun (a : WithTop.{u1} α) (b : WithTop.{u1} α) => WithTop.decidableEq.{u1} α (fun (a : α) (b : α) => instDecidableEq.{u1} α _inst_1 a b) a b) (WithTop.some.{u1} α) s))
Case conversion may be inaccurate. Consider using '#align finset.min_mem_insert_top_image_coe Finset.min_mem_insert_top_image_coeₓ'. -/
theorem min_mem_insert_top_image_coe (s : Finset α) :
    s.min ∈ (insert ⊤ (s.image coe) : Finset (WithTop α)) :=
  mem_insert.2 <| s.eq_empty_or_nonempty.imp min_eq_top.2 min_mem_image_coe
#align finset.min_mem_insert_top_image_coe Finset.min_mem_insert_top_image_coe

#print Finset.max'_erase_ne_self /-
theorem max'_erase_ne_self {s : Finset α} (s0 : (s.eraseₓ x).Nonempty) : (s.eraseₓ x).max' s0 ≠ x :=
  ne_of_mem_erase (max'_mem _ s0)
#align finset.max'_erase_ne_self Finset.max'_erase_ne_self
-/

#print Finset.min'_erase_ne_self /-
theorem min'_erase_ne_self {s : Finset α} (s0 : (s.eraseₓ x).Nonempty) : (s.eraseₓ x).min' s0 ≠ x :=
  ne_of_mem_erase (min'_mem _ s0)
#align finset.min'_erase_ne_self Finset.min'_erase_ne_self
-/

#print Finset.max_erase_ne_self /-
theorem max_erase_ne_self {s : Finset α} : (s.eraseₓ x).max ≠ x :=
  by
  by_cases s0 : (s.erase x).Nonempty
  · refine' ne_of_eq_of_ne (coe_max' s0).symm _
    exact with_bot.coe_eq_coe.not.mpr (max'_erase_ne_self _)
  · rw [not_nonempty_iff_eq_empty.mp s0, max_empty]
    exact WithBot.bot_ne_coe
#align finset.max_erase_ne_self Finset.max_erase_ne_self
-/

#print Finset.min_erase_ne_self /-
theorem min_erase_ne_self {s : Finset α} : (s.eraseₓ x).min ≠ x := by
  convert@max_erase_ne_self αᵒᵈ _ _ _
#align finset.min_erase_ne_self Finset.min_erase_ne_self
-/

/- warning: finset.exists_next_right -> Finset.exists_next_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {x : α} {s : Finset.{u1} α}, (Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y s) => LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) x y))) -> (Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y s) => And (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) x y) (forall (z : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) z s) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) x z) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) y z)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {x : α} {s : Finset.{u1} α}, (Exists.{succ u1} α (fun (y : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) y s) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x y))) -> (Exists.{succ u1} α (fun (y : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) y s) (And (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x y) (forall (z : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) z s) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x z) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) y z)))))
Case conversion may be inaccurate. Consider using '#align finset.exists_next_right Finset.exists_next_rightₓ'. -/
theorem exists_next_right {x : α} {s : Finset α} (h : ∃ y ∈ s, x < y) :
    ∃ y ∈ s, x < y ∧ ∀ z ∈ s, x < z → y ≤ z :=
  have Hne : (s.filterₓ ((· < ·) x)).Nonempty := h.imp fun y hy => mem_filter.2 ⟨hy.fst, hy.snd⟩
  ⟨min' _ Hne, (mem_filter.1 (min'_mem _ Hne)).1, (mem_filter.1 (min'_mem _ Hne)).2, fun z hzs hz =>
    min'_le _ _ <| mem_filter.2 ⟨hzs, hz⟩⟩
#align finset.exists_next_right Finset.exists_next_right

/- warning: finset.exists_next_left -> Finset.exists_next_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {x : α} {s : Finset.{u1} α}, (Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y s) => LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) y x))) -> (Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y s) => And (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) y x) (forall (z : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) z s) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) z x) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) z y)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {x : α} {s : Finset.{u1} α}, (Exists.{succ u1} α (fun (y : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) y s) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) y x))) -> (Exists.{succ u1} α (fun (y : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) y s) (And (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) y x) (forall (z : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) z s) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) z x) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) z y)))))
Case conversion may be inaccurate. Consider using '#align finset.exists_next_left Finset.exists_next_leftₓ'. -/
theorem exists_next_left {x : α} {s : Finset α} (h : ∃ y ∈ s, y < x) :
    ∃ y ∈ s, y < x ∧ ∀ z ∈ s, z < x → z ≤ y :=
  @exists_next_right αᵒᵈ _ x s h
#align finset.exists_next_left Finset.exists_next_left

/- warning: finset.card_le_of_interleaved -> Finset.card_le_of_interleaved is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, (forall (x : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y s) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) x y) -> (forall (z : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) z s) -> (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) z (Set.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) x y)))) -> (Exists.{succ u1} α (fun (z : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) z t) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) z t) => And (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) x z) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) z y)))))) -> (LE.le.{0} Nat Nat.hasLe (Finset.card.{u1} α s) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (Finset.card.{u1} α t) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, (forall (x : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s) -> (forall (y : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) y s) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x y) -> (forall (z : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) z s) -> (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) z (Set.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) x y)))) -> (Exists.{succ u1} α (fun (z : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) z t) (And (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x z) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) z y)))))) -> (LE.le.{0} Nat instLENat (Finset.card.{u1} α s) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Finset.card.{u1} α t) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
Case conversion may be inaccurate. Consider using '#align finset.card_le_of_interleaved Finset.card_le_of_interleavedₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » s) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » s) -/
/-- If finsets `s` and `t` are interleaved, then `finset.card s ≤ finset.card t + 1`. -/
theorem card_le_of_interleaved {s t : Finset α}
    (h :
      ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s),
        x < y → (∀ z ∈ s, z ∉ Set.Ioo x y) → ∃ z ∈ t, x < z ∧ z < y) :
    s.card ≤ t.card + 1 :=
  by
  replace h : ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s), x < y → ∃ z ∈ t, x < z ∧ z < y
  · intro x hx y hy hxy
    rcases exists_next_right ⟨y, hy, hxy⟩ with ⟨a, has, hxa, ha⟩
    rcases h x hx a has hxa fun z hzs hz => hz.2.not_le <| ha _ hzs hz.1 with ⟨b, hbt, hxb, hba⟩
    exact ⟨b, hbt, hxb, hba.trans_le <| ha _ hy hxy⟩
  set f : α → WithTop α := fun x => (t.filter fun y => x < y).min
  have f_mono : StrictMonoOn f s := by
    intro x hx y hy hxy
    rcases h x hx y hy hxy with ⟨a, hat, hxa, hay⟩
    calc
      f x ≤ a := min_le (mem_filter.2 ⟨hat, hxa⟩)
      _ < f y :=
        (Finset.lt_inf_iff <| WithTop.coe_lt_top a).2 fun b hb =>
          WithTop.coe_lt_coe.2 <| hay.trans (mem_filter.1 hb).2
      
  calc
    s.card = (s.image f).card := (card_image_of_inj_on f_mono.inj_on).symm
    _ ≤ (insert ⊤ (t.image coe) : Finset (WithTop α)).card :=
      (card_mono <|
        image_subset_iff.2 fun x hx =>
          insert_subset_insert _ (image_subset_image <| filter_subset _ _)
            (min_mem_insert_top_image_coe _))
    _ ≤ t.card + 1 := (card_insert_le _ _).trans (add_le_add_right card_image_le _)
    
#align finset.card_le_of_interleaved Finset.card_le_of_interleaved

/- warning: finset.card_le_diff_of_interleaved -> Finset.card_le_diff_of_interleaved is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, (forall (x : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y s) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) x y) -> (forall (z : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) z s) -> (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) z (Set.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) x y)))) -> (Exists.{succ u1} α (fun (z : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) z t) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) z t) => And (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) x z) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) z y)))))) -> (LE.le.{0} Nat Nat.hasLe (Finset.card.{u1} α s) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (Finset.card.{u1} α (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.hasSdiff.{u1} α (fun (a : α) (b : α) => Eq.decidable.{u1} α _inst_1 a b)) t s)) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, (forall (x : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s) -> (forall (y : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) y s) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x y) -> (forall (z : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) z s) -> (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) z (Set.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) x y)))) -> (Exists.{succ u1} α (fun (z : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) z t) (And (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x z) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) z y)))))) -> (LE.le.{0} Nat instLENat (Finset.card.{u1} α s) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Finset.card.{u1} α (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.instSDiffFinset.{u1} α (fun (a : α) (b : α) => instDecidableEq.{u1} α _inst_1 a b)) t s)) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
Case conversion may be inaccurate. Consider using '#align finset.card_le_diff_of_interleaved Finset.card_le_diff_of_interleavedₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » s) -/
/-- If finsets `s` and `t` are interleaved, then `finset.card s ≤ finset.card (t \ s) + 1`. -/
theorem card_le_diff_of_interleaved {s t : Finset α}
    (h :
      ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s),
        x < y → (∀ z ∈ s, z ∉ Set.Ioo x y) → ∃ z ∈ t, x < z ∧ z < y) :
    s.card ≤ (t \ s).card + 1 :=
  card_le_of_interleaved fun x hx y hy hxy hs =>
    let ⟨z, hzt, hxz, hzy⟩ := h x hx y hy hxy hs
    ⟨z, mem_sdiff.2 ⟨hzt, fun hzs => hs z hzs ⟨hxz, hzy⟩⟩, hxz, hzy⟩
#align finset.card_le_diff_of_interleaved Finset.card_le_diff_of_interleaved

/- warning: finset.induction_on_max -> Finset.induction_on_max is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] {p : (Finset.{u1} α) -> Prop} (s : Finset.{u1} α), (p (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α))) -> (forall (a : α) (s : Finset.{u1} α), (forall (x : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) x a)) -> (p s) -> (p (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s))) -> (p s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] {p : (Finset.{u1} α) -> Prop} (s : Finset.{u1} α), (p (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.instEmptyCollectionFinset.{u1} α))) -> (forall (a : α) (s : Finset.{u1} α), (forall (x : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x a)) -> (p s) -> (p (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s))) -> (p s)
Case conversion may be inaccurate. Consider using '#align finset.induction_on_max Finset.induction_on_maxₓ'. -/
/-- Induction principle for `finset`s in a linearly ordered type: a predicate is true on all
`s : finset α` provided that:

* it is true on the empty `finset`,
* for every `s : finset α` and an element `a` strictly greater than all elements of `s`, `p s`
  implies `p (insert a s)`. -/
@[elab_as_elim]
theorem induction_on_max [DecidableEq α] {p : Finset α → Prop} (s : Finset α) (h0 : p ∅)
    (step : ∀ a s, (∀ x ∈ s, x < a) → p s → p (insert a s)) : p s :=
  by
  induction' s using Finset.strongInductionOn with s ihs
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · exact h0
  · have H : s.max' hne ∈ s := max'_mem s hne
    rw [← insert_erase H]
    exact step _ _ (fun x => s.lt_max'_of_mem_erase_max' hne) (ihs _ <| erase_ssubset H)
#align finset.induction_on_max Finset.induction_on_max

/- warning: finset.induction_on_min -> Finset.induction_on_min is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] {p : (Finset.{u1} α) -> Prop} (s : Finset.{u1} α), (p (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α))) -> (forall (a : α) (s : Finset.{u1} α), (forall (x : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a x)) -> (p s) -> (p (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s))) -> (p s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] {p : (Finset.{u1} α) -> Prop} (s : Finset.{u1} α), (p (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.instEmptyCollectionFinset.{u1} α))) -> (forall (a : α) (s : Finset.{u1} α), (forall (x : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) a x)) -> (p s) -> (p (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s))) -> (p s)
Case conversion may be inaccurate. Consider using '#align finset.induction_on_min Finset.induction_on_minₓ'. -/
/-- Induction principle for `finset`s in a linearly ordered type: a predicate is true on all
`s : finset α` provided that:

* it is true on the empty `finset`,
* for every `s : finset α` and an element `a` strictly less than all elements of `s`, `p s`
  implies `p (insert a s)`. -/
@[elab_as_elim]
theorem induction_on_min [DecidableEq α] {p : Finset α → Prop} (s : Finset α) (h0 : p ∅)
    (step : ∀ a s, (∀ x ∈ s, a < x) → p s → p (insert a s)) : p s :=
  @induction_on_max αᵒᵈ _ _ _ s h0 step
#align finset.induction_on_min Finset.induction_on_min

end MaxMin

section MaxMinInductionValue

variable [LinearOrder α] [LinearOrder β]

/- warning: finset.induction_on_max_value -> Finset.induction_on_max_value is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_3 : DecidableEq.{succ u2} ι] (f : ι -> α) {p : (Finset.{u2} ι) -> Prop} (s : Finset.{u2} ι), (p (EmptyCollection.emptyCollection.{u2} (Finset.{u2} ι) (Finset.hasEmptyc.{u2} ι))) -> (forall (a : ι) (s : Finset.{u2} ι), (Not (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) a s)) -> (forall (x : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) x s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (f x) (f a))) -> (p s) -> (p (Insert.insert.{u2, u2} ι (Finset.{u2} ι) (Finset.hasInsert.{u2} ι (fun (a : ι) (b : ι) => _inst_3 a b)) a s))) -> (p s)
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_3 : DecidableEq.{succ u2} ι] (f : ι -> α) {p : (Finset.{u2} ι) -> Prop} (s : Finset.{u2} ι), (p (EmptyCollection.emptyCollection.{u2} (Finset.{u2} ι) (Finset.instEmptyCollectionFinset.{u2} ι))) -> (forall (a : ι) (s : Finset.{u2} ι), (Not (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) a s)) -> (forall (x : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) x s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (f x) (f a))) -> (p s) -> (p (Insert.insert.{u2, u2} ι (Finset.{u2} ι) (Finset.instInsertFinset.{u2} ι (fun (a : ι) (b : ι) => _inst_3 a b)) a s))) -> (p s)
Case conversion may be inaccurate. Consider using '#align finset.induction_on_max_value Finset.induction_on_max_valueₓ'. -/
/-- Induction principle for `finset`s in any type from which a given function `f` maps to a linearly
ordered type : a predicate is true on all `s : finset α` provided that:

* it is true on the empty `finset`,
* for every `s : finset α` and an element `a` such that for elements of `s` denoted by `x` we have
  `f x ≤ f a`, `p s` implies `p (insert a s)`. -/
@[elab_as_elim]
theorem induction_on_max_value [DecidableEq ι] (f : ι → α) {p : Finset ι → Prop} (s : Finset ι)
    (h0 : p ∅) (step : ∀ a s, a ∉ s → (∀ x ∈ s, f x ≤ f a) → p s → p (insert a s)) : p s :=
  by
  induction' s using Finset.strongInductionOn with s ihs
  rcases(s.image f).eq_empty_or_nonempty with (hne | hne)
  · simp only [image_eq_empty] at hne
    simp only [hne, h0]
  · have H : (s.image f).max' hne ∈ s.image f := max'_mem (s.image f) hne
    simp only [mem_image, exists_prop] at H
    rcases H with ⟨a, has, hfa⟩
    rw [← insert_erase has]
    refine' step _ _ (not_mem_erase a s) (fun x hx => _) (ihs _ <| erase_ssubset has)
    rw [hfa]
    exact le_max' _ _ (mem_image_of_mem _ <| mem_of_mem_erase hx)
#align finset.induction_on_max_value Finset.induction_on_max_value

/- warning: finset.induction_on_min_value -> Finset.induction_on_min_value is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_3 : DecidableEq.{succ u2} ι] (f : ι -> α) {p : (Finset.{u2} ι) -> Prop} (s : Finset.{u2} ι), (p (EmptyCollection.emptyCollection.{u2} (Finset.{u2} ι) (Finset.hasEmptyc.{u2} ι))) -> (forall (a : ι) (s : Finset.{u2} ι), (Not (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) a s)) -> (forall (x : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) x s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (f a) (f x))) -> (p s) -> (p (Insert.insert.{u2, u2} ι (Finset.{u2} ι) (Finset.hasInsert.{u2} ι (fun (a : ι) (b : ι) => _inst_3 a b)) a s))) -> (p s)
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_3 : DecidableEq.{succ u2} ι] (f : ι -> α) {p : (Finset.{u2} ι) -> Prop} (s : Finset.{u2} ι), (p (EmptyCollection.emptyCollection.{u2} (Finset.{u2} ι) (Finset.instEmptyCollectionFinset.{u2} ι))) -> (forall (a : ι) (s : Finset.{u2} ι), (Not (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) a s)) -> (forall (x : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) x s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (f a) (f x))) -> (p s) -> (p (Insert.insert.{u2, u2} ι (Finset.{u2} ι) (Finset.instInsertFinset.{u2} ι (fun (a : ι) (b : ι) => _inst_3 a b)) a s))) -> (p s)
Case conversion may be inaccurate. Consider using '#align finset.induction_on_min_value Finset.induction_on_min_valueₓ'. -/
/-- Induction principle for `finset`s in any type from which a given function `f` maps to a linearly
ordered type : a predicate is true on all `s : finset α` provided that:

* it is true on the empty `finset`,
* for every `s : finset α` and an element `a` such that for elements of `s` denoted by `x` we have
  `f a ≤ f x`, `p s` implies `p (insert a s)`. -/
@[elab_as_elim]
theorem induction_on_min_value [DecidableEq ι] (f : ι → α) {p : Finset ι → Prop} (s : Finset ι)
    (h0 : p ∅) (step : ∀ a s, a ∉ s → (∀ x ∈ s, f a ≤ f x) → p s → p (insert a s)) : p s :=
  @induction_on_max_value αᵒᵈ ι _ _ _ _ s h0 step
#align finset.induction_on_min_value Finset.induction_on_min_value

end MaxMinInductionValue

section ExistsMaxMin

variable [LinearOrder α]

/- warning: finset.exists_max_image -> Finset.exists_max_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] (s : Finset.{u2} β) (f : β -> α), (Finset.Nonempty.{u2} β s) -> (Exists.{succ u2} β (fun (x : β) => Exists.{0} (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s) (fun (H : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s) => forall (x' : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x' s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (f x') (f x)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] (s : Finset.{u2} β) (f : β -> α), (Finset.Nonempty.{u2} β s) -> (Exists.{succ u2} β (fun (x : β) => And (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) x s) (forall (x' : β), (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) x' s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (f x') (f x)))))
Case conversion may be inaccurate. Consider using '#align finset.exists_max_image Finset.exists_max_imageₓ'. -/
theorem exists_max_image (s : Finset β) (f : β → α) (h : s.Nonempty) :
    ∃ x ∈ s, ∀ x' ∈ s, f x' ≤ f x :=
  by
  cases' max_of_nonempty (h.image f) with y hy
  rcases mem_image.mp (mem_of_max hy) with ⟨x, hx, rfl⟩
  exact ⟨x, hx, fun x' hx' => le_max_of_eq (mem_image_of_mem f hx') hy⟩
#align finset.exists_max_image Finset.exists_max_image

/- warning: finset.exists_min_image -> Finset.exists_min_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] (s : Finset.{u2} β) (f : β -> α), (Finset.Nonempty.{u2} β s) -> (Exists.{succ u2} β (fun (x : β) => Exists.{0} (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s) (fun (H : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s) => forall (x' : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x' s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (f x) (f x')))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] (s : Finset.{u2} β) (f : β -> α), (Finset.Nonempty.{u2} β s) -> (Exists.{succ u2} β (fun (x : β) => And (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) x s) (forall (x' : β), (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) x' s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (f x) (f x')))))
Case conversion may be inaccurate. Consider using '#align finset.exists_min_image Finset.exists_min_imageₓ'. -/
theorem exists_min_image (s : Finset β) (f : β → α) (h : s.Nonempty) :
    ∃ x ∈ s, ∀ x' ∈ s, f x ≤ f x' :=
  @exists_max_image αᵒᵈ β _ s f h
#align finset.exists_min_image Finset.exists_min_image

end ExistsMaxMin

#print Finset.is_glb_iff_is_least /-
theorem is_glb_iff_is_least [LinearOrder α] (i : α) (s : Finset α) (hs : s.Nonempty) :
    IsGLB (s : Set α) i ↔ IsLeast (↑s) i :=
  by
  refine' ⟨fun his => _, IsLeast.isGLB⟩
  suffices i = min' s hs by
    rw [this]
    exact is_least_min' s hs
  rw [IsGLB, IsGreatest, mem_lowerBounds, mem_upperBounds] at his
  exact le_antisymm (his.1 (Finset.min' s hs) (Finset.min'_mem s hs)) (his.2 _ (Finset.min'_le s))
#align finset.is_glb_iff_is_least Finset.is_glb_iff_is_least
-/

#print Finset.is_lub_iff_is_greatest /-
theorem is_lub_iff_is_greatest [LinearOrder α] (i : α) (s : Finset α) (hs : s.Nonempty) :
    IsLUB (s : Set α) i ↔ IsGreatest (↑s) i :=
  @is_glb_iff_is_least αᵒᵈ _ i s hs
#align finset.is_lub_iff_is_greatest Finset.is_lub_iff_is_greatest
-/

#print Finset.is_glb_mem /-
theorem is_glb_mem [LinearOrder α] {i : α} (s : Finset α) (his : IsGLB (s : Set α) i)
    (hs : s.Nonempty) : i ∈ s := by
  rw [← mem_coe]
  exact ((is_glb_iff_is_least i s hs).mp his).1
#align finset.is_glb_mem Finset.is_glb_mem
-/

#print Finset.is_lub_mem /-
theorem is_lub_mem [LinearOrder α] {i : α} (s : Finset α) (his : IsLUB (s : Set α) i)
    (hs : s.Nonempty) : i ∈ s :=
  @is_glb_mem αᵒᵈ _ i s his hs
#align finset.is_lub_mem Finset.is_lub_mem
-/

end Finset

namespace Multiset

/- warning: multiset.map_finset_sup -> Multiset.map_finset_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : DecidableEq.{succ u2} β] (s : Finset.{u3} γ) (f : γ -> (Multiset.{u2} β)) (g : β -> α), (Function.Injective.{succ u2, succ u1} β α g) -> (Eq.{succ u1} (Multiset.{u1} α) (Multiset.map.{u2, u1} β α g (Finset.sup.{u2, u3} (Multiset.{u2} β) γ (Lattice.toSemilatticeSup.{u2} (Multiset.{u2} β) (Multiset.lattice.{u2} β (fun (a : β) (b : β) => _inst_2 a b))) (Multiset.orderBot.{u2} β) s f)) (Finset.sup.{u1, u3} (Multiset.{u1} α) γ (Lattice.toSemilatticeSup.{u1} (Multiset.{u1} α) (Multiset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b))) (Multiset.orderBot.{u1} α) s (Function.comp.{succ u3, succ u2, succ u1} γ (Multiset.{u2} β) (Multiset.{u1} α) (Multiset.map.{u2, u1} β α g) f)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : DecidableEq.{succ u3} α] [_inst_2 : DecidableEq.{succ u2} β] (s : Finset.{u1} γ) (f : γ -> (Multiset.{u2} β)) (g : β -> α), (Function.Injective.{succ u2, succ u3} β α g) -> (Eq.{succ u3} (Multiset.{u3} α) (Multiset.map.{u2, u3} β α g (Finset.sup.{u2, u1} (Multiset.{u2} β) γ (Lattice.toSemilatticeSup.{u2} (Multiset.{u2} β) (Multiset.instLatticeMultiset.{u2} β (fun (a : β) (b : β) => _inst_2 a b))) (Multiset.instOrderBotMultisetToLEToPreorderInstPartialOrderMultiset.{u2} β) s f)) (Finset.sup.{u3, u1} (Multiset.{u3} α) γ (Lattice.toSemilatticeSup.{u3} (Multiset.{u3} α) (Multiset.instLatticeMultiset.{u3} α (fun (a : α) (b : α) => _inst_1 a b))) (Multiset.instOrderBotMultisetToLEToPreorderInstPartialOrderMultiset.{u3} α) s (Function.comp.{succ u1, succ u2, succ u3} γ (Multiset.{u2} β) (Multiset.{u3} α) (Multiset.map.{u2, u3} β α g) f)))
Case conversion may be inaccurate. Consider using '#align multiset.map_finset_sup Multiset.map_finset_supₓ'. -/
theorem map_finset_sup [DecidableEq α] [DecidableEq β] (s : Finset γ) (f : γ → Multiset β)
    (g : β → α) (hg : Function.Injective g) : map g (s.sup f) = s.sup (map g ∘ f) :=
  Finset.comp_sup_eq_sup_comp _ (fun _ _ => map_union hg) (map_zero _)
#align multiset.map_finset_sup Multiset.map_finset_sup

/- warning: multiset.count_finset_sup -> Multiset.count_finset_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] (s : Finset.{u1} α) (f : α -> (Multiset.{u2} β)) (b : β), Eq.{1} Nat (Multiset.count.{u2} β (fun (a : β) (b : β) => _inst_1 a b) b (Finset.sup.{u2, u1} (Multiset.{u2} β) α (Lattice.toSemilatticeSup.{u2} (Multiset.{u2} β) (Multiset.lattice.{u2} β (fun (a : β) (b : β) => _inst_1 a b))) (Multiset.orderBot.{u2} β) s f)) (Finset.sup.{0, u1} Nat α (CanonicallyLinearOrderedAddMonoid.semilatticeSup.{0} Nat Nat.canonicallyLinearOrderedAddMonoid) Nat.orderBot s (fun (a : α) => Multiset.count.{u2} β (fun (a : β) (b : β) => _inst_1 a b) b (f a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] (s : Finset.{u1} α) (f : α -> (Multiset.{u2} β)) (b : β), Eq.{1} Nat (Multiset.count.{u2} β (fun (a : β) (b : β) => _inst_1 a b) b (Finset.sup.{u2, u1} (Multiset.{u2} β) α (Lattice.toSemilatticeSup.{u2} (Multiset.{u2} β) (Multiset.instLatticeMultiset.{u2} β (fun (a : β) (b : β) => _inst_1 a b))) (Multiset.instOrderBotMultisetToLEToPreorderInstPartialOrderMultiset.{u2} β) s f)) (Finset.sup.{0, u1} Nat α (Lattice.toSemilatticeSup.{0} Nat (DistribLattice.toLattice.{0} Nat instDistribLatticeNat)) Nat.orderBot s (fun (a : α) => Multiset.count.{u2} β (fun (a : β) (b : β) => _inst_1 a b) b (f a)))
Case conversion may be inaccurate. Consider using '#align multiset.count_finset_sup Multiset.count_finset_supₓ'. -/
theorem count_finset_sup [DecidableEq β] (s : Finset α) (f : α → Multiset β) (b : β) :
    count b (s.sup f) = s.sup fun a => count b (f a) :=
  by
  letI := Classical.decEq α
  refine' s.induction _ _
  · exact count_zero _
  · intro i s his ih
    rw [Finset.sup_insert, sup_eq_union, count_union, Finset.sup_insert, ih]
    rfl
#align multiset.count_finset_sup Multiset.count_finset_sup

/- warning: multiset.mem_sup -> Multiset.mem_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] {s : Finset.{u1} α} {f : α -> (Multiset.{u2} β)} {x : β}, Iff (Membership.Mem.{u2, u2} β (Multiset.{u2} β) (Multiset.hasMem.{u2} β) x (Finset.sup.{u2, u1} (Multiset.{u2} β) α (Lattice.toSemilatticeSup.{u2} (Multiset.{u2} β) (Multiset.lattice.{u2} β (fun (a : β) (b : β) => _inst_1 a b))) (Multiset.orderBot.{u2} β) s f)) (Exists.{succ u1} α (fun (v : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) v s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) v s) => Membership.Mem.{u2, u2} β (Multiset.{u2} β) (Multiset.hasMem.{u2} β) x (f v))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] {s : Finset.{u2} α} {f : α -> (Multiset.{u1} β)} {x : β}, Iff (Membership.mem.{u1, u1} β (Multiset.{u1} β) (Multiset.instMembershipMultiset.{u1} β) x (Finset.sup.{u1, u2} (Multiset.{u1} β) α (Lattice.toSemilatticeSup.{u1} (Multiset.{u1} β) (Multiset.instLatticeMultiset.{u1} β (fun (a : β) (b : β) => _inst_1 a b))) (Multiset.instOrderBotMultisetToLEToPreorderInstPartialOrderMultiset.{u1} β) s f)) (Exists.{succ u2} α (fun (v : α) => And (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) v s) (Membership.mem.{u1, u1} β (Multiset.{u1} β) (Multiset.instMembershipMultiset.{u1} β) x (f v))))
Case conversion may be inaccurate. Consider using '#align multiset.mem_sup Multiset.mem_supₓ'. -/
theorem mem_sup {α β} [DecidableEq β] {s : Finset α} {f : α → Multiset β} {x : β} :
    x ∈ s.sup f ↔ ∃ v ∈ s, x ∈ f v := by
  classical
    apply s.induction_on
    · simp
    · intro a s has hxs
      rw [Finset.sup_insert, Multiset.sup_eq_union, Multiset.mem_union]
      constructor
      · intro hxi
        cases' hxi with hf hf
        · refine' ⟨a, _, hf⟩
          simp only [true_or_iff, eq_self_iff_true, Finset.mem_insert]
        · rcases hxs.mp hf with ⟨v, hv, hfv⟩
          refine' ⟨v, _, hfv⟩
          simp only [hv, or_true_iff, Finset.mem_insert]
      · rintro ⟨v, hv, hfv⟩
        rw [Finset.mem_insert] at hv
        rcases hv with (rfl | hv)
        · exact Or.inl hfv
        · refine' Or.inr (hxs.mpr ⟨v, hv, hfv⟩)
#align multiset.mem_sup Multiset.mem_sup

end Multiset

namespace Finset

/- warning: finset.mem_sup -> Finset.mem_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] {s : Finset.{u1} α} {f : α -> (Finset.{u2} β)} {x : β}, Iff (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x (Finset.sup.{u2, u1} (Finset.{u2} β) α (Lattice.toSemilatticeSup.{u2} (Finset.{u2} β) (Finset.lattice.{u2} β (fun (a : β) (b : β) => _inst_1 a b))) (Finset.orderBot.{u2} β) s f)) (Exists.{succ u1} α (fun (v : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) v s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) v s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x (f v))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] {s : Finset.{u2} α} {f : α -> (Finset.{u1} β)} {x : β}, Iff (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) x (Finset.sup.{u1, u2} (Finset.{u1} β) α (Lattice.toSemilatticeSup.{u1} (Finset.{u1} β) (Finset.instLatticeFinset.{u1} β (fun (a : β) (b : β) => _inst_1 a b))) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} β) s f)) (Exists.{succ u2} α (fun (v : α) => And (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) v s) (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) x (f v))))
Case conversion may be inaccurate. Consider using '#align finset.mem_sup Finset.mem_supₓ'. -/
theorem mem_sup {α β} [DecidableEq β] {s : Finset α} {f : α → Finset β} {x : β} :
    x ∈ s.sup f ↔ ∃ v ∈ s, x ∈ f v :=
  by
  change _ ↔ ∃ v ∈ s, x ∈ (f v).val
  rw [← Multiset.mem_sup, ← Multiset.mem_toFinset, sup_to_finset]
  simp_rw [val_to_finset]
#align finset.mem_sup Finset.mem_sup

/- warning: finset.sup_eq_bUnion -> Finset.sup_eq_biUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] (s : Finset.{u1} α) (t : α -> (Finset.{u2} β)), Eq.{succ u2} (Finset.{u2} β) (Finset.sup.{u2, u1} (Finset.{u2} β) α (Lattice.toSemilatticeSup.{u2} (Finset.{u2} β) (Finset.lattice.{u2} β (fun (a : β) (b : β) => _inst_1 a b))) (Finset.orderBot.{u2} β) s t) (Finset.biUnion.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] (s : Finset.{u2} α) (t : α -> (Finset.{u1} β)), Eq.{succ u1} (Finset.{u1} β) (Finset.sup.{u1, u2} (Finset.{u1} β) α (Lattice.toSemilatticeSup.{u1} (Finset.{u1} β) (Finset.instLatticeFinset.{u1} β (fun (a : β) (b : β) => _inst_1 a b))) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} β) s t) (Finset.biUnion.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) s t)
Case conversion may be inaccurate. Consider using '#align finset.sup_eq_bUnion Finset.sup_eq_biUnionₓ'. -/
theorem sup_eq_biUnion {α β} [DecidableEq β] (s : Finset α) (t : α → Finset β) :
    s.sup t = s.biUnion t := by
  ext
  rw [mem_sup, mem_bUnion]
#align finset.sup_eq_bUnion Finset.sup_eq_biUnion

/- warning: finset.sup_singleton'' -> Finset.sup_singleton'' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u2} β) (f : β -> α), Eq.{succ u1} (Finset.{u1} α) (Finset.sup.{u1, u2} (Finset.{u1} α) β (Lattice.toSemilatticeSup.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b))) (Finset.orderBot.{u1} α) s (fun (b : β) => Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) (f b))) (Finset.image.{u2, u1} β α (fun (a : α) (b : α) => _inst_1 a b) f s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] (s : Finset.{u1} β) (f : β -> α), Eq.{succ u2} (Finset.{u2} α) (Finset.sup.{u2, u1} (Finset.{u2} α) β (Lattice.toSemilatticeSup.{u2} (Finset.{u2} α) (Finset.instLatticeFinset.{u2} α (fun (a : α) (b : α) => _inst_1 a b))) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} α) s (fun (b : β) => Singleton.singleton.{u2, u2} α (Finset.{u2} α) (Finset.instSingletonFinset.{u2} α) (f b))) (Finset.image.{u1, u2} β α (fun (a : α) (b : α) => _inst_1 a b) f s)
Case conversion may be inaccurate. Consider using '#align finset.sup_singleton'' Finset.sup_singleton''ₓ'. -/
@[simp]
theorem sup_singleton'' [DecidableEq α] (s : Finset β) (f : β → α) :
    (s.sup fun b => {f b}) = s.image f := by
  ext a
  rw [mem_sup, mem_image]
  simp only [mem_singleton, eq_comm]
#align finset.sup_singleton'' Finset.sup_singleton''

/- warning: finset.sup_singleton' -> Finset.sup_singleton' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (Finset.sup.{u1, u1} (Finset.{u1} α) α (Lattice.toSemilatticeSup.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b))) (Finset.orderBot.{u1} α) s (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α))) s
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (Finset.sup.{u1, u1} (Finset.{u1} α) α (Lattice.toSemilatticeSup.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b))) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α))) s
Case conversion may be inaccurate. Consider using '#align finset.sup_singleton' Finset.sup_singleton'ₓ'. -/
@[simp]
theorem sup_singleton' [DecidableEq α] (s : Finset α) : s.sup singleton = s :=
  (s.sup_singleton'' _).trans image_id
#align finset.sup_singleton' Finset.sup_singleton'

end Finset

section Lattice

variable {ι' : Sort _} [CompleteLattice α]

/- warning: supr_eq_supr_finset -> iSup_eq_iSup_finset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] (s : ι -> α), Eq.{succ u1} α (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => s i)) (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Finset.{u2} ι) (fun (t : Finset.{u2} ι) => iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i t) (fun (H : Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i t) => s i))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] (s : ι -> α), Eq.{succ u2} α (iSup.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => s i)) (iSup.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) (Finset.{u1} ι) (fun (t : Finset.{u1} ι) => iSup.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => iSup.{u2, 0} α (CompleteLattice.toSupSet.{u2} α _inst_1) (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i t) (fun (H : Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i t) => s i))))
Case conversion may be inaccurate. Consider using '#align supr_eq_supr_finset iSup_eq_iSup_finsetₓ'. -/
/-- Supremum of `s i`, `i : ι`, is equal to the supremum over `t : finset ι` of suprema
`⨆ i ∈ t, s i`. This version assumes `ι` is a `Type*`. See `supr_eq_supr_finset'` for a version
that works for `ι : Sort*`. -/
theorem iSup_eq_iSup_finset (s : ι → α) : (⨆ i, s i) = ⨆ t : Finset ι, ⨆ i ∈ t, s i := by
  classical exact
      le_antisymm
        (iSup_le fun b => le_iSup_of_le {b} <| le_iSup_of_le b <| le_iSup_of_le (by simp) <| le_rfl)
        (iSup_le fun t => iSup_le fun b => iSup_le fun hb => le_iSup _ _)
#align supr_eq_supr_finset iSup_eq_iSup_finset

/- warning: supr_eq_supr_finset' -> iSup_eq_iSup_finset' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι' : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (s : ι' -> α), Eq.{succ u1} α (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι' (fun (i : ι') => s i)) (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Finset.{u2} (PLift.{u2} ι')) (fun (t : Finset.{u2} (PLift.{u2} ι')) => iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (PLift.{u2} ι') (fun (i : PLift.{u2} ι') => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} (PLift.{u2} ι') (Finset.{u2} (PLift.{u2} ι')) (Finset.hasMem.{u2} (PLift.{u2} ι')) i t) (fun (H : Membership.Mem.{u2, u2} (PLift.{u2} ι') (Finset.{u2} (PLift.{u2} ι')) (Finset.hasMem.{u2} (PLift.{u2} ι')) i t) => s (PLift.down.{u2} ι' i)))))
but is expected to have type
  forall {α : Type.{u2}} {ι' : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (s : ι' -> α), Eq.{succ u2} α (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι' (fun (i : ι') => s i)) (iSup.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) (Finset.{u1} (PLift.{u1} ι')) (fun (t : Finset.{u1} (PLift.{u1} ι')) => iSup.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) (PLift.{u1} ι') (fun (i : PLift.{u1} ι') => iSup.{u2, 0} α (CompleteLattice.toSupSet.{u2} α _inst_1) (Membership.mem.{u1, u1} (PLift.{u1} ι') (Finset.{u1} (PLift.{u1} ι')) (Finset.instMembershipFinset.{u1} (PLift.{u1} ι')) i t) (fun (H : Membership.mem.{u1, u1} (PLift.{u1} ι') (Finset.{u1} (PLift.{u1} ι')) (Finset.instMembershipFinset.{u1} (PLift.{u1} ι')) i t) => s (PLift.down.{u1} ι' i)))))
Case conversion may be inaccurate. Consider using '#align supr_eq_supr_finset' iSup_eq_iSup_finset'ₓ'. -/
/-- Supremum of `s i`, `i : ι`, is equal to the supremum over `t : finset ι` of suprema
`⨆ i ∈ t, s i`. This version works for `ι : Sort*`. See `supr_eq_supr_finset` for a version
that assumes `ι : Type*` but has no `plift`s. -/
theorem iSup_eq_iSup_finset' (s : ι' → α) :
    (⨆ i, s i) = ⨆ t : Finset (PLift ι'), ⨆ i ∈ t, s (PLift.down i) := by
  rw [← iSup_eq_iSup_finset, ← equiv.plift.surjective.supr_comp] <;> rfl
#align supr_eq_supr_finset' iSup_eq_iSup_finset'

/- warning: infi_eq_infi_finset -> iInf_eq_iInf_finset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] (s : ι -> α), Eq.{succ u1} α (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => s i)) (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Finset.{u2} ι) (fun (t : Finset.{u2} ι) => iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i t) (fun (H : Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i t) => s i))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] (s : ι -> α), Eq.{succ u2} α (iInf.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => s i)) (iInf.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) (Finset.{u1} ι) (fun (t : Finset.{u1} ι) => iInf.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => iInf.{u2, 0} α (CompleteLattice.toInfSet.{u2} α _inst_1) (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i t) (fun (H : Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i t) => s i))))
Case conversion may be inaccurate. Consider using '#align infi_eq_infi_finset iInf_eq_iInf_finsetₓ'. -/
/-- Infimum of `s i`, `i : ι`, is equal to the infimum over `t : finset ι` of infima
`⨅ i ∈ t, s i`. This version assumes `ι` is a `Type*`. See `infi_eq_infi_finset'` for a version
that works for `ι : Sort*`. -/
theorem iInf_eq_iInf_finset (s : ι → α) : (⨅ i, s i) = ⨅ (t : Finset ι) (i ∈ t), s i :=
  @iSup_eq_iSup_finset αᵒᵈ _ _ _
#align infi_eq_infi_finset iInf_eq_iInf_finset

/- warning: infi_eq_infi_finset' -> iInf_eq_iInf_finset' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι' : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (s : ι' -> α), Eq.{succ u1} α (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι' (fun (i : ι') => s i)) (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Finset.{u2} (PLift.{u2} ι')) (fun (t : Finset.{u2} (PLift.{u2} ι')) => iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (PLift.{u2} ι') (fun (i : PLift.{u2} ι') => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} (PLift.{u2} ι') (Finset.{u2} (PLift.{u2} ι')) (Finset.hasMem.{u2} (PLift.{u2} ι')) i t) (fun (H : Membership.Mem.{u2, u2} (PLift.{u2} ι') (Finset.{u2} (PLift.{u2} ι')) (Finset.hasMem.{u2} (PLift.{u2} ι')) i t) => s (PLift.down.{u2} ι' i)))))
but is expected to have type
  forall {α : Type.{u2}} {ι' : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (s : ι' -> α), Eq.{succ u2} α (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι' (fun (i : ι') => s i)) (iInf.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) (Finset.{u1} (PLift.{u1} ι')) (fun (t : Finset.{u1} (PLift.{u1} ι')) => iInf.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) (PLift.{u1} ι') (fun (i : PLift.{u1} ι') => iInf.{u2, 0} α (CompleteLattice.toInfSet.{u2} α _inst_1) (Membership.mem.{u1, u1} (PLift.{u1} ι') (Finset.{u1} (PLift.{u1} ι')) (Finset.instMembershipFinset.{u1} (PLift.{u1} ι')) i t) (fun (H : Membership.mem.{u1, u1} (PLift.{u1} ι') (Finset.{u1} (PLift.{u1} ι')) (Finset.instMembershipFinset.{u1} (PLift.{u1} ι')) i t) => s (PLift.down.{u1} ι' i)))))
Case conversion may be inaccurate. Consider using '#align infi_eq_infi_finset' iInf_eq_iInf_finset'ₓ'. -/
/-- Infimum of `s i`, `i : ι`, is equal to the infimum over `t : finset ι` of infima
`⨅ i ∈ t, s i`. This version works for `ι : Sort*`. See `infi_eq_infi_finset` for a version
that assumes `ι : Type*` but has no `plift`s. -/
theorem iInf_eq_iInf_finset' (s : ι' → α) :
    (⨅ i, s i) = ⨅ t : Finset (PLift ι'), ⨅ i ∈ t, s (PLift.down i) :=
  @iSup_eq_iSup_finset' αᵒᵈ _ _ _
#align infi_eq_infi_finset' iInf_eq_iInf_finset'

end Lattice

namespace Set

variable {ι' : Sort _}

/- warning: set.Union_eq_Union_finset -> Set.iUnion_eq_iUnion_finset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} (s : ι -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.iUnion.{u1, succ u2} α ι (fun (i : ι) => s i)) (Set.iUnion.{u1, succ u2} α (Finset.{u2} ι) (fun (t : Finset.{u2} ι) => Set.iUnion.{u1, succ u2} α ι (fun (i : ι) => Set.iUnion.{u1, 0} α (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i t) (fun (H : Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i t) => s i))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} (s : ι -> (Set.{u2} α)), Eq.{succ u2} (Set.{u2} α) (Set.iUnion.{u2, succ u1} α ι (fun (i : ι) => s i)) (Set.iUnion.{u2, succ u1} α (Finset.{u1} ι) (fun (t : Finset.{u1} ι) => Set.iUnion.{u2, succ u1} α ι (fun (i : ι) => Set.iUnion.{u2, 0} α (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i t) (fun (H : Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i t) => s i))))
Case conversion may be inaccurate. Consider using '#align set.Union_eq_Union_finset Set.iUnion_eq_iUnion_finsetₓ'. -/
/-- Union of an indexed family of sets `s : ι → set α` is equal to the union of the unions
of finite subfamilies. This version assumes `ι : Type*`. See also `Union_eq_Union_finset'` for
a version that works for `ι : Sort*`. -/
theorem iUnion_eq_iUnion_finset (s : ι → Set α) : (⋃ i, s i) = ⋃ t : Finset ι, ⋃ i ∈ t, s i :=
  iSup_eq_iSup_finset s
#align set.Union_eq_Union_finset Set.iUnion_eq_iUnion_finset

/- warning: set.Union_eq_Union_finset' -> Set.iUnion_eq_iUnion_finset' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι' : Sort.{u2}} (s : ι' -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.iUnion.{u1, u2} α ι' (fun (i : ι') => s i)) (Set.iUnion.{u1, succ u2} α (Finset.{u2} (PLift.{u2} ι')) (fun (t : Finset.{u2} (PLift.{u2} ι')) => Set.iUnion.{u1, succ u2} α (PLift.{u2} ι') (fun (i : PLift.{u2} ι') => Set.iUnion.{u1, 0} α (Membership.Mem.{u2, u2} (PLift.{u2} ι') (Finset.{u2} (PLift.{u2} ι')) (Finset.hasMem.{u2} (PLift.{u2} ι')) i t) (fun (H : Membership.Mem.{u2, u2} (PLift.{u2} ι') (Finset.{u2} (PLift.{u2} ι')) (Finset.hasMem.{u2} (PLift.{u2} ι')) i t) => s (PLift.down.{u2} ι' i)))))
but is expected to have type
  forall {α : Type.{u2}} {ι' : Sort.{u1}} (s : ι' -> (Set.{u2} α)), Eq.{succ u2} (Set.{u2} α) (Set.iUnion.{u2, u1} α ι' (fun (i : ι') => s i)) (Set.iUnion.{u2, succ u1} α (Finset.{u1} (PLift.{u1} ι')) (fun (t : Finset.{u1} (PLift.{u1} ι')) => Set.iUnion.{u2, succ u1} α (PLift.{u1} ι') (fun (i : PLift.{u1} ι') => Set.iUnion.{u2, 0} α (Membership.mem.{u1, u1} (PLift.{u1} ι') (Finset.{u1} (PLift.{u1} ι')) (Finset.instMembershipFinset.{u1} (PLift.{u1} ι')) i t) (fun (H : Membership.mem.{u1, u1} (PLift.{u1} ι') (Finset.{u1} (PLift.{u1} ι')) (Finset.instMembershipFinset.{u1} (PLift.{u1} ι')) i t) => s (PLift.down.{u1} ι' i)))))
Case conversion may be inaccurate. Consider using '#align set.Union_eq_Union_finset' Set.iUnion_eq_iUnion_finset'ₓ'. -/
/-- Union of an indexed family of sets `s : ι → set α` is equal to the union of the unions
of finite subfamilies. This version works for `ι : Sort*`. See also `Union_eq_Union_finset` for
a version that assumes `ι : Type*` but avoids `plift`s in the right hand side. -/
theorem iUnion_eq_iUnion_finset' (s : ι' → Set α) :
    (⋃ i, s i) = ⋃ t : Finset (PLift ι'), ⋃ i ∈ t, s (PLift.down i) :=
  iSup_eq_iSup_finset' s
#align set.Union_eq_Union_finset' Set.iUnion_eq_iUnion_finset'

/- warning: set.Inter_eq_Inter_finset -> Set.iInter_eq_iInter_finset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} (s : ι -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.iInter.{u1, succ u2} α ι (fun (i : ι) => s i)) (Set.iInter.{u1, succ u2} α (Finset.{u2} ι) (fun (t : Finset.{u2} ι) => Set.iInter.{u1, succ u2} α ι (fun (i : ι) => Set.iInter.{u1, 0} α (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i t) (fun (H : Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i t) => s i))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} (s : ι -> (Set.{u2} α)), Eq.{succ u2} (Set.{u2} α) (Set.iInter.{u2, succ u1} α ι (fun (i : ι) => s i)) (Set.iInter.{u2, succ u1} α (Finset.{u1} ι) (fun (t : Finset.{u1} ι) => Set.iInter.{u2, succ u1} α ι (fun (i : ι) => Set.iInter.{u2, 0} α (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i t) (fun (H : Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i t) => s i))))
Case conversion may be inaccurate. Consider using '#align set.Inter_eq_Inter_finset Set.iInter_eq_iInter_finsetₓ'. -/
/-- Intersection of an indexed family of sets `s : ι → set α` is equal to the intersection of the
intersections of finite subfamilies. This version assumes `ι : Type*`. See also
`Inter_eq_Inter_finset'` for a version that works for `ι : Sort*`. -/
theorem iInter_eq_iInter_finset (s : ι → Set α) : (⋂ i, s i) = ⋂ t : Finset ι, ⋂ i ∈ t, s i :=
  iInf_eq_iInf_finset s
#align set.Inter_eq_Inter_finset Set.iInter_eq_iInter_finset

/- warning: set.Inter_eq_Inter_finset' -> Set.iInter_eq_iInter_finset' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι' : Sort.{u2}} (s : ι' -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.iInter.{u1, u2} α ι' (fun (i : ι') => s i)) (Set.iInter.{u1, succ u2} α (Finset.{u2} (PLift.{u2} ι')) (fun (t : Finset.{u2} (PLift.{u2} ι')) => Set.iInter.{u1, succ u2} α (PLift.{u2} ι') (fun (i : PLift.{u2} ι') => Set.iInter.{u1, 0} α (Membership.Mem.{u2, u2} (PLift.{u2} ι') (Finset.{u2} (PLift.{u2} ι')) (Finset.hasMem.{u2} (PLift.{u2} ι')) i t) (fun (H : Membership.Mem.{u2, u2} (PLift.{u2} ι') (Finset.{u2} (PLift.{u2} ι')) (Finset.hasMem.{u2} (PLift.{u2} ι')) i t) => s (PLift.down.{u2} ι' i)))))
but is expected to have type
  forall {α : Type.{u2}} {ι' : Sort.{u1}} (s : ι' -> (Set.{u2} α)), Eq.{succ u2} (Set.{u2} α) (Set.iInter.{u2, u1} α ι' (fun (i : ι') => s i)) (Set.iInter.{u2, succ u1} α (Finset.{u1} (PLift.{u1} ι')) (fun (t : Finset.{u1} (PLift.{u1} ι')) => Set.iInter.{u2, succ u1} α (PLift.{u1} ι') (fun (i : PLift.{u1} ι') => Set.iInter.{u2, 0} α (Membership.mem.{u1, u1} (PLift.{u1} ι') (Finset.{u1} (PLift.{u1} ι')) (Finset.instMembershipFinset.{u1} (PLift.{u1} ι')) i t) (fun (H : Membership.mem.{u1, u1} (PLift.{u1} ι') (Finset.{u1} (PLift.{u1} ι')) (Finset.instMembershipFinset.{u1} (PLift.{u1} ι')) i t) => s (PLift.down.{u1} ι' i)))))
Case conversion may be inaccurate. Consider using '#align set.Inter_eq_Inter_finset' Set.iInter_eq_iInter_finset'ₓ'. -/
/-- Intersection of an indexed family of sets `s : ι → set α` is equal to the intersection of the
intersections of finite subfamilies. This version works for `ι : Sort*`. See also
`Inter_eq_Inter_finset` for a version that assumes `ι : Type*` but avoids `plift`s in the right
hand side. -/
theorem iInter_eq_iInter_finset' (s : ι' → Set α) :
    (⋂ i, s i) = ⋂ t : Finset (PLift ι'), ⋂ i ∈ t, s (PLift.down i) :=
  iInf_eq_iInf_finset' s
#align set.Inter_eq_Inter_finset' Set.iInter_eq_iInter_finset'

end Set

namespace Finset

/-! ### Interaction with ordered algebra structures -/


/- warning: finset.sup_mul_le_mul_sup_of_nonneg -> Finset.sup_mul_le_mul_sup_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : LinearOrderedSemiring.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1)))))] {a : ι -> α} {b : ι -> α} (s : Finset.{u2} ι), (forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1))))))))) (a i))) -> (forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1))))))))) (b i))) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1))))) (Finset.sup.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (LinearOrder.toLattice.{u1} α (LinearOrderedAddCommMonoid.toLinearOrder.{u1} α (LinearOrderedSemiring.toLinearOrderedAddCommMonoid.{u1} α _inst_1)))) _inst_2 s (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (ι -> α) (ι -> α) (ι -> α) (instHMul.{max u2 u1} (ι -> α) (Pi.instMul.{u2, u1} ι (fun (ᾰ : ι) => α) (fun (i : ι) => Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1)))))))) a b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1))))))) (Finset.sup.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (LinearOrder.toLattice.{u1} α (LinearOrderedAddCommMonoid.toLinearOrder.{u1} α (LinearOrderedSemiring.toLinearOrderedAddCommMonoid.{u1} α _inst_1)))) _inst_2 s a) (Finset.sup.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (LinearOrder.toLattice.{u1} α (LinearOrderedAddCommMonoid.toLinearOrder.{u1} α (LinearOrderedSemiring.toLinearOrderedAddCommMonoid.{u1} α _inst_1)))) _inst_2 s b)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : LinearOrderedSemiring.{u2} α] [_inst_2 : OrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (StrictOrderedSemiring.toPartialOrder.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α _inst_1))))] {a : ι -> α} {b : ι -> α} (s : Finset.{u1} ι), (forall (i : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (StrictOrderedSemiring.toPartialOrder.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α _inst_1)))) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α (StrictOrderedSemiring.toSemiring.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α _inst_1)))))) (a i))) -> (forall (i : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (StrictOrderedSemiring.toPartialOrder.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α _inst_1)))) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α (StrictOrderedSemiring.toSemiring.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α _inst_1)))))) (b i))) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (StrictOrderedSemiring.toPartialOrder.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α _inst_1)))) (Finset.sup.{u2, u1} α ι (Lattice.toSemilatticeSup.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α (LinearOrderedAddCommMonoid.toLinearOrder.{u2} α (LinearOrderedSemiring.toLinearOrderedAddCommMonoid.{u2} α _inst_1))))) _inst_2 s (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (ι -> α) (ι -> α) (ι -> α) (instHMul.{max u2 u1} (ι -> α) (Pi.instMul.{u1, u2} ι (fun (ᾰ : ι) => α) (fun (i : ι) => NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (StrictOrderedSemiring.toSemiring.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α _inst_1))))))) a b)) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (StrictOrderedSemiring.toSemiring.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α _inst_1)))))) (Finset.sup.{u2, u1} α ι (Lattice.toSemilatticeSup.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α (LinearOrderedAddCommMonoid.toLinearOrder.{u2} α (LinearOrderedSemiring.toLinearOrderedAddCommMonoid.{u2} α _inst_1))))) _inst_2 s a) (Finset.sup.{u2, u1} α ι (Lattice.toSemilatticeSup.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α (LinearOrderedAddCommMonoid.toLinearOrder.{u2} α (LinearOrderedSemiring.toLinearOrderedAddCommMonoid.{u2} α _inst_1))))) _inst_2 s b)))
Case conversion may be inaccurate. Consider using '#align finset.sup_mul_le_mul_sup_of_nonneg Finset.sup_mul_le_mul_sup_of_nonnegₓ'. -/
theorem sup_mul_le_mul_sup_of_nonneg [LinearOrderedSemiring α] [OrderBot α] {a b : ι → α}
    (s : Finset ι) (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) :
    s.sup (a * b) ≤ s.sup a * s.sup b :=
  Finset.sup_le fun i hi =>
    mul_le_mul (le_sup hi) (le_sup hi) (hb _ hi) ((ha _ hi).trans <| le_sup hi)
#align finset.sup_mul_le_mul_sup_of_nonneg Finset.sup_mul_le_mul_sup_of_nonneg

/- warning: finset.mul_inf_le_inf_mul_of_nonneg -> Finset.mul_inf_le_inf_mul_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : LinearOrderedSemiring.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1)))))] {a : ι -> α} {b : ι -> α} (s : Finset.{u2} ι), (forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1))))))))) (a i))) -> (forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1))))))))) (b i))) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1))))))) (Finset.inf.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α (LinearOrderedAddCommMonoid.toLinearOrder.{u1} α (LinearOrderedSemiring.toLinearOrderedAddCommMonoid.{u1} α _inst_1)))) _inst_2 s a) (Finset.inf.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α (LinearOrderedAddCommMonoid.toLinearOrder.{u1} α (LinearOrderedSemiring.toLinearOrderedAddCommMonoid.{u1} α _inst_1)))) _inst_2 s b)) (Finset.inf.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α (LinearOrderedAddCommMonoid.toLinearOrder.{u1} α (LinearOrderedSemiring.toLinearOrderedAddCommMonoid.{u1} α _inst_1)))) _inst_2 s (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (ι -> α) (ι -> α) (ι -> α) (instHMul.{max u2 u1} (ι -> α) (Pi.instMul.{u2, u1} ι (fun (ᾰ : ι) => α) (fun (i : ι) => Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1)))))))) a b)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : LinearOrderedSemiring.{u2} α] [_inst_2 : OrderTop.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (StrictOrderedSemiring.toPartialOrder.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α _inst_1))))] {a : ι -> α} {b : ι -> α} (s : Finset.{u1} ι), (forall (i : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (StrictOrderedSemiring.toPartialOrder.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α _inst_1)))) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α (StrictOrderedSemiring.toSemiring.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α _inst_1)))))) (a i))) -> (forall (i : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (StrictOrderedSemiring.toPartialOrder.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α _inst_1)))) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α (StrictOrderedSemiring.toSemiring.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α _inst_1)))))) (b i))) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (StrictOrderedSemiring.toPartialOrder.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α _inst_1)))) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (StrictOrderedSemiring.toSemiring.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α _inst_1)))))) (Finset.inf.{u2, u1} α ι (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α (LinearOrderedAddCommMonoid.toLinearOrder.{u2} α (LinearOrderedSemiring.toLinearOrderedAddCommMonoid.{u2} α _inst_1))))) _inst_2 s a) (Finset.inf.{u2, u1} α ι (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α (LinearOrderedAddCommMonoid.toLinearOrder.{u2} α (LinearOrderedSemiring.toLinearOrderedAddCommMonoid.{u2} α _inst_1))))) _inst_2 s b)) (Finset.inf.{u2, u1} α ι (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α (LinearOrderedAddCommMonoid.toLinearOrder.{u2} α (LinearOrderedSemiring.toLinearOrderedAddCommMonoid.{u2} α _inst_1))))) _inst_2 s (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (ι -> α) (ι -> α) (ι -> α) (instHMul.{max u2 u1} (ι -> α) (Pi.instMul.{u1, u2} ι (fun (ᾰ : ι) => α) (fun (i : ι) => NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (StrictOrderedSemiring.toSemiring.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α _inst_1))))))) a b)))
Case conversion may be inaccurate. Consider using '#align finset.mul_inf_le_inf_mul_of_nonneg Finset.mul_inf_le_inf_mul_of_nonnegₓ'. -/
theorem mul_inf_le_inf_mul_of_nonneg [LinearOrderedSemiring α] [OrderTop α] {a b : ι → α}
    (s : Finset ι) (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) :
    s.inf a * s.inf b ≤ s.inf (a * b) :=
  Finset.le_inf fun i hi => mul_le_mul (inf_le hi) (inf_le hi) (Finset.le_inf hb) (ha i hi)
#align finset.mul_inf_le_inf_mul_of_nonneg Finset.mul_inf_le_inf_mul_of_nonneg

/- warning: finset.sup'_mul_le_mul_sup'_of_nonneg -> Finset.sup'_mul_le_mul_sup'_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : LinearOrderedSemiring.{u1} α] {a : ι -> α} {b : ι -> α} (s : Finset.{u2} ι) (H : Finset.Nonempty.{u2} ι s), (forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1))))))))) (a i))) -> (forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1))))))))) (b i))) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1))))) (Finset.sup'.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (LinearOrder.toLattice.{u1} α (LinearOrderedAddCommMonoid.toLinearOrder.{u1} α (LinearOrderedSemiring.toLinearOrderedAddCommMonoid.{u1} α _inst_1)))) s H (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (ι -> α) (ι -> α) (ι -> α) (instHMul.{max u2 u1} (ι -> α) (Pi.instMul.{u2, u1} ι (fun (ᾰ : ι) => α) (fun (i : ι) => Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1)))))))) a b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1))))))) (Finset.sup'.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (LinearOrder.toLattice.{u1} α (LinearOrderedAddCommMonoid.toLinearOrder.{u1} α (LinearOrderedSemiring.toLinearOrderedAddCommMonoid.{u1} α _inst_1)))) s H a) (Finset.sup'.{u1, u2} α ι (Lattice.toSemilatticeSup.{u1} α (LinearOrder.toLattice.{u1} α (LinearOrderedAddCommMonoid.toLinearOrder.{u1} α (LinearOrderedSemiring.toLinearOrderedAddCommMonoid.{u1} α _inst_1)))) s H b)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : LinearOrderedSemiring.{u2} α] {a : ι -> α} {b : ι -> α} (s : Finset.{u1} ι) (H : Finset.Nonempty.{u1} ι s), (forall (i : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (StrictOrderedSemiring.toPartialOrder.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α _inst_1)))) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α (StrictOrderedSemiring.toSemiring.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α _inst_1)))))) (a i))) -> (forall (i : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (StrictOrderedSemiring.toPartialOrder.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α _inst_1)))) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α (StrictOrderedSemiring.toSemiring.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α _inst_1)))))) (b i))) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (StrictOrderedSemiring.toPartialOrder.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α _inst_1)))) (Finset.sup'.{u2, u1} α ι (Lattice.toSemilatticeSup.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α (LinearOrderedAddCommMonoid.toLinearOrder.{u2} α (LinearOrderedSemiring.toLinearOrderedAddCommMonoid.{u2} α _inst_1))))) s H (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (ι -> α) (ι -> α) (ι -> α) (instHMul.{max u2 u1} (ι -> α) (Pi.instMul.{u1, u2} ι (fun (ᾰ : ι) => α) (fun (i : ι) => NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (StrictOrderedSemiring.toSemiring.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α _inst_1))))))) a b)) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (StrictOrderedSemiring.toSemiring.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α _inst_1)))))) (Finset.sup'.{u2, u1} α ι (Lattice.toSemilatticeSup.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α (LinearOrderedAddCommMonoid.toLinearOrder.{u2} α (LinearOrderedSemiring.toLinearOrderedAddCommMonoid.{u2} α _inst_1))))) s H a) (Finset.sup'.{u2, u1} α ι (Lattice.toSemilatticeSup.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α (LinearOrderedAddCommMonoid.toLinearOrder.{u2} α (LinearOrderedSemiring.toLinearOrderedAddCommMonoid.{u2} α _inst_1))))) s H b)))
Case conversion may be inaccurate. Consider using '#align finset.sup'_mul_le_mul_sup'_of_nonneg Finset.sup'_mul_le_mul_sup'_of_nonnegₓ'. -/
theorem sup'_mul_le_mul_sup'_of_nonneg [LinearOrderedSemiring α] {a b : ι → α} (s : Finset ι)
    (H : s.Nonempty) (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) :
    s.sup' H (a * b) ≤ s.sup' H a * s.sup' H b :=
  sup'_le _ _ fun i hi =>
    mul_le_mul (le_sup' _ hi) (le_sup' _ hi) (hb _ hi) ((ha _ hi).trans <| le_sup' _ hi)
#align finset.sup'_mul_le_mul_sup'_of_nonneg Finset.sup'_mul_le_mul_sup'_of_nonneg

/- warning: finset.inf'_mul_le_mul_inf'_of_nonneg -> Finset.inf'_mul_le_mul_inf'_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : LinearOrderedSemiring.{u1} α] {a : ι -> α} {b : ι -> α} (s : Finset.{u2} ι) (H : Finset.Nonempty.{u2} ι s), (forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1))))))))) (a i))) -> (forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1))))))))) (b i))) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1))))))) (Finset.inf'.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α (LinearOrderedAddCommMonoid.toLinearOrder.{u1} α (LinearOrderedSemiring.toLinearOrderedAddCommMonoid.{u1} α _inst_1)))) s H a) (Finset.inf'.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α (LinearOrderedAddCommMonoid.toLinearOrder.{u1} α (LinearOrderedSemiring.toLinearOrderedAddCommMonoid.{u1} α _inst_1)))) s H b)) (Finset.inf'.{u1, u2} α ι (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α (LinearOrderedAddCommMonoid.toLinearOrder.{u1} α (LinearOrderedSemiring.toLinearOrderedAddCommMonoid.{u1} α _inst_1)))) s H (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (ι -> α) (ι -> α) (ι -> α) (instHMul.{max u2 u1} (ι -> α) (Pi.instMul.{u2, u1} ι (fun (ᾰ : ι) => α) (fun (i : ι) => Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1)))))))) a b)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : LinearOrderedSemiring.{u2} α] {a : ι -> α} {b : ι -> α} (s : Finset.{u1} ι) (H : Finset.Nonempty.{u1} ι s), (forall (i : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (StrictOrderedSemiring.toPartialOrder.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α _inst_1)))) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α (StrictOrderedSemiring.toSemiring.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α _inst_1)))))) (a i))) -> (forall (i : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (StrictOrderedSemiring.toPartialOrder.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α _inst_1)))) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α (StrictOrderedSemiring.toSemiring.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α _inst_1)))))) (b i))) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (StrictOrderedSemiring.toPartialOrder.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α _inst_1)))) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (StrictOrderedSemiring.toSemiring.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α _inst_1)))))) (Finset.inf'.{u2, u1} α ι (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α (LinearOrderedAddCommMonoid.toLinearOrder.{u2} α (LinearOrderedSemiring.toLinearOrderedAddCommMonoid.{u2} α _inst_1))))) s H a) (Finset.inf'.{u2, u1} α ι (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α (LinearOrderedAddCommMonoid.toLinearOrder.{u2} α (LinearOrderedSemiring.toLinearOrderedAddCommMonoid.{u2} α _inst_1))))) s H b)) (Finset.inf'.{u2, u1} α ι (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α (LinearOrderedAddCommMonoid.toLinearOrder.{u2} α (LinearOrderedSemiring.toLinearOrderedAddCommMonoid.{u2} α _inst_1))))) s H (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (ι -> α) (ι -> α) (ι -> α) (instHMul.{max u2 u1} (ι -> α) (Pi.instMul.{u1, u2} ι (fun (ᾰ : ι) => α) (fun (i : ι) => NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (StrictOrderedSemiring.toSemiring.{u2} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} α _inst_1))))))) a b)))
Case conversion may be inaccurate. Consider using '#align finset.inf'_mul_le_mul_inf'_of_nonneg Finset.inf'_mul_le_mul_inf'_of_nonnegₓ'. -/
theorem inf'_mul_le_mul_inf'_of_nonneg [LinearOrderedSemiring α] {a b : ι → α} (s : Finset ι)
    (H : s.Nonempty) (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) :
    s.inf' H a * s.inf' H b ≤ s.inf' H (a * b) :=
  le_inf' _ _ fun i hi => mul_le_mul (inf'_le _ hi) (inf'_le _ hi) (le_inf' _ _ hb) (ha _ hi)
#align finset.inf'_mul_le_mul_inf'_of_nonneg Finset.inf'_mul_le_mul_inf'_of_nonneg

open Function

/-! ### Interaction with big lattice/set operations -/


section Lattice

#print Finset.iSup_coe /-
theorem iSup_coe [SupSet β] (f : α → β) (s : Finset α) : (⨆ x ∈ (↑s : Set α), f x) = ⨆ x ∈ s, f x :=
  rfl
#align finset.supr_coe Finset.iSup_coe
-/

#print Finset.iInf_coe /-
theorem iInf_coe [InfSet β] (f : α → β) (s : Finset α) : (⨅ x ∈ (↑s : Set α), f x) = ⨅ x ∈ s, f x :=
  rfl
#align finset.infi_coe Finset.iInf_coe
-/

variable [CompleteLattice β]

/- warning: finset.supr_singleton -> Finset.iSup_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u2} β] (a : α) (s : α -> β), Eq.{succ u2} β (iSup.{u2, succ u1} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) α (fun (x : α) => iSup.{u2, 0} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a)) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a)) => s x))) (s a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u2} β] (a : α) (s : α -> β), Eq.{succ u2} β (iSup.{u2, succ u1} β (CompleteLattice.toSupSet.{u2} β _inst_1) α (fun (x : α) => iSup.{u2, 0} β (CompleteLattice.toSupSet.{u2} β _inst_1) (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a)) (fun (H : Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a)) => s x))) (s a)
Case conversion may be inaccurate. Consider using '#align finset.supr_singleton Finset.iSup_singletonₓ'. -/
theorem iSup_singleton (a : α) (s : α → β) : (⨆ x ∈ ({a} : Finset α), s x) = s a := by simp
#align finset.supr_singleton Finset.iSup_singleton

/- warning: finset.infi_singleton -> Finset.iInf_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u2} β] (a : α) (s : α -> β), Eq.{succ u2} β (iInf.{u2, succ u1} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) α (fun (x : α) => iInf.{u2, 0} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a)) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a)) => s x))) (s a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u2} β] (a : α) (s : α -> β), Eq.{succ u2} β (iInf.{u2, succ u1} β (CompleteLattice.toInfSet.{u2} β _inst_1) α (fun (x : α) => iInf.{u2, 0} β (CompleteLattice.toInfSet.{u2} β _inst_1) (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a)) (fun (H : Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a)) => s x))) (s a)
Case conversion may be inaccurate. Consider using '#align finset.infi_singleton Finset.iInf_singletonₓ'. -/
theorem iInf_singleton (a : α) (s : α → β) : (⨅ x ∈ ({a} : Finset α), s x) = s a := by simp
#align finset.infi_singleton Finset.iInf_singleton

/- warning: finset.supr_option_to_finset -> Finset.iSup_option_toFinset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u2} β] (o : Option.{u1} α) (f : α -> β), Eq.{succ u2} β (iSup.{u2, succ u1} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) α (fun (x : α) => iSup.{u2, 0} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Option.toFinset.{u1} α o)) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Option.toFinset.{u1} α o)) => f x))) (iSup.{u2, succ u1} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) α (fun (x : α) => iSup.{u2, 0} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) (Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) x o) (fun (H : Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) x o) => f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u1} β] (o : Option.{u2} α) (f : α -> β), Eq.{succ u1} β (iSup.{u1, succ u2} β (CompleteLattice.toSupSet.{u1} β _inst_1) α (fun (x : α) => iSup.{u1, 0} β (CompleteLattice.toSupSet.{u1} β _inst_1) (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Option.toFinset.{u2} α o)) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Option.toFinset.{u2} α o)) => f x))) (iSup.{u1, succ u2} β (CompleteLattice.toSupSet.{u1} β _inst_1) α (fun (x : α) => iSup.{u1, 0} β (CompleteLattice.toSupSet.{u1} β _inst_1) (Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) x o) (fun (H : Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) x o) => f x)))
Case conversion may be inaccurate. Consider using '#align finset.supr_option_to_finset Finset.iSup_option_toFinsetₓ'. -/
theorem iSup_option_toFinset (o : Option α) (f : α → β) : (⨆ x ∈ o.toFinset, f x) = ⨆ x ∈ o, f x :=
  by simp
#align finset.supr_option_to_finset Finset.iSup_option_toFinset

/- warning: finset.infi_option_to_finset -> Finset.iInf_option_toFinset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u2} β] (o : Option.{u1} α) (f : α -> β), Eq.{succ u2} β (iInf.{u2, succ u1} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) α (fun (x : α) => iInf.{u2, 0} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Option.toFinset.{u1} α o)) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Option.toFinset.{u1} α o)) => f x))) (iInf.{u2, succ u1} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) α (fun (x : α) => iInf.{u2, 0} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) (Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) x o) (fun (H : Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) x o) => f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u1} β] (o : Option.{u2} α) (f : α -> β), Eq.{succ u1} β (iInf.{u1, succ u2} β (CompleteLattice.toInfSet.{u1} β _inst_1) α (fun (x : α) => iInf.{u1, 0} β (CompleteLattice.toInfSet.{u1} β _inst_1) (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Option.toFinset.{u2} α o)) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Option.toFinset.{u2} α o)) => f x))) (iInf.{u1, succ u2} β (CompleteLattice.toInfSet.{u1} β _inst_1) α (fun (x : α) => iInf.{u1, 0} β (CompleteLattice.toInfSet.{u1} β _inst_1) (Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) x o) (fun (H : Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) x o) => f x)))
Case conversion may be inaccurate. Consider using '#align finset.infi_option_to_finset Finset.iInf_option_toFinsetₓ'. -/
theorem iInf_option_toFinset (o : Option α) (f : α → β) : (⨅ x ∈ o.toFinset, f x) = ⨅ x ∈ o, f x :=
  @iSup_option_toFinset _ βᵒᵈ _ _ _
#align finset.infi_option_to_finset Finset.iInf_option_toFinset

variable [DecidableEq α]

/- warning: finset.supr_union -> Finset.iSup_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u2} β] [_inst_2 : DecidableEq.{succ u1} α] {f : α -> β} {s : Finset.{u1} α} {t : Finset.{u1} α}, Eq.{succ u2} β (iSup.{u2, succ u1} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) α (fun (x : α) => iSup.{u2, 0} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) s t)) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) s t)) => f x))) (Sup.sup.{u2} β (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (CompleteLattice.toLattice.{u2} β _inst_1))) (iSup.{u2, succ u1} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) α (fun (x : α) => iSup.{u2, 0} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) => f x))) (iSup.{u2, succ u1} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) α (fun (x : α) => iSup.{u2, 0} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x t) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x t) => f x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] {f : α -> β} {s : Finset.{u2} α} {t : Finset.{u2} α}, Eq.{succ u1} β (iSup.{u1, succ u2} β (CompleteLattice.toSupSet.{u1} β _inst_1) α (fun (x : α) => iSup.{u1, 0} β (CompleteLattice.toSupSet.{u1} β _inst_1) (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Union.union.{u2} (Finset.{u2} α) (Finset.instUnionFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s t)) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Union.union.{u2} (Finset.{u2} α) (Finset.instUnionFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s t)) => f x))) (Sup.sup.{u1} β (SemilatticeSup.toSup.{u1} β (Lattice.toSemilatticeSup.{u1} β (CompleteLattice.toLattice.{u1} β _inst_1))) (iSup.{u1, succ u2} β (CompleteLattice.toSupSet.{u1} β _inst_1) α (fun (x : α) => iSup.{u1, 0} β (CompleteLattice.toSupSet.{u1} β _inst_1) (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) => f x))) (iSup.{u1, succ u2} β (CompleteLattice.toSupSet.{u1} β _inst_1) α (fun (x : α) => iSup.{u1, 0} β (CompleteLattice.toSupSet.{u1} β _inst_1) (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x t) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x t) => f x))))
Case conversion may be inaccurate. Consider using '#align finset.supr_union Finset.iSup_unionₓ'. -/
theorem iSup_union {f : α → β} {s t : Finset α} :
    (⨆ x ∈ s ∪ t, f x) = (⨆ x ∈ s, f x) ⊔ ⨆ x ∈ t, f x := by simp [iSup_or, iSup_sup_eq]
#align finset.supr_union Finset.iSup_union

/- warning: finset.infi_union -> Finset.iInf_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u2} β] [_inst_2 : DecidableEq.{succ u1} α] {f : α -> β} {s : Finset.{u1} α} {t : Finset.{u1} α}, Eq.{succ u2} β (iInf.{u2, succ u1} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) α (fun (x : α) => iInf.{u2, 0} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) s t)) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) s t)) => f x))) (Inf.inf.{u2} β (SemilatticeInf.toHasInf.{u2} β (Lattice.toSemilatticeInf.{u2} β (CompleteLattice.toLattice.{u2} β _inst_1))) (iInf.{u2, succ u1} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) α (fun (x : α) => iInf.{u2, 0} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) => f x))) (iInf.{u2, succ u1} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) α (fun (x : α) => iInf.{u2, 0} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x t) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x t) => f x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] {f : α -> β} {s : Finset.{u2} α} {t : Finset.{u2} α}, Eq.{succ u1} β (iInf.{u1, succ u2} β (CompleteLattice.toInfSet.{u1} β _inst_1) α (fun (x : α) => iInf.{u1, 0} β (CompleteLattice.toInfSet.{u1} β _inst_1) (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Union.union.{u2} (Finset.{u2} α) (Finset.instUnionFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s t)) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Union.union.{u2} (Finset.{u2} α) (Finset.instUnionFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s t)) => f x))) (Inf.inf.{u1} β (Lattice.toInf.{u1} β (CompleteLattice.toLattice.{u1} β _inst_1)) (iInf.{u1, succ u2} β (CompleteLattice.toInfSet.{u1} β _inst_1) α (fun (x : α) => iInf.{u1, 0} β (CompleteLattice.toInfSet.{u1} β _inst_1) (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) => f x))) (iInf.{u1, succ u2} β (CompleteLattice.toInfSet.{u1} β _inst_1) α (fun (x : α) => iInf.{u1, 0} β (CompleteLattice.toInfSet.{u1} β _inst_1) (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x t) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x t) => f x))))
Case conversion may be inaccurate. Consider using '#align finset.infi_union Finset.iInf_unionₓ'. -/
theorem iInf_union {f : α → β} {s t : Finset α} :
    (⨅ x ∈ s ∪ t, f x) = (⨅ x ∈ s, f x) ⊓ ⨅ x ∈ t, f x :=
  @iSup_union α βᵒᵈ _ _ _ _ _
#align finset.infi_union Finset.iInf_union

/- warning: finset.supr_insert -> Finset.iSup_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u2} β] [_inst_2 : DecidableEq.{succ u1} α] (a : α) (s : Finset.{u1} α) (t : α -> β), Eq.{succ u2} β (iSup.{u2, succ u1} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) α (fun (x : α) => iSup.{u2, 0} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s)) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s)) => t x))) (Sup.sup.{u2} β (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (CompleteLattice.toLattice.{u2} β _inst_1))) (t a) (iSup.{u2, succ u1} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) α (fun (x : α) => iSup.{u2, 0} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) => t x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] (a : α) (s : Finset.{u2} α) (t : α -> β), Eq.{succ u1} β (iSup.{u1, succ u2} β (CompleteLattice.toSupSet.{u1} β _inst_1) α (fun (x : α) => iSup.{u1, 0} β (CompleteLattice.toSupSet.{u1} β _inst_1) (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) a s)) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) a s)) => t x))) (Sup.sup.{u1} β (SemilatticeSup.toSup.{u1} β (Lattice.toSemilatticeSup.{u1} β (CompleteLattice.toLattice.{u1} β _inst_1))) (t a) (iSup.{u1, succ u2} β (CompleteLattice.toSupSet.{u1} β _inst_1) α (fun (x : α) => iSup.{u1, 0} β (CompleteLattice.toSupSet.{u1} β _inst_1) (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) => t x))))
Case conversion may be inaccurate. Consider using '#align finset.supr_insert Finset.iSup_insertₓ'. -/
theorem iSup_insert (a : α) (s : Finset α) (t : α → β) :
    (⨆ x ∈ insert a s, t x) = t a ⊔ ⨆ x ∈ s, t x :=
  by
  rw [insert_eq]
  simp only [iSup_union, Finset.iSup_singleton]
#align finset.supr_insert Finset.iSup_insert

/- warning: finset.infi_insert -> Finset.iInf_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u2} β] [_inst_2 : DecidableEq.{succ u1} α] (a : α) (s : Finset.{u1} α) (t : α -> β), Eq.{succ u2} β (iInf.{u2, succ u1} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) α (fun (x : α) => iInf.{u2, 0} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s)) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s)) => t x))) (Inf.inf.{u2} β (SemilatticeInf.toHasInf.{u2} β (Lattice.toSemilatticeInf.{u2} β (CompleteLattice.toLattice.{u2} β _inst_1))) (t a) (iInf.{u2, succ u1} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) α (fun (x : α) => iInf.{u2, 0} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) => t x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] (a : α) (s : Finset.{u2} α) (t : α -> β), Eq.{succ u1} β (iInf.{u1, succ u2} β (CompleteLattice.toInfSet.{u1} β _inst_1) α (fun (x : α) => iInf.{u1, 0} β (CompleteLattice.toInfSet.{u1} β _inst_1) (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) a s)) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) a s)) => t x))) (Inf.inf.{u1} β (Lattice.toInf.{u1} β (CompleteLattice.toLattice.{u1} β _inst_1)) (t a) (iInf.{u1, succ u2} β (CompleteLattice.toInfSet.{u1} β _inst_1) α (fun (x : α) => iInf.{u1, 0} β (CompleteLattice.toInfSet.{u1} β _inst_1) (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) => t x))))
Case conversion may be inaccurate. Consider using '#align finset.infi_insert Finset.iInf_insertₓ'. -/
theorem iInf_insert (a : α) (s : Finset α) (t : α → β) :
    (⨅ x ∈ insert a s, t x) = t a ⊓ ⨅ x ∈ s, t x :=
  @iSup_insert α βᵒᵈ _ _ _ _ _
#align finset.infi_insert Finset.iInf_insert

/- warning: finset.supr_finset_image -> Finset.iSup_finset_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u2} β] [_inst_2 : DecidableEq.{succ u1} α] {f : γ -> α} {g : α -> β} {s : Finset.{u3} γ}, Eq.{succ u2} β (iSup.{u2, succ u1} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) α (fun (x : α) => iSup.{u2, 0} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Finset.image.{u3, u1} γ α (fun (a : α) (b : α) => _inst_2 a b) f s)) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Finset.image.{u3, u1} γ α (fun (a : α) (b : α) => _inst_2 a b) f s)) => g x))) (iSup.{u2, succ u3} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) γ (fun (y : γ) => iSup.{u2, 0} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) (Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) y s) (fun (H : Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) y s) => g (f y))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u2} β] [_inst_2 : DecidableEq.{succ u1} α] {f : γ -> α} {g : α -> β} {s : Finset.{u3} γ}, Eq.{succ u2} β (iSup.{u2, succ u1} β (CompleteLattice.toSupSet.{u2} β _inst_1) α (fun (x : α) => iSup.{u2, 0} β (CompleteLattice.toSupSet.{u2} β _inst_1) (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x (Finset.image.{u3, u1} γ α (fun (a : α) (b : α) => _inst_2 a b) f s)) (fun (H : Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x (Finset.image.{u3, u1} γ α (fun (a : α) (b : α) => _inst_2 a b) f s)) => g x))) (iSup.{u2, succ u3} β (CompleteLattice.toSupSet.{u2} β _inst_1) γ (fun (y : γ) => iSup.{u2, 0} β (CompleteLattice.toSupSet.{u2} β _inst_1) (Membership.mem.{u3, u3} γ (Finset.{u3} γ) (Finset.instMembershipFinset.{u3} γ) y s) (fun (H : Membership.mem.{u3, u3} γ (Finset.{u3} γ) (Finset.instMembershipFinset.{u3} γ) y s) => g (f y))))
Case conversion may be inaccurate. Consider using '#align finset.supr_finset_image Finset.iSup_finset_imageₓ'. -/
theorem iSup_finset_image {f : γ → α} {g : α → β} {s : Finset γ} :
    (⨆ x ∈ s.image f, g x) = ⨆ y ∈ s, g (f y) := by rw [← supr_coe, coe_image, iSup_image, supr_coe]
#align finset.supr_finset_image Finset.iSup_finset_image

/- warning: finset.infi_finset_image -> Finset.iInf_finset_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u2} β] [_inst_2 : DecidableEq.{succ u1} α] {f : γ -> α} {g : α -> β} {s : Finset.{u3} γ}, Eq.{succ u2} β (iInf.{u2, succ u1} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) α (fun (x : α) => iInf.{u2, 0} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Finset.image.{u3, u1} γ α (fun (a : α) (b : α) => _inst_2 a b) f s)) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Finset.image.{u3, u1} γ α (fun (a : α) (b : α) => _inst_2 a b) f s)) => g x))) (iInf.{u2, succ u3} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) γ (fun (y : γ) => iInf.{u2, 0} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) (Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) y s) (fun (H : Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) y s) => g (f y))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u2} β] [_inst_2 : DecidableEq.{succ u1} α] {f : γ -> α} {g : α -> β} {s : Finset.{u3} γ}, Eq.{succ u2} β (iInf.{u2, succ u1} β (CompleteLattice.toInfSet.{u2} β _inst_1) α (fun (x : α) => iInf.{u2, 0} β (CompleteLattice.toInfSet.{u2} β _inst_1) (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x (Finset.image.{u3, u1} γ α (fun (a : α) (b : α) => _inst_2 a b) f s)) (fun (H : Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x (Finset.image.{u3, u1} γ α (fun (a : α) (b : α) => _inst_2 a b) f s)) => g x))) (iInf.{u2, succ u3} β (CompleteLattice.toInfSet.{u2} β _inst_1) γ (fun (y : γ) => iInf.{u2, 0} β (CompleteLattice.toInfSet.{u2} β _inst_1) (Membership.mem.{u3, u3} γ (Finset.{u3} γ) (Finset.instMembershipFinset.{u3} γ) y s) (fun (H : Membership.mem.{u3, u3} γ (Finset.{u3} γ) (Finset.instMembershipFinset.{u3} γ) y s) => g (f y))))
Case conversion may be inaccurate. Consider using '#align finset.infi_finset_image Finset.iInf_finset_imageₓ'. -/
theorem iInf_finset_image {f : γ → α} {g : α → β} {s : Finset γ} :
    (⨅ x ∈ s.image f, g x) = ⨅ y ∈ s, g (f y) := by rw [← infi_coe, coe_image, iInf_image, infi_coe]
#align finset.infi_finset_image Finset.iInf_finset_image

/- warning: finset.supr_insert_update -> Finset.iSup_insert_update is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u2} β] [_inst_2 : DecidableEq.{succ u1} α] {x : α} {t : Finset.{u1} α} (f : α -> β) {s : β}, (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x t)) -> (Eq.{succ u2} β (iSup.{u2, succ u1} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) α (fun (i : α) => iSup.{u2, 0} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) x t)) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) x t)) => Function.update.{succ u1, succ u2} α (fun (ᾰ : α) => β) (fun (a : α) (b : α) => _inst_2 a b) f x s i))) (Sup.sup.{u2} β (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (CompleteLattice.toLattice.{u2} β _inst_1))) s (iSup.{u2, succ u1} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) α (fun (i : α) => iSup.{u2, 0} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i t) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i t) => f i)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] {x : α} {t : Finset.{u2} α} (f : α -> β) {s : β}, (Not (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x t)) -> (Eq.{succ u1} β (iSup.{u1, succ u2} β (CompleteLattice.toSupSet.{u1} β _inst_1) α (fun (i : α) => iSup.{u1, 0} β (CompleteLattice.toSupSet.{u1} β _inst_1) (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) x t)) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) x t)) => Function.update.{succ u2, succ u1} α (fun (ᾰ : α) => β) (fun (a : α) (b : α) => _inst_2 a b) f x s i))) (Sup.sup.{u1} β (SemilatticeSup.toSup.{u1} β (Lattice.toSemilatticeSup.{u1} β (CompleteLattice.toLattice.{u1} β _inst_1))) s (iSup.{u1, succ u2} β (CompleteLattice.toSupSet.{u1} β _inst_1) α (fun (i : α) => iSup.{u1, 0} β (CompleteLattice.toSupSet.{u1} β _inst_1) (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i t) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i t) => f i)))))
Case conversion may be inaccurate. Consider using '#align finset.supr_insert_update Finset.iSup_insert_updateₓ'. -/
theorem iSup_insert_update {x : α} {t : Finset α} (f : α → β) {s : β} (hx : x ∉ t) :
    (⨆ i ∈ insert x t, Function.update f x s i) = s ⊔ ⨆ i ∈ t, f i :=
  by
  simp only [Finset.iSup_insert, update_same]
  rcongr (i hi); apply update_noteq; rintro rfl; exact hx hi
#align finset.supr_insert_update Finset.iSup_insert_update

/- warning: finset.infi_insert_update -> Finset.iInf_insert_update is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u2} β] [_inst_2 : DecidableEq.{succ u1} α] {x : α} {t : Finset.{u1} α} (f : α -> β) {s : β}, (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x t)) -> (Eq.{succ u2} β (iInf.{u2, succ u1} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) α (fun (i : α) => iInf.{u2, 0} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) x t)) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) x t)) => Function.update.{succ u1, succ u2} α (fun (ᾰ : α) => β) (fun (a : α) (b : α) => _inst_2 a b) f x s i))) (Inf.inf.{u2} β (SemilatticeInf.toHasInf.{u2} β (Lattice.toSemilatticeInf.{u2} β (CompleteLattice.toLattice.{u2} β _inst_1))) s (iInf.{u2, succ u1} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) α (fun (i : α) => iInf.{u2, 0} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i t) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i t) => f i)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] {x : α} {t : Finset.{u2} α} (f : α -> β) {s : β}, (Not (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x t)) -> (Eq.{succ u1} β (iInf.{u1, succ u2} β (CompleteLattice.toInfSet.{u1} β _inst_1) α (fun (i : α) => iInf.{u1, 0} β (CompleteLattice.toInfSet.{u1} β _inst_1) (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) x t)) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) x t)) => Function.update.{succ u2, succ u1} α (fun (ᾰ : α) => β) (fun (a : α) (b : α) => _inst_2 a b) f x s i))) (Inf.inf.{u1} β (Lattice.toInf.{u1} β (CompleteLattice.toLattice.{u1} β _inst_1)) s (iInf.{u1, succ u2} β (CompleteLattice.toInfSet.{u1} β _inst_1) α (fun (i : α) => iInf.{u1, 0} β (CompleteLattice.toInfSet.{u1} β _inst_1) (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i t) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i t) => f i)))))
Case conversion may be inaccurate. Consider using '#align finset.infi_insert_update Finset.iInf_insert_updateₓ'. -/
theorem iInf_insert_update {x : α} {t : Finset α} (f : α → β) {s : β} (hx : x ∉ t) :
    (⨅ i ∈ insert x t, update f x s i) = s ⊓ ⨅ i ∈ t, f i :=
  @iSup_insert_update α βᵒᵈ _ _ _ _ f _ hx
#align finset.infi_insert_update Finset.iInf_insert_update

/- warning: finset.supr_bUnion -> Finset.iSup_biUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u2} β] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u3} γ) (t : γ -> (Finset.{u1} α)) (f : α -> β), Eq.{succ u2} β (iSup.{u2, succ u1} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) α (fun (y : α) => iSup.{u2, 0} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y (Finset.biUnion.{u3, u1} γ α (fun (a : α) (b : α) => _inst_2 a b) s t)) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y (Finset.biUnion.{u3, u1} γ α (fun (a : α) (b : α) => _inst_2 a b) s t)) => f y))) (iSup.{u2, succ u3} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) γ (fun (x : γ) => iSup.{u2, 0} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) (Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) x s) (fun (H : Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) x s) => iSup.{u2, succ u1} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) α (fun (y : α) => iSup.{u2, 0} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_1)) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y (t x)) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y (t x)) => f y)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] (s : Finset.{u3} γ) (t : γ -> (Finset.{u2} α)) (f : α -> β), Eq.{succ u1} β (iSup.{u1, succ u2} β (CompleteLattice.toSupSet.{u1} β _inst_1) α (fun (y : α) => iSup.{u1, 0} β (CompleteLattice.toSupSet.{u1} β _inst_1) (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) y (Finset.biUnion.{u3, u2} γ α (fun (a : α) (b : α) => _inst_2 a b) s t)) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) y (Finset.biUnion.{u3, u2} γ α (fun (a : α) (b : α) => _inst_2 a b) s t)) => f y))) (iSup.{u1, succ u3} β (CompleteLattice.toSupSet.{u1} β _inst_1) γ (fun (x : γ) => iSup.{u1, 0} β (CompleteLattice.toSupSet.{u1} β _inst_1) (Membership.mem.{u3, u3} γ (Finset.{u3} γ) (Finset.instMembershipFinset.{u3} γ) x s) (fun (H : Membership.mem.{u3, u3} γ (Finset.{u3} γ) (Finset.instMembershipFinset.{u3} γ) x s) => iSup.{u1, succ u2} β (CompleteLattice.toSupSet.{u1} β _inst_1) α (fun (y : α) => iSup.{u1, 0} β (CompleteLattice.toSupSet.{u1} β _inst_1) (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) y (t x)) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) y (t x)) => f y)))))
Case conversion may be inaccurate. Consider using '#align finset.supr_bUnion Finset.iSup_biUnionₓ'. -/
theorem iSup_biUnion (s : Finset γ) (t : γ → Finset α) (f : α → β) :
    (⨆ y ∈ s.biUnion t, f y) = ⨆ (x ∈ s) (y ∈ t x), f y := by simp [@iSup_comm _ α, iSup_and]
#align finset.supr_bUnion Finset.iSup_biUnion

/- warning: finset.infi_bUnion -> Finset.iInf_biUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u2} β] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u3} γ) (t : γ -> (Finset.{u1} α)) (f : α -> β), Eq.{succ u2} β (iInf.{u2, succ u1} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) α (fun (y : α) => iInf.{u2, 0} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y (Finset.biUnion.{u3, u1} γ α (fun (a : α) (b : α) => _inst_2 a b) s t)) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y (Finset.biUnion.{u3, u1} γ α (fun (a : α) (b : α) => _inst_2 a b) s t)) => f y))) (iInf.{u2, succ u3} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) γ (fun (x : γ) => iInf.{u2, 0} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) (Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) x s) (fun (H : Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) x s) => iInf.{u2, succ u1} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) α (fun (y : α) => iInf.{u2, 0} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_1)) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y (t x)) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y (t x)) => f y)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] (s : Finset.{u3} γ) (t : γ -> (Finset.{u2} α)) (f : α -> β), Eq.{succ u1} β (iInf.{u1, succ u2} β (CompleteLattice.toInfSet.{u1} β _inst_1) α (fun (y : α) => iInf.{u1, 0} β (CompleteLattice.toInfSet.{u1} β _inst_1) (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) y (Finset.biUnion.{u3, u2} γ α (fun (a : α) (b : α) => _inst_2 a b) s t)) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) y (Finset.biUnion.{u3, u2} γ α (fun (a : α) (b : α) => _inst_2 a b) s t)) => f y))) (iInf.{u1, succ u3} β (CompleteLattice.toInfSet.{u1} β _inst_1) γ (fun (x : γ) => iInf.{u1, 0} β (CompleteLattice.toInfSet.{u1} β _inst_1) (Membership.mem.{u3, u3} γ (Finset.{u3} γ) (Finset.instMembershipFinset.{u3} γ) x s) (fun (H : Membership.mem.{u3, u3} γ (Finset.{u3} γ) (Finset.instMembershipFinset.{u3} γ) x s) => iInf.{u1, succ u2} β (CompleteLattice.toInfSet.{u1} β _inst_1) α (fun (y : α) => iInf.{u1, 0} β (CompleteLattice.toInfSet.{u1} β _inst_1) (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) y (t x)) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) y (t x)) => f y)))))
Case conversion may be inaccurate. Consider using '#align finset.infi_bUnion Finset.iInf_biUnionₓ'. -/
theorem iInf_biUnion (s : Finset γ) (t : γ → Finset α) (f : α → β) :
    (⨅ y ∈ s.biUnion t, f y) = ⨅ (x ∈ s) (y ∈ t x), f y :=
  @iSup_biUnion _ βᵒᵈ _ _ _ _ _ _
#align finset.infi_bUnion Finset.iInf_biUnion

end Lattice

/- warning: finset.set_bUnion_coe -> Finset.set_biUnion_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Finset.{u1} α) (t : α -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Set.iUnion.{u2, succ u1} β α (fun (x : α) => Set.iUnion.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) => t x))) (Set.iUnion.{u2, succ u1} β α (fun (x : α) => Set.iUnion.{u2, 0} β (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) => t x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Finset.{u2} α) (t : α -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Set.iUnion.{u1, succ u2} β α (fun (x : α) => Set.iUnion.{u1, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Finset.toSet.{u2} α s)) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Finset.toSet.{u2} α s)) => t x))) (Set.iUnion.{u1, succ u2} β α (fun (x : α) => Set.iUnion.{u1, 0} β (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) => t x)))
Case conversion may be inaccurate. Consider using '#align finset.set_bUnion_coe Finset.set_biUnion_coeₓ'. -/
theorem set_biUnion_coe (s : Finset α) (t : α → Set β) : (⋃ x ∈ (↑s : Set α), t x) = ⋃ x ∈ s, t x :=
  rfl
#align finset.set_bUnion_coe Finset.set_biUnion_coe

/- warning: finset.set_bInter_coe -> Finset.set_biInter_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Finset.{u1} α) (t : α -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Set.iInter.{u2, succ u1} β α (fun (x : α) => Set.iInter.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) => t x))) (Set.iInter.{u2, succ u1} β α (fun (x : α) => Set.iInter.{u2, 0} β (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) => t x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Finset.{u2} α) (t : α -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Set.iInter.{u1, succ u2} β α (fun (x : α) => Set.iInter.{u1, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Finset.toSet.{u2} α s)) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Finset.toSet.{u2} α s)) => t x))) (Set.iInter.{u1, succ u2} β α (fun (x : α) => Set.iInter.{u1, 0} β (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) => t x)))
Case conversion may be inaccurate. Consider using '#align finset.set_bInter_coe Finset.set_biInter_coeₓ'. -/
theorem set_biInter_coe (s : Finset α) (t : α → Set β) : (⋂ x ∈ (↑s : Set α), t x) = ⋂ x ∈ s, t x :=
  rfl
#align finset.set_bInter_coe Finset.set_biInter_coe

#print Finset.set_biUnion_singleton /-
theorem set_biUnion_singleton (a : α) (s : α → Set β) : (⋃ x ∈ ({a} : Finset α), s x) = s a :=
  iSup_singleton a s
#align finset.set_bUnion_singleton Finset.set_biUnion_singleton
-/

#print Finset.set_biInter_singleton /-
theorem set_biInter_singleton (a : α) (s : α → Set β) : (⋂ x ∈ ({a} : Finset α), s x) = s a :=
  iInf_singleton a s
#align finset.set_bInter_singleton Finset.set_biInter_singleton
-/

#print Finset.set_biUnion_preimage_singleton /-
@[simp]
theorem set_biUnion_preimage_singleton (f : α → β) (s : Finset β) :
    (⋃ y ∈ s, f ⁻¹' {y}) = f ⁻¹' s :=
  Set.biUnion_preimage_singleton f s
#align finset.set_bUnion_preimage_singleton Finset.set_biUnion_preimage_singleton
-/

/- warning: finset.set_bUnion_option_to_finset -> Finset.set_biUnion_option_toFinset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (o : Option.{u1} α) (f : α -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Set.iUnion.{u2, succ u1} β α (fun (x : α) => Set.iUnion.{u2, 0} β (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Option.toFinset.{u1} α o)) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Option.toFinset.{u1} α o)) => f x))) (Set.iUnion.{u2, succ u1} β α (fun (x : α) => Set.iUnion.{u2, 0} β (Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) x o) (fun (H : Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) x o) => f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (o : Option.{u2} α) (f : α -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Set.iUnion.{u1, succ u2} β α (fun (x : α) => Set.iUnion.{u1, 0} β (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Option.toFinset.{u2} α o)) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Option.toFinset.{u2} α o)) => f x))) (Set.iUnion.{u1, succ u2} β α (fun (x : α) => Set.iUnion.{u1, 0} β (Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) x o) (fun (H : Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) x o) => f x)))
Case conversion may be inaccurate. Consider using '#align finset.set_bUnion_option_to_finset Finset.set_biUnion_option_toFinsetₓ'. -/
theorem set_biUnion_option_toFinset (o : Option α) (f : α → Set β) :
    (⋃ x ∈ o.toFinset, f x) = ⋃ x ∈ o, f x :=
  iSup_option_toFinset o f
#align finset.set_bUnion_option_to_finset Finset.set_biUnion_option_toFinset

/- warning: finset.set_bInter_option_to_finset -> Finset.set_biInter_option_toFinset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (o : Option.{u1} α) (f : α -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Set.iInter.{u2, succ u1} β α (fun (x : α) => Set.iInter.{u2, 0} β (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Option.toFinset.{u1} α o)) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Option.toFinset.{u1} α o)) => f x))) (Set.iInter.{u2, succ u1} β α (fun (x : α) => Set.iInter.{u2, 0} β (Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) x o) (fun (H : Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) x o) => f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (o : Option.{u2} α) (f : α -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Set.iInter.{u1, succ u2} β α (fun (x : α) => Set.iInter.{u1, 0} β (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Option.toFinset.{u2} α o)) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Option.toFinset.{u2} α o)) => f x))) (Set.iInter.{u1, succ u2} β α (fun (x : α) => Set.iInter.{u1, 0} β (Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) x o) (fun (H : Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) x o) => f x)))
Case conversion may be inaccurate. Consider using '#align finset.set_bInter_option_to_finset Finset.set_biInter_option_toFinsetₓ'. -/
theorem set_biInter_option_toFinset (o : Option α) (f : α → Set β) :
    (⋂ x ∈ o.toFinset, f x) = ⋂ x ∈ o, f x :=
  iInf_option_toFinset o f
#align finset.set_bInter_option_to_finset Finset.set_biInter_option_toFinset

/- warning: finset.subset_set_bUnion_of_mem -> Finset.subset_set_biUnion_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {f : α -> (Set.{u2} β)} {x : α}, (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (f x) (Set.iUnion.{u2, succ u1} β α (fun (y : α) => Set.iUnion.{u2, 0} β (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y s) => f y))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Finset.{u2} α} {f : α -> (Set.{u1} β)} {x : α}, (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) -> (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (f x) (Set.iUnion.{u1, succ u2} β α (fun (y : α) => Set.iUnion.{u1, 0} β (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) y s) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) y s) => f y))))
Case conversion may be inaccurate. Consider using '#align finset.subset_set_bUnion_of_mem Finset.subset_set_biUnion_of_memₓ'. -/
theorem subset_set_biUnion_of_mem {s : Finset α} {f : α → Set β} {x : α} (h : x ∈ s) :
    f x ⊆ ⋃ y ∈ s, f y :=
  show f x ≤ ⨆ y ∈ s, f y from le_iSup_of_le x <| le_iSup _ h
#align finset.subset_set_bUnion_of_mem Finset.subset_set_biUnion_of_mem

variable [DecidableEq α]

/- warning: finset.set_bUnion_union -> Finset.set_biUnion_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α) (u : α -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Set.iUnion.{u2, succ u1} β α (fun (x : α) => Set.iUnion.{u2, 0} β (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) => u x))) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) (Set.iUnion.{u2, succ u1} β α (fun (x : α) => Set.iUnion.{u2, 0} β (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) => u x))) (Set.iUnion.{u2, succ u1} β α (fun (x : α) => Set.iUnion.{u2, 0} β (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x t) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x t) => u x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] (s : Finset.{u2} α) (t : Finset.{u2} α) (u : α -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Set.iUnion.{u1, succ u2} β α (fun (x : α) => Set.iUnion.{u1, 0} β (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Union.union.{u2} (Finset.{u2} α) (Finset.instUnionFinset.{u2} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Union.union.{u2} (Finset.{u2} α) (Finset.instUnionFinset.{u2} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) => u x))) (Union.union.{u1} (Set.{u1} β) (Set.instUnionSet.{u1} β) (Set.iUnion.{u1, succ u2} β α (fun (x : α) => Set.iUnion.{u1, 0} β (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) => u x))) (Set.iUnion.{u1, succ u2} β α (fun (x : α) => Set.iUnion.{u1, 0} β (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x t) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x t) => u x))))
Case conversion may be inaccurate. Consider using '#align finset.set_bUnion_union Finset.set_biUnion_unionₓ'. -/
theorem set_biUnion_union (s t : Finset α) (u : α → Set β) :
    (⋃ x ∈ s ∪ t, u x) = (⋃ x ∈ s, u x) ∪ ⋃ x ∈ t, u x :=
  iSup_union
#align finset.set_bUnion_union Finset.set_biUnion_union

/- warning: finset.set_bInter_inter -> Finset.set_biInter_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α) (u : α -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Set.iInter.{u2, succ u1} β α (fun (x : α) => Set.iInter.{u2, 0} β (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) => u x))) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (Set.iInter.{u2, succ u1} β α (fun (x : α) => Set.iInter.{u2, 0} β (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) => u x))) (Set.iInter.{u2, succ u1} β α (fun (x : α) => Set.iInter.{u2, 0} β (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x t) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x t) => u x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] (s : Finset.{u2} α) (t : Finset.{u2} α) (u : α -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Set.iInter.{u1, succ u2} β α (fun (x : α) => Set.iInter.{u1, 0} β (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Union.union.{u2} (Finset.{u2} α) (Finset.instUnionFinset.{u2} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Union.union.{u2} (Finset.{u2} α) (Finset.instUnionFinset.{u2} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) => u x))) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (Set.iInter.{u1, succ u2} β α (fun (x : α) => Set.iInter.{u1, 0} β (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) => u x))) (Set.iInter.{u1, succ u2} β α (fun (x : α) => Set.iInter.{u1, 0} β (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x t) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x t) => u x))))
Case conversion may be inaccurate. Consider using '#align finset.set_bInter_inter Finset.set_biInter_interₓ'. -/
theorem set_biInter_inter (s t : Finset α) (u : α → Set β) :
    (⋂ x ∈ s ∪ t, u x) = (⋂ x ∈ s, u x) ∩ ⋂ x ∈ t, u x :=
  iInf_union
#align finset.set_bInter_inter Finset.set_biInter_inter

/- warning: finset.set_bUnion_insert -> Finset.set_biUnion_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] (a : α) (s : Finset.{u1} α) (t : α -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Set.iUnion.{u2, succ u1} β α (fun (x : α) => Set.iUnion.{u2, 0} β (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) => t x))) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) (t a) (Set.iUnion.{u2, succ u1} β α (fun (x : α) => Set.iUnion.{u2, 0} β (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) => t x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] (a : α) (s : Finset.{u2} α) (t : α -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Set.iUnion.{u1, succ u2} β α (fun (x : α) => Set.iUnion.{u1, 0} β (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) => t x))) (Union.union.{u1} (Set.{u1} β) (Set.instUnionSet.{u1} β) (t a) (Set.iUnion.{u1, succ u2} β α (fun (x : α) => Set.iUnion.{u1, 0} β (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) => t x))))
Case conversion may be inaccurate. Consider using '#align finset.set_bUnion_insert Finset.set_biUnion_insertₓ'. -/
theorem set_biUnion_insert (a : α) (s : Finset α) (t : α → Set β) :
    (⋃ x ∈ insert a s, t x) = t a ∪ ⋃ x ∈ s, t x :=
  iSup_insert a s t
#align finset.set_bUnion_insert Finset.set_biUnion_insert

/- warning: finset.set_bInter_insert -> Finset.set_biInter_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] (a : α) (s : Finset.{u1} α) (t : α -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Set.iInter.{u2, succ u1} β α (fun (x : α) => Set.iInter.{u2, 0} β (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) => t x))) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (t a) (Set.iInter.{u2, succ u1} β α (fun (x : α) => Set.iInter.{u2, 0} β (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) => t x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] (a : α) (s : Finset.{u2} α) (t : α -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Set.iInter.{u1, succ u2} β α (fun (x : α) => Set.iInter.{u1, 0} β (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) => t x))) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (t a) (Set.iInter.{u1, succ u2} β α (fun (x : α) => Set.iInter.{u1, 0} β (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) => t x))))
Case conversion may be inaccurate. Consider using '#align finset.set_bInter_insert Finset.set_biInter_insertₓ'. -/
theorem set_biInter_insert (a : α) (s : Finset α) (t : α → Set β) :
    (⋂ x ∈ insert a s, t x) = t a ∩ ⋂ x ∈ s, t x :=
  iInf_insert a s t
#align finset.set_bInter_insert Finset.set_biInter_insert

/- warning: finset.set_bUnion_finset_image -> Finset.set_biUnion_finset_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : DecidableEq.{succ u1} α] {f : γ -> α} {g : α -> (Set.{u2} β)} {s : Finset.{u3} γ}, Eq.{succ u2} (Set.{u2} β) (Set.iUnion.{u2, succ u1} β α (fun (x : α) => Set.iUnion.{u2, 0} β (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Finset.image.{u3, u1} γ α (fun (a : α) (b : α) => _inst_1 a b) f s)) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Finset.image.{u3, u1} γ α (fun (a : α) (b : α) => _inst_1 a b) f s)) => g x))) (Set.iUnion.{u2, succ u3} β γ (fun (y : γ) => Set.iUnion.{u2, 0} β (Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) y s) (fun (H : Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) y s) => g (f y))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] {f : γ -> α} {g : α -> (Set.{u3} β)} {s : Finset.{u2} γ}, Eq.{succ u3} (Set.{u3} β) (Set.iUnion.{u3, succ u1} β α (fun (x : α) => Set.iUnion.{u3, 0} β (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x (Finset.image.{u2, u1} γ α (fun (a : α) (b : α) => _inst_1 a b) f s)) (fun (H : Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x (Finset.image.{u2, u1} γ α (fun (a : α) (b : α) => _inst_1 a b) f s)) => g x))) (Set.iUnion.{u3, succ u2} β γ (fun (y : γ) => Set.iUnion.{u3, 0} β (Membership.mem.{u2, u2} γ (Finset.{u2} γ) (Finset.instMembershipFinset.{u2} γ) y s) (fun (H : Membership.mem.{u2, u2} γ (Finset.{u2} γ) (Finset.instMembershipFinset.{u2} γ) y s) => g (f y))))
Case conversion may be inaccurate. Consider using '#align finset.set_bUnion_finset_image Finset.set_biUnion_finset_imageₓ'. -/
theorem set_biUnion_finset_image {f : γ → α} {g : α → Set β} {s : Finset γ} :
    (⋃ x ∈ s.image f, g x) = ⋃ y ∈ s, g (f y) :=
  iSup_finset_image
#align finset.set_bUnion_finset_image Finset.set_biUnion_finset_image

/- warning: finset.set_bInter_finset_image -> Finset.set_biInter_finset_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : DecidableEq.{succ u1} α] {f : γ -> α} {g : α -> (Set.{u2} β)} {s : Finset.{u3} γ}, Eq.{succ u2} (Set.{u2} β) (Set.iInter.{u2, succ u1} β α (fun (x : α) => Set.iInter.{u2, 0} β (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Finset.image.{u3, u1} γ α (fun (a : α) (b : α) => _inst_1 a b) f s)) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Finset.image.{u3, u1} γ α (fun (a : α) (b : α) => _inst_1 a b) f s)) => g x))) (Set.iInter.{u2, succ u3} β γ (fun (y : γ) => Set.iInter.{u2, 0} β (Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) y s) (fun (H : Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) y s) => g (f y))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] {f : γ -> α} {g : α -> (Set.{u3} β)} {s : Finset.{u2} γ}, Eq.{succ u3} (Set.{u3} β) (Set.iInter.{u3, succ u1} β α (fun (x : α) => Set.iInter.{u3, 0} β (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x (Finset.image.{u2, u1} γ α (fun (a : α) (b : α) => _inst_1 a b) f s)) (fun (H : Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x (Finset.image.{u2, u1} γ α (fun (a : α) (b : α) => _inst_1 a b) f s)) => g x))) (Set.iInter.{u3, succ u2} β γ (fun (y : γ) => Set.iInter.{u3, 0} β (Membership.mem.{u2, u2} γ (Finset.{u2} γ) (Finset.instMembershipFinset.{u2} γ) y s) (fun (H : Membership.mem.{u2, u2} γ (Finset.{u2} γ) (Finset.instMembershipFinset.{u2} γ) y s) => g (f y))))
Case conversion may be inaccurate. Consider using '#align finset.set_bInter_finset_image Finset.set_biInter_finset_imageₓ'. -/
theorem set_biInter_finset_image {f : γ → α} {g : α → Set β} {s : Finset γ} :
    (⋂ x ∈ s.image f, g x) = ⋂ y ∈ s, g (f y) :=
  iInf_finset_image
#align finset.set_bInter_finset_image Finset.set_biInter_finset_image

/- warning: finset.set_bUnion_insert_update -> Finset.set_biUnion_insert_update is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] {x : α} {t : Finset.{u1} α} (f : α -> (Set.{u2} β)) {s : Set.{u2} β}, (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x t)) -> (Eq.{succ u2} (Set.{u2} β) (Set.iUnion.{u2, succ u1} β α (fun (i : α) => Set.iUnion.{u2, 0} β (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) x t)) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) x t)) => Function.update.{succ u1, succ u2} α (fun (ᾰ : α) => Set.{u2} β) (fun (a : α) (b : α) => _inst_1 a b) f x s i))) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) s (Set.iUnion.{u2, succ u1} β α (fun (i : α) => Set.iUnion.{u2, 0} β (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i t) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i t) => f i)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] {x : α} {t : Finset.{u2} α} (f : α -> (Set.{u1} β)) {s : Set.{u1} β}, (Not (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x t)) -> (Eq.{succ u1} (Set.{u1} β) (Set.iUnion.{u1, succ u2} β α (fun (i : α) => Set.iUnion.{u1, 0} β (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_1 a b)) x t)) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_1 a b)) x t)) => Function.update.{succ u2, succ u1} α (fun (ᾰ : α) => Set.{u1} β) (fun (a : α) (b : α) => _inst_1 a b) f x s i))) (Union.union.{u1} (Set.{u1} β) (Set.instUnionSet.{u1} β) s (Set.iUnion.{u1, succ u2} β α (fun (i : α) => Set.iUnion.{u1, 0} β (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i t) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i t) => f i)))))
Case conversion may be inaccurate. Consider using '#align finset.set_bUnion_insert_update Finset.set_biUnion_insert_updateₓ'. -/
theorem set_biUnion_insert_update {x : α} {t : Finset α} (f : α → Set β) {s : Set β} (hx : x ∉ t) :
    (⋃ i ∈ insert x t, @update _ _ _ f x s i) = s ∪ ⋃ i ∈ t, f i :=
  iSup_insert_update f hx
#align finset.set_bUnion_insert_update Finset.set_biUnion_insert_update

/- warning: finset.set_bInter_insert_update -> Finset.set_biInter_insert_update is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] {x : α} {t : Finset.{u1} α} (f : α -> (Set.{u2} β)) {s : Set.{u2} β}, (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x t)) -> (Eq.{succ u2} (Set.{u2} β) (Set.iInter.{u2, succ u1} β α (fun (i : α) => Set.iInter.{u2, 0} β (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) x t)) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) x t)) => Function.update.{succ u1, succ u2} α (fun (ᾰ : α) => Set.{u2} β) (fun (a : α) (b : α) => _inst_1 a b) f x s i))) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) s (Set.iInter.{u2, succ u1} β α (fun (i : α) => Set.iInter.{u2, 0} β (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i t) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i t) => f i)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] {x : α} {t : Finset.{u2} α} (f : α -> (Set.{u1} β)) {s : Set.{u1} β}, (Not (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x t)) -> (Eq.{succ u1} (Set.{u1} β) (Set.iInter.{u1, succ u2} β α (fun (i : α) => Set.iInter.{u1, 0} β (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_1 a b)) x t)) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_1 a b)) x t)) => Function.update.{succ u2, succ u1} α (fun (ᾰ : α) => Set.{u1} β) (fun (a : α) (b : α) => _inst_1 a b) f x s i))) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) s (Set.iInter.{u1, succ u2} β α (fun (i : α) => Set.iInter.{u1, 0} β (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i t) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i t) => f i)))))
Case conversion may be inaccurate. Consider using '#align finset.set_bInter_insert_update Finset.set_biInter_insert_updateₓ'. -/
theorem set_biInter_insert_update {x : α} {t : Finset α} (f : α → Set β) {s : Set β} (hx : x ∉ t) :
    (⋂ i ∈ insert x t, @update _ _ _ f x s i) = s ∩ ⋂ i ∈ t, f i :=
  iInf_insert_update f hx
#align finset.set_bInter_insert_update Finset.set_biInter_insert_update

/- warning: finset.set_bUnion_bUnion -> Finset.set_biUnion_biUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u3} γ) (t : γ -> (Finset.{u1} α)) (f : α -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Set.iUnion.{u2, succ u1} β α (fun (y : α) => Set.iUnion.{u2, 0} β (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y (Finset.biUnion.{u3, u1} γ α (fun (a : α) (b : α) => _inst_1 a b) s t)) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y (Finset.biUnion.{u3, u1} γ α (fun (a : α) (b : α) => _inst_1 a b) s t)) => f y))) (Set.iUnion.{u2, succ u3} β γ (fun (x : γ) => Set.iUnion.{u2, 0} β (Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) x s) (fun (H : Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) x s) => Set.iUnion.{u2, succ u1} β α (fun (y : α) => Set.iUnion.{u2, 0} β (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y (t x)) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y (t x)) => f y)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : DecidableEq.{succ u2} α] (s : Finset.{u3} γ) (t : γ -> (Finset.{u2} α)) (f : α -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Set.iUnion.{u1, succ u2} β α (fun (y : α) => Set.iUnion.{u1, 0} β (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) y (Finset.biUnion.{u3, u2} γ α (fun (a : α) (b : α) => _inst_1 a b) s t)) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) y (Finset.biUnion.{u3, u2} γ α (fun (a : α) (b : α) => _inst_1 a b) s t)) => f y))) (Set.iUnion.{u1, succ u3} β γ (fun (x : γ) => Set.iUnion.{u1, 0} β (Membership.mem.{u3, u3} γ (Finset.{u3} γ) (Finset.instMembershipFinset.{u3} γ) x s) (fun (H : Membership.mem.{u3, u3} γ (Finset.{u3} γ) (Finset.instMembershipFinset.{u3} γ) x s) => Set.iUnion.{u1, succ u2} β α (fun (y : α) => Set.iUnion.{u1, 0} β (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) y (t x)) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) y (t x)) => f y)))))
Case conversion may be inaccurate. Consider using '#align finset.set_bUnion_bUnion Finset.set_biUnion_biUnionₓ'. -/
theorem set_biUnion_biUnion (s : Finset γ) (t : γ → Finset α) (f : α → Set β) :
    (⋃ y ∈ s.biUnion t, f y) = ⋃ (x ∈ s) (y ∈ t x), f y :=
  iSup_biUnion s t f
#align finset.set_bUnion_bUnion Finset.set_biUnion_biUnion

/- warning: finset.set_bInter_bUnion -> Finset.set_biInter_biUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u3} γ) (t : γ -> (Finset.{u1} α)) (f : α -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (Set.iInter.{u2, succ u1} β α (fun (y : α) => Set.iInter.{u2, 0} β (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y (Finset.biUnion.{u3, u1} γ α (fun (a : α) (b : α) => _inst_1 a b) s t)) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y (Finset.biUnion.{u3, u1} γ α (fun (a : α) (b : α) => _inst_1 a b) s t)) => f y))) (Set.iInter.{u2, succ u3} β γ (fun (x : γ) => Set.iInter.{u2, 0} β (Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) x s) (fun (H : Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) x s) => Set.iInter.{u2, succ u1} β α (fun (y : α) => Set.iInter.{u2, 0} β (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y (t x)) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y (t x)) => f y)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : DecidableEq.{succ u2} α] (s : Finset.{u3} γ) (t : γ -> (Finset.{u2} α)) (f : α -> (Set.{u1} β)), Eq.{succ u1} (Set.{u1} β) (Set.iInter.{u1, succ u2} β α (fun (y : α) => Set.iInter.{u1, 0} β (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) y (Finset.biUnion.{u3, u2} γ α (fun (a : α) (b : α) => _inst_1 a b) s t)) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) y (Finset.biUnion.{u3, u2} γ α (fun (a : α) (b : α) => _inst_1 a b) s t)) => f y))) (Set.iInter.{u1, succ u3} β γ (fun (x : γ) => Set.iInter.{u1, 0} β (Membership.mem.{u3, u3} γ (Finset.{u3} γ) (Finset.instMembershipFinset.{u3} γ) x s) (fun (H : Membership.mem.{u3, u3} γ (Finset.{u3} γ) (Finset.instMembershipFinset.{u3} γ) x s) => Set.iInter.{u1, succ u2} β α (fun (y : α) => Set.iInter.{u1, 0} β (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) y (t x)) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) y (t x)) => f y)))))
Case conversion may be inaccurate. Consider using '#align finset.set_bInter_bUnion Finset.set_biInter_biUnionₓ'. -/
theorem set_biInter_biUnion (s : Finset γ) (t : γ → Finset α) (f : α → Set β) :
    (⋂ y ∈ s.biUnion t, f y) = ⋂ (x ∈ s) (y ∈ t x), f y :=
  iInf_biUnion s t f
#align finset.set_bInter_bUnion Finset.set_biInter_biUnion

end Finset

