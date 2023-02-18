/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Johannes Hölzl

! This file was ported from Lean 3 source module order.ord_continuous
! leanprover-community/mathlib commit 2738d2ca56cbc63be80c3bd48e9ed90ad94e947d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.ConditionallyCompleteLattice.Basic
import Mathbin.Order.RelIso.Basic

/-!
# Order continuity

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We say that a function is *left order continuous* if it sends all least upper bounds
to least upper bounds. The order dual notion is called *right order continuity*.

For monotone functions `ℝ → ℝ` these notions correspond to the usual left and right continuity.

We prove some basic lemmas (`map_sup`, `map_Sup` etc) and prove that an `rel_iso` is both left
and right order continuous.
-/


universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}

open Function OrderDual Set

/-!
### Definitions
-/


#print LeftOrdContinuous /-
/-- A function `f` between preorders is left order continuous if it preserves all suprema.  We
define it using `is_lub` instead of `Sup` so that the proof works both for complete lattices and
conditionally complete lattices. -/
def LeftOrdContinuous [Preorder α] [Preorder β] (f : α → β) :=
  ∀ ⦃s : Set α⦄ ⦃x⦄, IsLUB s x → IsLUB (f '' s) (f x)
#align left_ord_continuous LeftOrdContinuous
-/

#print RightOrdContinuous /-
/-- A function `f` between preorders is right order continuous if it preserves all infima.  We
define it using `is_glb` instead of `Inf` so that the proof works both for complete lattices and
conditionally complete lattices. -/
def RightOrdContinuous [Preorder α] [Preorder β] (f : α → β) :=
  ∀ ⦃s : Set α⦄ ⦃x⦄, IsGLB s x → IsGLB (f '' s) (f x)
#align right_ord_continuous RightOrdContinuous
-/

namespace LeftOrdContinuous

section Preorder

variable (α) [Preorder α] [Preorder β] [Preorder γ] {g : β → γ} {f : α → β}

#print LeftOrdContinuous.id /-
protected theorem id : LeftOrdContinuous (id : α → α) := fun s x h => by
  simpa only [image_id] using h
#align left_ord_continuous.id LeftOrdContinuous.id
-/

variable {α}

#print LeftOrdContinuous.order_dual /-
protected theorem order_dual : LeftOrdContinuous f → RightOrdContinuous (toDual ∘ f ∘ ofDual) :=
  id
#align left_ord_continuous.order_dual LeftOrdContinuous.order_dual
-/

#print LeftOrdContinuous.map_isGreatest /-
theorem map_isGreatest (hf : LeftOrdContinuous f) {s : Set α} {x : α} (h : IsGreatest s x) :
    IsGreatest (f '' s) (f x) :=
  ⟨mem_image_of_mem f h.1, (hf h.IsLUB).1⟩
#align left_ord_continuous.map_is_greatest LeftOrdContinuous.map_isGreatest
-/

#print LeftOrdContinuous.mono /-
theorem mono (hf : LeftOrdContinuous f) : Monotone f := fun a₁ a₂ h =>
  have : IsGreatest {a₁, a₂} a₂ := ⟨Or.inr rfl, by simp [*]⟩
  (hf.map_isGreatest this).2 <| mem_image_of_mem _ (Or.inl rfl)
#align left_ord_continuous.mono LeftOrdContinuous.mono
-/

#print LeftOrdContinuous.comp /-
theorem comp (hg : LeftOrdContinuous g) (hf : LeftOrdContinuous f) : LeftOrdContinuous (g ∘ f) :=
  fun s x h => by simpa only [image_image] using hg (hf h)
#align left_ord_continuous.comp LeftOrdContinuous.comp
-/

#print LeftOrdContinuous.iterate /-
protected theorem iterate {f : α → α} (hf : LeftOrdContinuous f) (n : ℕ) :
    LeftOrdContinuous (f^[n]) :=
  Nat.recOn n (LeftOrdContinuous.id α) fun n ihn => ihn.comp hf
#align left_ord_continuous.iterate LeftOrdContinuous.iterate
-/

end Preorder

section SemilatticeSup

variable [SemilatticeSup α] [SemilatticeSup β] {f : α → β}

#print LeftOrdContinuous.map_sup /-
theorem map_sup (hf : LeftOrdContinuous f) (x y : α) : f (x ⊔ y) = f x ⊔ f y :=
  (hf isLUB_pair).unique <| by simp only [image_pair, isLUB_pair]
#align left_ord_continuous.map_sup LeftOrdContinuous.map_sup
-/

#print LeftOrdContinuous.le_iff /-
theorem le_iff (hf : LeftOrdContinuous f) (h : Injective f) {x y} : f x ≤ f y ↔ x ≤ y := by
  simp only [← sup_eq_right, ← hf.map_sup, h.eq_iff]
#align left_ord_continuous.le_iff LeftOrdContinuous.le_iff
-/

#print LeftOrdContinuous.lt_iff /-
theorem lt_iff (hf : LeftOrdContinuous f) (h : Injective f) {x y} : f x < f y ↔ x < y := by
  simp only [lt_iff_le_not_le, hf.le_iff h]
#align left_ord_continuous.lt_iff LeftOrdContinuous.lt_iff
-/

variable (f)

#print LeftOrdContinuous.toOrderEmbedding /-
/-- Convert an injective left order continuous function to an order embedding. -/
def toOrderEmbedding (hf : LeftOrdContinuous f) (h : Injective f) : α ↪o β :=
  ⟨⟨f, h⟩, fun x y => hf.le_iff h⟩
#align left_ord_continuous.to_order_embedding LeftOrdContinuous.toOrderEmbedding
-/

variable {f}

/- warning: left_ord_continuous.coe_to_order_embedding -> LeftOrdContinuous.coe_toOrderEmbedding is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : SemilatticeSup.{u2} β] {f : α -> β} (hf : LeftOrdContinuous.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)) (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2)) f) (h : Function.Injective.{succ u1, succ u2} α β f), Eq.{max (succ u1) (succ u2)} (α -> β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderEmbedding.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2)))) (fun (_x : RelEmbedding.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2))))) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2))))) (LeftOrdContinuous.toOrderEmbedding.{u1, u2} α β _inst_1 _inst_2 f hf h)) f
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : SemilatticeSup.{u2} β] {f : α -> β} (hf : LeftOrdContinuous.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)) (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2)) f) (h : Function.Injective.{succ u1, succ u2} α β f), Eq.{max (succ u1) (succ u2)} (forall (ᾰ : α), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) ᾰ) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} α β)) (RelEmbedding.toEmbedding.{u1, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (LeftOrdContinuous.toOrderEmbedding.{u1, u2} α β _inst_1 _inst_2 f hf h))) f
Case conversion may be inaccurate. Consider using '#align left_ord_continuous.coe_to_order_embedding LeftOrdContinuous.coe_toOrderEmbeddingₓ'. -/
@[simp]
theorem coe_toOrderEmbedding (hf : LeftOrdContinuous f) (h : Injective f) :
    ⇑(hf.toOrderEmbedding f h) = f :=
  rfl
#align left_ord_continuous.coe_to_order_embedding LeftOrdContinuous.coe_toOrderEmbedding

end SemilatticeSup

section CompleteLattice

variable [CompleteLattice α] [CompleteLattice β] {f : α → β}

/- warning: left_ord_continuous.map_Sup' -> LeftOrdContinuous.map_supₛ' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {f : α -> β}, (LeftOrdContinuous.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) s)) (SupSet.supₛ.{u2} β (ConditionallyCompleteLattice.toHasSup.{u2} β (CompleteLattice.toConditionallyCompleteLattice.{u2} β _inst_2)) (Set.image.{u1, u2} α β f s)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {f : α -> β}, (LeftOrdContinuous.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) s)) (SupSet.supₛ.{u2} β (ConditionallyCompleteLattice.toSupSet.{u2} β (CompleteLattice.toConditionallyCompleteLattice.{u2} β _inst_2)) (Set.image.{u1, u2} α β f s)))
Case conversion may be inaccurate. Consider using '#align left_ord_continuous.map_Sup' LeftOrdContinuous.map_supₛ'ₓ'. -/
theorem map_supₛ' (hf : LeftOrdContinuous f) (s : Set α) : f (supₛ s) = supₛ (f '' s) :=
  (hf <| isLUB_supₛ s).supₛ_eq.symm
#align left_ord_continuous.map_Sup' LeftOrdContinuous.map_supₛ'

/- warning: left_ord_continuous.map_Sup -> LeftOrdContinuous.map_supₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {f : α -> β}, (LeftOrdContinuous.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) s)) (supᵢ.{u2, succ u1} β (ConditionallyCompleteLattice.toHasSup.{u2} β (CompleteLattice.toConditionallyCompleteLattice.{u2} β _inst_2)) α (fun (x : α) => supᵢ.{u2, 0} β (ConditionallyCompleteLattice.toHasSup.{u2} β (CompleteLattice.toConditionallyCompleteLattice.{u2} β _inst_2)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => f x))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {f : α -> β}, (LeftOrdContinuous.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) s)) (supᵢ.{u2, succ u1} β (ConditionallyCompleteLattice.toSupSet.{u2} β (CompleteLattice.toConditionallyCompleteLattice.{u2} β _inst_2)) α (fun (x : α) => supᵢ.{u2, 0} β (ConditionallyCompleteLattice.toSupSet.{u2} β (CompleteLattice.toConditionallyCompleteLattice.{u2} β _inst_2)) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) => f x))))
Case conversion may be inaccurate. Consider using '#align left_ord_continuous.map_Sup LeftOrdContinuous.map_supₛₓ'. -/
theorem map_supₛ (hf : LeftOrdContinuous f) (s : Set α) : f (supₛ s) = ⨆ x ∈ s, f x := by
  rw [hf.map_Sup', supₛ_image]
#align left_ord_continuous.map_Sup LeftOrdContinuous.map_supₛ

/- warning: left_ord_continuous.map_supr -> LeftOrdContinuous.map_supᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {f : α -> β}, (LeftOrdContinuous.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (forall (g : ι -> α), Eq.{succ u2} β (f (supᵢ.{u1, u3} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) ι (fun (i : ι) => g i))) (supᵢ.{u2, u3} β (ConditionallyCompleteLattice.toHasSup.{u2} β (CompleteLattice.toConditionallyCompleteLattice.{u2} β _inst_2)) ι (fun (i : ι) => f (g i))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {f : α -> β}, (LeftOrdContinuous.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (forall (g : ι -> α), Eq.{succ u2} β (f (supᵢ.{u1, u3} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) ι (fun (i : ι) => g i))) (supᵢ.{u2, u3} β (ConditionallyCompleteLattice.toSupSet.{u2} β (CompleteLattice.toConditionallyCompleteLattice.{u2} β _inst_2)) ι (fun (i : ι) => f (g i))))
Case conversion may be inaccurate. Consider using '#align left_ord_continuous.map_supr LeftOrdContinuous.map_supᵢₓ'. -/
theorem map_supᵢ (hf : LeftOrdContinuous f) (g : ι → α) : f (⨆ i, g i) = ⨆ i, f (g i) := by
  simp only [supᵢ, hf.map_Sup', ← range_comp]
#align left_ord_continuous.map_supr LeftOrdContinuous.map_supᵢ

end CompleteLattice

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β] [Nonempty ι] {f : α → β}

/- warning: left_ord_continuous.map_cSup -> LeftOrdContinuous.map_csupₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] {f : α -> β}, (LeftOrdContinuous.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) f) -> (forall {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Eq.{succ u2} β (f (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s)) (SupSet.supₛ.{u2} β (ConditionallyCompleteLattice.toHasSup.{u2} β _inst_2) (Set.image.{u1, u2} α β f s))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] {f : α -> β}, (LeftOrdContinuous.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) f) -> (forall {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Eq.{succ u2} β (f (SupSet.supₛ.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s)) (SupSet.supₛ.{u2} β (ConditionallyCompleteLattice.toSupSet.{u2} β _inst_2) (Set.image.{u1, u2} α β f s))))
Case conversion may be inaccurate. Consider using '#align left_ord_continuous.map_cSup LeftOrdContinuous.map_csupₛₓ'. -/
theorem map_csupₛ (hf : LeftOrdContinuous f) {s : Set α} (sne : s.Nonempty) (sbdd : BddAbove s) :
    f (supₛ s) = supₛ (f '' s) :=
  ((hf <| isLUB_csupₛ sne sbdd).csupₛ_eq <| sne.image f).symm
#align left_ord_continuous.map_cSup LeftOrdContinuous.map_csupₛ

/- warning: left_ord_continuous.map_csupr -> LeftOrdContinuous.map_csupᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] [_inst_3 : Nonempty.{u3} ι] {f : α -> β}, (LeftOrdContinuous.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) f) -> (forall {g : ι -> α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u3} α ι g)) -> (Eq.{succ u2} β (f (supᵢ.{u1, u3} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) ι (fun (i : ι) => g i))) (supᵢ.{u2, u3} β (ConditionallyCompleteLattice.toHasSup.{u2} β _inst_2) ι (fun (i : ι) => f (g i)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] [_inst_3 : Nonempty.{u3} ι] {f : α -> β}, (LeftOrdContinuous.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) f) -> (forall {g : ι -> α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u3} α ι g)) -> (Eq.{succ u2} β (f (supᵢ.{u1, u3} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (i : ι) => g i))) (supᵢ.{u2, u3} β (ConditionallyCompleteLattice.toSupSet.{u2} β _inst_2) ι (fun (i : ι) => f (g i)))))
Case conversion may be inaccurate. Consider using '#align left_ord_continuous.map_csupr LeftOrdContinuous.map_csupᵢₓ'. -/
theorem map_csupᵢ (hf : LeftOrdContinuous f) {g : ι → α} (hg : BddAbove (range g)) :
    f (⨆ i, g i) = ⨆ i, f (g i) := by
  simp only [supᵢ, hf.map_cSup (range_nonempty _) hg, ← range_comp]
#align left_ord_continuous.map_csupr LeftOrdContinuous.map_csupᵢ

end ConditionallyCompleteLattice

end LeftOrdContinuous

namespace RightOrdContinuous

section Preorder

variable (α) [Preorder α] [Preorder β] [Preorder γ] {g : β → γ} {f : α → β}

#print RightOrdContinuous.id /-
protected theorem id : RightOrdContinuous (id : α → α) := fun s x h => by
  simpa only [image_id] using h
#align right_ord_continuous.id RightOrdContinuous.id
-/

variable {α}

#print RightOrdContinuous.orderDual /-
protected theorem orderDual : RightOrdContinuous f → LeftOrdContinuous (toDual ∘ f ∘ ofDual) :=
  id
#align right_ord_continuous.order_dual RightOrdContinuous.orderDual
-/

#print RightOrdContinuous.map_isLeast /-
theorem map_isLeast (hf : RightOrdContinuous f) {s : Set α} {x : α} (h : IsLeast s x) :
    IsLeast (f '' s) (f x) :=
  hf.OrderDual.map_isGreatest h
#align right_ord_continuous.map_is_least RightOrdContinuous.map_isLeast
-/

#print RightOrdContinuous.mono /-
theorem mono (hf : RightOrdContinuous f) : Monotone f :=
  hf.OrderDual.mono.dual
#align right_ord_continuous.mono RightOrdContinuous.mono
-/

#print RightOrdContinuous.comp /-
theorem comp (hg : RightOrdContinuous g) (hf : RightOrdContinuous f) : RightOrdContinuous (g ∘ f) :=
  hg.OrderDual.comp hf.OrderDual
#align right_ord_continuous.comp RightOrdContinuous.comp
-/

#print RightOrdContinuous.iterate /-
protected theorem iterate {f : α → α} (hf : RightOrdContinuous f) (n : ℕ) :
    RightOrdContinuous (f^[n]) :=
  hf.OrderDual.iterate n
#align right_ord_continuous.iterate RightOrdContinuous.iterate
-/

end Preorder

section SemilatticeInf

variable [SemilatticeInf α] [SemilatticeInf β] {f : α → β}

#print RightOrdContinuous.map_inf /-
theorem map_inf (hf : RightOrdContinuous f) (x y : α) : f (x ⊓ y) = f x ⊓ f y :=
  hf.OrderDual.map_sup x y
#align right_ord_continuous.map_inf RightOrdContinuous.map_inf
-/

#print RightOrdContinuous.le_iff /-
theorem le_iff (hf : RightOrdContinuous f) (h : Injective f) {x y} : f x ≤ f y ↔ x ≤ y :=
  hf.OrderDual.le_iff h
#align right_ord_continuous.le_iff RightOrdContinuous.le_iff
-/

#print RightOrdContinuous.lt_iff /-
theorem lt_iff (hf : RightOrdContinuous f) (h : Injective f) {x y} : f x < f y ↔ x < y :=
  hf.OrderDual.lt_iff h
#align right_ord_continuous.lt_iff RightOrdContinuous.lt_iff
-/

variable (f)

#print RightOrdContinuous.toOrderEmbedding /-
/-- Convert an injective left order continuous function to a `order_embedding`. -/
def toOrderEmbedding (hf : RightOrdContinuous f) (h : Injective f) : α ↪o β :=
  ⟨⟨f, h⟩, fun x y => hf.le_iff h⟩
#align right_ord_continuous.to_order_embedding RightOrdContinuous.toOrderEmbedding
-/

variable {f}

/- warning: right_ord_continuous.coe_to_order_embedding -> RightOrdContinuous.coe_toOrderEmbedding is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : SemilatticeInf.{u2} β] {f : α -> β} (hf : RightOrdContinuous.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β _inst_2)) f) (h : Function.Injective.{succ u1, succ u2} α β f), Eq.{max (succ u1) (succ u2)} (α -> β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderEmbedding.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β _inst_2)))) (fun (_x : RelEmbedding.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β _inst_2))))) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β _inst_2))))) (RightOrdContinuous.toOrderEmbedding.{u1, u2} α β _inst_1 _inst_2 f hf h)) f
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : SemilatticeInf.{u2} β] {f : α -> β} (hf : RightOrdContinuous.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β _inst_2)) f) (h : Function.Injective.{succ u1, succ u2} α β f), Eq.{max (succ u1) (succ u2)} (forall (ᾰ : α), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) ᾰ) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} α β)) (RelEmbedding.toEmbedding.{u1, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β _inst_2))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (RightOrdContinuous.toOrderEmbedding.{u1, u2} α β _inst_1 _inst_2 f hf h))) f
Case conversion may be inaccurate. Consider using '#align right_ord_continuous.coe_to_order_embedding RightOrdContinuous.coe_toOrderEmbeddingₓ'. -/
@[simp]
theorem coe_toOrderEmbedding (hf : RightOrdContinuous f) (h : Injective f) :
    ⇑(hf.toOrderEmbedding f h) = f :=
  rfl
#align right_ord_continuous.coe_to_order_embedding RightOrdContinuous.coe_toOrderEmbedding

end SemilatticeInf

section CompleteLattice

variable [CompleteLattice α] [CompleteLattice β] {f : α → β}

/- warning: right_ord_continuous.map_Inf' -> RightOrdContinuous.map_infₛ' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {f : α -> β}, (RightOrdContinuous.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) s)) (InfSet.infₛ.{u2} β (ConditionallyCompleteLattice.toHasInf.{u2} β (CompleteLattice.toConditionallyCompleteLattice.{u2} β _inst_2)) (Set.image.{u1, u2} α β f s)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {f : α -> β}, (RightOrdContinuous.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) s)) (InfSet.infₛ.{u2} β (ConditionallyCompleteLattice.toInfSet.{u2} β (CompleteLattice.toConditionallyCompleteLattice.{u2} β _inst_2)) (Set.image.{u1, u2} α β f s)))
Case conversion may be inaccurate. Consider using '#align right_ord_continuous.map_Inf' RightOrdContinuous.map_infₛ'ₓ'. -/
theorem map_infₛ' (hf : RightOrdContinuous f) (s : Set α) : f (infₛ s) = infₛ (f '' s) :=
  hf.OrderDual.map_supₛ' s
#align right_ord_continuous.map_Inf' RightOrdContinuous.map_infₛ'

/- warning: right_ord_continuous.map_Inf -> RightOrdContinuous.map_infₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {f : α -> β}, (RightOrdContinuous.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) s)) (infᵢ.{u2, succ u1} β (ConditionallyCompleteLattice.toHasInf.{u2} β (CompleteLattice.toConditionallyCompleteLattice.{u2} β _inst_2)) α (fun (x : α) => infᵢ.{u2, 0} β (ConditionallyCompleteLattice.toHasInf.{u2} β (CompleteLattice.toConditionallyCompleteLattice.{u2} β _inst_2)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => f x))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {f : α -> β}, (RightOrdContinuous.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) s)) (infᵢ.{u2, succ u1} β (ConditionallyCompleteLattice.toInfSet.{u2} β (CompleteLattice.toConditionallyCompleteLattice.{u2} β _inst_2)) α (fun (x : α) => infᵢ.{u2, 0} β (ConditionallyCompleteLattice.toInfSet.{u2} β (CompleteLattice.toConditionallyCompleteLattice.{u2} β _inst_2)) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) => f x))))
Case conversion may be inaccurate. Consider using '#align right_ord_continuous.map_Inf RightOrdContinuous.map_infₛₓ'. -/
theorem map_infₛ (hf : RightOrdContinuous f) (s : Set α) : f (infₛ s) = ⨅ x ∈ s, f x :=
  hf.OrderDual.map_supₛ s
#align right_ord_continuous.map_Inf RightOrdContinuous.map_infₛ

/- warning: right_ord_continuous.map_infi -> RightOrdContinuous.map_infᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {f : α -> β}, (RightOrdContinuous.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (forall (g : ι -> α), Eq.{succ u2} β (f (infᵢ.{u1, u3} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) ι (fun (i : ι) => g i))) (infᵢ.{u2, u3} β (ConditionallyCompleteLattice.toHasInf.{u2} β (CompleteLattice.toConditionallyCompleteLattice.{u2} β _inst_2)) ι (fun (i : ι) => f (g i))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {f : α -> β}, (RightOrdContinuous.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (forall (g : ι -> α), Eq.{succ u2} β (f (infᵢ.{u1, u3} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) ι (fun (i : ι) => g i))) (infᵢ.{u2, u3} β (ConditionallyCompleteLattice.toInfSet.{u2} β (CompleteLattice.toConditionallyCompleteLattice.{u2} β _inst_2)) ι (fun (i : ι) => f (g i))))
Case conversion may be inaccurate. Consider using '#align right_ord_continuous.map_infi RightOrdContinuous.map_infᵢₓ'. -/
theorem map_infᵢ (hf : RightOrdContinuous f) (g : ι → α) : f (⨅ i, g i) = ⨅ i, f (g i) :=
  hf.OrderDual.map_supᵢ g
#align right_ord_continuous.map_infi RightOrdContinuous.map_infᵢ

end CompleteLattice

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β] [Nonempty ι] {f : α → β}

/- warning: right_ord_continuous.map_cInf -> RightOrdContinuous.map_cinfₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] {f : α -> β}, (RightOrdContinuous.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) f) -> (forall {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Eq.{succ u2} β (f (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s)) (InfSet.infₛ.{u2} β (ConditionallyCompleteLattice.toHasInf.{u2} β _inst_2) (Set.image.{u1, u2} α β f s))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] {f : α -> β}, (RightOrdContinuous.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) f) -> (forall {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Eq.{succ u2} β (f (InfSet.infₛ.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s)) (InfSet.infₛ.{u2} β (ConditionallyCompleteLattice.toInfSet.{u2} β _inst_2) (Set.image.{u1, u2} α β f s))))
Case conversion may be inaccurate. Consider using '#align right_ord_continuous.map_cInf RightOrdContinuous.map_cinfₛₓ'. -/
theorem map_cinfₛ (hf : RightOrdContinuous f) {s : Set α} (sne : s.Nonempty) (sbdd : BddBelow s) :
    f (infₛ s) = infₛ (f '' s) :=
  hf.OrderDual.map_csupₛ sne sbdd
#align right_ord_continuous.map_cInf RightOrdContinuous.map_cinfₛ

/- warning: right_ord_continuous.map_cinfi -> RightOrdContinuous.map_cinfᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] [_inst_3 : Nonempty.{u3} ι] {f : α -> β}, (RightOrdContinuous.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) f) -> (forall {g : ι -> α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u3} α ι g)) -> (Eq.{succ u2} β (f (infᵢ.{u1, u3} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) ι (fun (i : ι) => g i))) (infᵢ.{u2, u3} β (ConditionallyCompleteLattice.toHasInf.{u2} β _inst_2) ι (fun (i : ι) => f (g i)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] [_inst_2 : ConditionallyCompleteLattice.{u2} β] [_inst_3 : Nonempty.{u3} ι] {f : α -> β}, (RightOrdContinuous.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β _inst_2)))) f) -> (forall {g : ι -> α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) (Set.range.{u1, u3} α ι g)) -> (Eq.{succ u2} β (f (infᵢ.{u1, u3} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) ι (fun (i : ι) => g i))) (infᵢ.{u2, u3} β (ConditionallyCompleteLattice.toInfSet.{u2} β _inst_2) ι (fun (i : ι) => f (g i)))))
Case conversion may be inaccurate. Consider using '#align right_ord_continuous.map_cinfi RightOrdContinuous.map_cinfᵢₓ'. -/
theorem map_cinfᵢ (hf : RightOrdContinuous f) {g : ι → α} (hg : BddBelow (range g)) :
    f (⨅ i, g i) = ⨅ i, f (g i) :=
  hf.OrderDual.map_csupᵢ hg
#align right_ord_continuous.map_cinfi RightOrdContinuous.map_cinfᵢ

end ConditionallyCompleteLattice

end RightOrdContinuous

namespace OrderIso

section Preorder

variable [Preorder α] [Preorder β] (e : α ≃o β) {s : Set α} {x : α}

/- warning: order_iso.left_ord_continuous -> OrderIso.leftOrdContinuous is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] (e : OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)), LeftOrdContinuous.{u1, u2} α β _inst_1 _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) e)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] (e : OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)), LeftOrdContinuous.{u1, u2} α β _inst_1 _inst_2 (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} α β)) (RelEmbedding.toEmbedding.{u1, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{u1, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) e)))
Case conversion may be inaccurate. Consider using '#align order_iso.left_ord_continuous OrderIso.leftOrdContinuousₓ'. -/
protected theorem leftOrdContinuous : LeftOrdContinuous e := fun s x hx =>
  ⟨Monotone.mem_upperBounds_image (fun x y => e.map_rel_iff.2) hx.1, fun y hy =>
    e.rel_symm_apply.1 <|
      (isLUB_le_iff hx).2 fun x' hx' => e.rel_symm_apply.2 <| hy <| mem_image_of_mem _ hx'⟩
#align order_iso.left_ord_continuous OrderIso.leftOrdContinuous

/- warning: order_iso.right_ord_continuous -> OrderIso.rightOrdContinuous is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] (e : OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)), RightOrdContinuous.{u1, u2} α β _inst_1 _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) e)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] (e : OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)), RightOrdContinuous.{u1, u2} α β _inst_1 _inst_2 (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} α β)) (RelEmbedding.toEmbedding.{u1, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{u1, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) e)))
Case conversion may be inaccurate. Consider using '#align order_iso.right_ord_continuous OrderIso.rightOrdContinuousₓ'. -/
protected theorem rightOrdContinuous : RightOrdContinuous e :=
  OrderIso.leftOrdContinuous e.dual
#align order_iso.right_ord_continuous OrderIso.rightOrdContinuous

end Preorder

end OrderIso

