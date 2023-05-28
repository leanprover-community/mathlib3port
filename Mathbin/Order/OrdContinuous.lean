/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Johannes Hölzl

! This file was ported from Lean 3 source module order.ord_continuous
! leanprover-community/mathlib commit c3291da49cfa65f0d43b094750541c0731edc932
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

theorem map_sup (hf : LeftOrdContinuous f) (x y : α) : f (x ⊔ y) = f x ⊔ f y :=
  (hf isLUB_pair).unique <| by simp only [image_pair, isLUB_pair]
#align left_ord_continuous.map_sup LeftOrdContinuous.map_sup

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

@[simp]
theorem coe_toOrderEmbedding (hf : LeftOrdContinuous f) (h : Injective f) :
    ⇑(hf.toOrderEmbedding f h) = f :=
  rfl
#align left_ord_continuous.coe_to_order_embedding LeftOrdContinuous.coe_toOrderEmbedding

end SemilatticeSup

section CompleteLattice

variable [CompleteLattice α] [CompleteLattice β] {f : α → β}

theorem map_sSup' (hf : LeftOrdContinuous f) (s : Set α) : f (sSup s) = sSup (f '' s) :=
  (hf <| isLUB_sSup s).sSup_eq.symm
#align left_ord_continuous.map_Sup' LeftOrdContinuous.map_sSup'

theorem map_sSup (hf : LeftOrdContinuous f) (s : Set α) : f (sSup s) = ⨆ x ∈ s, f x := by
  rw [hf.map_Sup', sSup_image]
#align left_ord_continuous.map_Sup LeftOrdContinuous.map_sSup

theorem map_iSup (hf : LeftOrdContinuous f) (g : ι → α) : f (⨆ i, g i) = ⨆ i, f (g i) := by
  simp only [iSup, hf.map_Sup', ← range_comp]
#align left_ord_continuous.map_supr LeftOrdContinuous.map_iSup

end CompleteLattice

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β] [Nonempty ι] {f : α → β}

theorem map_csSup (hf : LeftOrdContinuous f) {s : Set α} (sne : s.Nonempty) (sbdd : BddAbove s) :
    f (sSup s) = sSup (f '' s) :=
  ((hf <| isLUB_csSup sne sbdd).csSup_eq <| sne.image f).symm
#align left_ord_continuous.map_cSup LeftOrdContinuous.map_csSup

theorem map_ciSup (hf : LeftOrdContinuous f) {g : ι → α} (hg : BddAbove (range g)) :
    f (⨆ i, g i) = ⨆ i, f (g i) := by
  simp only [iSup, hf.map_cSup (range_nonempty _) hg, ← range_comp]
#align left_ord_continuous.map_csupr LeftOrdContinuous.map_ciSup

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

theorem map_inf (hf : RightOrdContinuous f) (x y : α) : f (x ⊓ y) = f x ⊓ f y :=
  hf.OrderDual.map_sup x y
#align right_ord_continuous.map_inf RightOrdContinuous.map_inf

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

@[simp]
theorem coe_toOrderEmbedding (hf : RightOrdContinuous f) (h : Injective f) :
    ⇑(hf.toOrderEmbedding f h) = f :=
  rfl
#align right_ord_continuous.coe_to_order_embedding RightOrdContinuous.coe_toOrderEmbedding

end SemilatticeInf

section CompleteLattice

variable [CompleteLattice α] [CompleteLattice β] {f : α → β}

theorem map_sInf' (hf : RightOrdContinuous f) (s : Set α) : f (sInf s) = sInf (f '' s) :=
  hf.OrderDual.map_sSup' s
#align right_ord_continuous.map_Inf' RightOrdContinuous.map_sInf'

theorem map_sInf (hf : RightOrdContinuous f) (s : Set α) : f (sInf s) = ⨅ x ∈ s, f x :=
  hf.OrderDual.map_sSup s
#align right_ord_continuous.map_Inf RightOrdContinuous.map_sInf

theorem map_iInf (hf : RightOrdContinuous f) (g : ι → α) : f (⨅ i, g i) = ⨅ i, f (g i) :=
  hf.OrderDual.map_iSup g
#align right_ord_continuous.map_infi RightOrdContinuous.map_iInf

end CompleteLattice

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β] [Nonempty ι] {f : α → β}

theorem map_csInf (hf : RightOrdContinuous f) {s : Set α} (sne : s.Nonempty) (sbdd : BddBelow s) :
    f (sInf s) = sInf (f '' s) :=
  hf.OrderDual.map_csSup sne sbdd
#align right_ord_continuous.map_cInf RightOrdContinuous.map_csInf

theorem map_ciInf (hf : RightOrdContinuous f) {g : ι → α} (hg : BddBelow (range g)) :
    f (⨅ i, g i) = ⨅ i, f (g i) :=
  hf.OrderDual.map_ciSup hg
#align right_ord_continuous.map_cinfi RightOrdContinuous.map_ciInf

end ConditionallyCompleteLattice

end RightOrdContinuous

namespace OrderIso

section Preorder

variable [Preorder α] [Preorder β] (e : α ≃o β) {s : Set α} {x : α}

protected theorem leftOrdContinuous : LeftOrdContinuous e := fun s x hx =>
  ⟨Monotone.mem_upperBounds_image (fun x y => e.map_rel_iff.2) hx.1, fun y hy =>
    e.rel_symm_apply.1 <|
      (isLUB_le_iff hx).2 fun x' hx' => e.rel_symm_apply.2 <| hy <| mem_image_of_mem _ hx'⟩
#align order_iso.left_ord_continuous OrderIso.leftOrdContinuous

protected theorem rightOrdContinuous : RightOrdContinuous e :=
  OrderIso.leftOrdContinuous e.dual
#align order_iso.right_ord_continuous OrderIso.rightOrdContinuous

end Preorder

end OrderIso

