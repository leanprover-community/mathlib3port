/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Violeta Hernández Palacios, Grayson Burton, Floris van Doorn

! This file was ported from Lean 3 source module order.cover
! leanprover-community/mathlib commit dd71334db81d0bd444af1ee339a29298bef40734
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Intervals.OrdConnected
import Mathbin.Order.Antisymmetrization

/-!
# The covering relation

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the covering relation in an order. `b` is said to cover `a` if `a < b` and there
is no element in between. We say that `b` weakly covers `a` if `a ≤ b` and there is no element
between `a` and `b`. In a partial order this is equivalent to `a ⋖ b ∨ a = b`, in a preorder this
is equivalent to `a ⋖ b ∨ (a ≤ b ∧ b ≤ a)`

## Notation

* `a ⋖ b` means that `b` covers `a`.
* `a ⩿ b` means that `b` weakly covers `a`.
-/


open Set OrderDual

variable {α β : Type _}

section WeaklyCovers

section Preorder

variable [Preorder α] [Preorder β] {a b c : α}

#print Wcovby /-
/-- `wcovby a b` means that `a = b` or `b` covers `a`.
This means that `a ≤ b` and there is no element in between.
-/
def Wcovby (a b : α) : Prop :=
  a ≤ b ∧ ∀ ⦃c⦄, a < c → ¬c < b
#align wcovby Wcovby
-/

-- mathport name: «expr ⩿ »
infixl:50 " ⩿ " => Wcovby

#print Wcovby.le /-
theorem Wcovby.le (h : a ⩿ b) : a ≤ b :=
  h.1
#align wcovby.le Wcovby.le
-/

#print Wcovby.refl /-
theorem Wcovby.refl (a : α) : a ⩿ a :=
  ⟨le_rfl, fun c hc => hc.not_lt⟩
#align wcovby.refl Wcovby.refl
-/

#print Wcovby.rfl /-
theorem Wcovby.rfl : a ⩿ a :=
  Wcovby.refl a
#align wcovby.rfl Wcovby.rfl
-/

#print Eq.wcovby /-
protected theorem Eq.wcovby (h : a = b) : a ⩿ b :=
  h ▸ Wcovby.rfl
#align eq.wcovby Eq.wcovby
-/

#print wcovby_of_le_of_le /-
theorem wcovby_of_le_of_le (h1 : a ≤ b) (h2 : b ≤ a) : a ⩿ b :=
  ⟨h1, fun c hac hcb => (hac.trans hcb).not_le h2⟩
#align wcovby_of_le_of_le wcovby_of_le_of_le
-/

alias wcovby_of_le_of_le ← LE.le.wcovby_of_le

#print AntisymmRel.wcovby /-
theorem AntisymmRel.wcovby (h : AntisymmRel (· ≤ ·) a b) : a ⩿ b :=
  wcovby_of_le_of_le h.1 h.2
#align antisymm_rel.wcovby AntisymmRel.wcovby
-/

#print Wcovby.wcovby_iff_le /-
theorem Wcovby.wcovby_iff_le (hab : a ⩿ b) : b ⩿ a ↔ b ≤ a :=
  ⟨fun h => h.le, fun h => h.wcovby_of_le hab.le⟩
#align wcovby.wcovby_iff_le Wcovby.wcovby_iff_le
-/

#print wcovby_of_eq_or_eq /-
theorem wcovby_of_eq_or_eq (hab : a ≤ b) (h : ∀ c, a ≤ c → c ≤ b → c = a ∨ c = b) : a ⩿ b :=
  ⟨hab, fun c ha hb => (h c ha.le hb.le).elim ha.ne' hb.Ne⟩
#align wcovby_of_eq_or_eq wcovby_of_eq_or_eq
-/

#print AntisymmRel.trans_wcovby /-
theorem AntisymmRel.trans_wcovby (hab : AntisymmRel (· ≤ ·) a b) (hbc : b ⩿ c) : a ⩿ c :=
  ⟨hab.1.trans hbc.le, fun d had hdc => hbc.2 (hab.2.trans_lt had) hdc⟩
#align antisymm_rel.trans_wcovby AntisymmRel.trans_wcovby
-/

#print wcovby_congr_left /-
theorem wcovby_congr_left (hab : AntisymmRel (· ≤ ·) a b) : a ⩿ c ↔ b ⩿ c :=
  ⟨hab.symm.trans_wcovby, hab.trans_wcovby⟩
#align wcovby_congr_left wcovby_congr_left
-/

#print Wcovby.trans_antisymm_rel /-
theorem Wcovby.trans_antisymm_rel (hab : a ⩿ b) (hbc : AntisymmRel (· ≤ ·) b c) : a ⩿ c :=
  ⟨hab.le.trans hbc.1, fun d had hdc => hab.2 had <| hdc.trans_le hbc.2⟩
#align wcovby.trans_antisymm_rel Wcovby.trans_antisymm_rel
-/

#print wcovby_congr_right /-
theorem wcovby_congr_right (hab : AntisymmRel (· ≤ ·) a b) : c ⩿ a ↔ c ⩿ b :=
  ⟨fun h => h.trans_antisymm_rel hab, fun h => h.trans_antisymm_rel hab.symm⟩
#align wcovby_congr_right wcovby_congr_right
-/

#print not_wcovby_iff /-
/-- If `a ≤ b`, then `b` does not cover `a` iff there's an element in between. -/
theorem not_wcovby_iff (h : a ≤ b) : ¬a ⩿ b ↔ ∃ c, a < c ∧ c < b := by
  simp_rw [Wcovby, h, true_and_iff, not_forall, exists_prop, not_not]
#align not_wcovby_iff not_wcovby_iff
-/

#print Wcovby.isRefl /-
instance Wcovby.isRefl : IsRefl α (· ⩿ ·) :=
  ⟨Wcovby.refl⟩
#align wcovby.is_refl Wcovby.isRefl
-/

#print Wcovby.Ioo_eq /-
theorem Wcovby.Ioo_eq (h : a ⩿ b) : Ioo a b = ∅ :=
  eq_empty_iff_forall_not_mem.2 fun x hx => h.2 hx.1 hx.2
#align wcovby.Ioo_eq Wcovby.Ioo_eq
-/

#print wcovby_iff_Ioo_eq /-
theorem wcovby_iff_Ioo_eq : a ⩿ b ↔ a ≤ b ∧ Ioo a b = ∅ :=
  and_congr_right' <| by simp [eq_empty_iff_forall_not_mem]
#align wcovby_iff_Ioo_eq wcovby_iff_Ioo_eq
-/

/- warning: wcovby.of_image -> Wcovby.of_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {a : α} {b : α} (f : OrderEmbedding.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)), (Wcovby.{u2} β _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderEmbedding.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)) (fun (_x : RelEmbedding.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) f a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderEmbedding.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)) (fun (_x : RelEmbedding.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) f b)) -> (Wcovby.{u1} α _inst_1 a b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {a : α} {b : α} (f : OrderEmbedding.{u2, u1} α β (Preorder.toLE.{u2} α _inst_1) (Preorder.toLE.{u1} β _inst_2)), (Wcovby.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) _inst_2 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.744 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.746 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.744 x._@.Mathlib.Order.Hom.Basic._hyg.746) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.759 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.761 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) x._@.Mathlib.Order.Hom.Basic._hyg.759 x._@.Mathlib.Order.Hom.Basic._hyg.761) f) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.744 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.746 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.744 x._@.Mathlib.Order.Hom.Basic._hyg.746) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.759 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.761 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) x._@.Mathlib.Order.Hom.Basic._hyg.759 x._@.Mathlib.Order.Hom.Basic._hyg.761) f) b)) -> (Wcovby.{u2} α _inst_1 a b)
Case conversion may be inaccurate. Consider using '#align wcovby.of_image Wcovby.of_imageₓ'. -/
theorem Wcovby.of_image (f : α ↪o β) (h : f a ⩿ f b) : a ⩿ b :=
  ⟨f.le_iff_le.mp h.le, fun c hac hcb => h.2 (f.lt_iff_lt.mpr hac) (f.lt_iff_lt.mpr hcb)⟩
#align wcovby.of_image Wcovby.of_image

/- warning: wcovby.image -> Wcovby.image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {a : α} {b : α} (f : OrderEmbedding.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)), (Wcovby.{u1} α _inst_1 a b) -> (Set.OrdConnected.{u2} β _inst_2 (Set.range.{u2, succ u1} β α (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderEmbedding.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)) (fun (_x : RelEmbedding.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) f))) -> (Wcovby.{u2} β _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderEmbedding.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)) (fun (_x : RelEmbedding.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) f a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderEmbedding.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)) (fun (_x : RelEmbedding.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) f b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {a : α} {b : α} (f : OrderEmbedding.{u2, u1} α β (Preorder.toLE.{u2} α _inst_1) (Preorder.toLE.{u1} β _inst_2)), (Wcovby.{u2} α _inst_1 a b) -> (Set.OrdConnected.{u1} β _inst_2 (Set.range.{u1, succ u2} β α (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.744 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.746 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.744 x._@.Mathlib.Order.Hom.Basic._hyg.746) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.759 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.761 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) x._@.Mathlib.Order.Hom.Basic._hyg.759 x._@.Mathlib.Order.Hom.Basic._hyg.761) f)))) -> (Wcovby.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) _inst_2 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.744 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.746 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.744 x._@.Mathlib.Order.Hom.Basic._hyg.746) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.759 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.761 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) x._@.Mathlib.Order.Hom.Basic._hyg.759 x._@.Mathlib.Order.Hom.Basic._hyg.761) f) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.744 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.746 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.744 x._@.Mathlib.Order.Hom.Basic._hyg.746) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.759 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.761 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) x._@.Mathlib.Order.Hom.Basic._hyg.759 x._@.Mathlib.Order.Hom.Basic._hyg.761) f) b))
Case conversion may be inaccurate. Consider using '#align wcovby.image Wcovby.imageₓ'. -/
theorem Wcovby.image (f : α ↪o β) (hab : a ⩿ b) (h : (range f).OrdConnected) : f a ⩿ f b :=
  by
  refine' ⟨f.monotone hab.le, fun c ha hb => _⟩
  obtain ⟨c, rfl⟩ := h.out (mem_range_self _) (mem_range_self _) ⟨ha.le, hb.le⟩
  rw [f.lt_iff_lt] at ha hb
  exact hab.2 ha hb
#align wcovby.image Wcovby.image

/- warning: set.ord_connected.apply_wcovby_apply_iff -> Set.OrdConnected.apply_wcovby_apply_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {a : α} {b : α} (f : OrderEmbedding.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)), (Set.OrdConnected.{u2} β _inst_2 (Set.range.{u2, succ u1} β α (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderEmbedding.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)) (fun (_x : RelEmbedding.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) f))) -> (Iff (Wcovby.{u2} β _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderEmbedding.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)) (fun (_x : RelEmbedding.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) f a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderEmbedding.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)) (fun (_x : RelEmbedding.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) f b)) (Wcovby.{u1} α _inst_1 a b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {a : α} {b : α} (f : OrderEmbedding.{u2, u1} α β (Preorder.toLE.{u2} α _inst_1) (Preorder.toLE.{u1} β _inst_2)), (Set.OrdConnected.{u1} β _inst_2 (Set.range.{u1, succ u2} β α (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.744 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.746 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.744 x._@.Mathlib.Order.Hom.Basic._hyg.746) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.759 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.761 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) x._@.Mathlib.Order.Hom.Basic._hyg.759 x._@.Mathlib.Order.Hom.Basic._hyg.761) f)))) -> (Iff (Wcovby.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) _inst_2 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.744 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.746 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.744 x._@.Mathlib.Order.Hom.Basic._hyg.746) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.759 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.761 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) x._@.Mathlib.Order.Hom.Basic._hyg.759 x._@.Mathlib.Order.Hom.Basic._hyg.761) f) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.744 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.746 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.744 x._@.Mathlib.Order.Hom.Basic._hyg.746) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.759 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.761 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) x._@.Mathlib.Order.Hom.Basic._hyg.759 x._@.Mathlib.Order.Hom.Basic._hyg.761) f) b)) (Wcovby.{u2} α _inst_1 a b))
Case conversion may be inaccurate. Consider using '#align set.ord_connected.apply_wcovby_apply_iff Set.OrdConnected.apply_wcovby_apply_iffₓ'. -/
theorem Set.OrdConnected.apply_wcovby_apply_iff (f : α ↪o β) (h : (range f).OrdConnected) :
    f a ⩿ f b ↔ a ⩿ b :=
  ⟨fun h2 => h2.of_image f, fun hab => hab.image f h⟩
#align set.ord_connected.apply_wcovby_apply_iff Set.OrdConnected.apply_wcovby_apply_iff

/- warning: apply_wcovby_apply_iff -> apply_wcovby_apply_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {a : α} {b : α} {E : Type.{u3}} [_inst_3 : OrderIsoClass.{u3, u1, u2} E α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)] (e : E), Iff (Wcovby.{u2} β _inst_2 (coeFn.{succ u3, max (succ u1) (succ u2)} E (fun (_x : E) => α -> β) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} E α (fun (_x : α) => β) (RelHomClass.toFunLike.{u3, u1, u2} E α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2)) (OrderIsoClass.toOrderHomClass.{u3, u1, u2} E α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2) _inst_3))) e a) (coeFn.{succ u3, max (succ u1) (succ u2)} E (fun (_x : E) => α -> β) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} E α (fun (_x : α) => β) (RelHomClass.toFunLike.{u3, u1, u2} E α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2)) (OrderIsoClass.toOrderHomClass.{u3, u1, u2} E α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2) _inst_3))) e b)) (Wcovby.{u1} α _inst_1 a b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {a : α} {b : α} {E : Type.{u3}} [_inst_3 : OrderIsoClass.{u3, u2, u1} E α β (Preorder.toLE.{u2} α _inst_1) (Preorder.toLE.{u1} β _inst_2)] (e : E), Iff (Wcovby.{u1} ((fun (x._@.Mathlib.Order.RelIso.Basic._hyg.931 : α) => β) a) _inst_2 (FunLike.coe.{succ u3, succ u2, succ u1} E α (fun (_x : α) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.931 : α) => β) _x) (RelHomClass.toFunLike.{u3, u2, u1} E α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.2092 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.2094 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.2092 x._@.Mathlib.Order.Hom.Basic._hyg.2094) (fun (_x : β) (x._@.Mathlib.Order.Hom.Basic._hyg.2116 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) _x x._@.Mathlib.Order.Hom.Basic._hyg.2116) (OrderIsoClass.toOrderHomClass.{u3, u2, u1} E α β (Preorder.toLE.{u2} α _inst_1) (Preorder.toLE.{u1} β _inst_2) _inst_3)) e a) (FunLike.coe.{succ u3, succ u2, succ u1} E α (fun (_x : α) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.931 : α) => β) _x) (RelHomClass.toFunLike.{u3, u2, u1} E α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.2092 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.2094 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.2092 x._@.Mathlib.Order.Hom.Basic._hyg.2094) (fun (_x : β) (x._@.Mathlib.Order.Hom.Basic._hyg.2116 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) _x x._@.Mathlib.Order.Hom.Basic._hyg.2116) (OrderIsoClass.toOrderHomClass.{u3, u2, u1} E α β (Preorder.toLE.{u2} α _inst_1) (Preorder.toLE.{u1} β _inst_2) _inst_3)) e b)) (Wcovby.{u2} α _inst_1 a b)
Case conversion may be inaccurate. Consider using '#align apply_wcovby_apply_iff apply_wcovby_apply_iffₓ'. -/
@[simp]
theorem apply_wcovby_apply_iff {E : Type _} [OrderIsoClass E α β] (e : E) : e a ⩿ e b ↔ a ⩿ b :=
  (ordConnected_range (e : α ≃o β)).apply_wcovby_apply_iff ((e : α ≃o β) : α ↪o β)
#align apply_wcovby_apply_iff apply_wcovby_apply_iff

#print toDual_wcovby_toDual_iff /-
@[simp]
theorem toDual_wcovby_toDual_iff : toDual b ⩿ toDual a ↔ a ⩿ b :=
  and_congr_right' <| forall_congr' fun c => forall_swap
#align to_dual_wcovby_to_dual_iff toDual_wcovby_toDual_iff
-/

#print ofDual_wcovby_ofDual_iff /-
@[simp]
theorem ofDual_wcovby_ofDual_iff {a b : αᵒᵈ} : ofDual a ⩿ ofDual b ↔ b ⩿ a :=
  and_congr_right' <| forall_congr' fun c => forall_swap
#align of_dual_wcovby_of_dual_iff ofDual_wcovby_ofDual_iff
-/

alias toDual_wcovby_toDual_iff ↔ _ Wcovby.to_dual

alias ofDual_wcovby_ofDual_iff ↔ _ Wcovby.of_dual

end Preorder

section PartialOrder

variable [PartialOrder α] {a b c : α}

#print Wcovby.eq_or_eq /-
theorem Wcovby.eq_or_eq (h : a ⩿ b) (h2 : a ≤ c) (h3 : c ≤ b) : c = a ∨ c = b :=
  by
  rcases h2.eq_or_lt with (h2 | h2); · exact Or.inl h2.symm
  rcases h3.eq_or_lt with (h3 | h3); · exact Or.inr h3
  exact (h.2 h2 h3).elim
#align wcovby.eq_or_eq Wcovby.eq_or_eq
-/

#print wcovby_iff_le_and_eq_or_eq /-
/-- An `iff` version of `wcovby.eq_or_eq` and `wcovby_of_eq_or_eq`. -/
theorem wcovby_iff_le_and_eq_or_eq : a ⩿ b ↔ a ≤ b ∧ ∀ c, a ≤ c → c ≤ b → c = a ∨ c = b :=
  ⟨fun h => ⟨h.le, fun c => h.eq_or_eq⟩, And.ndrec wcovby_of_eq_or_eq⟩
#align wcovby_iff_le_and_eq_or_eq wcovby_iff_le_and_eq_or_eq
-/

#print Wcovby.le_and_le_iff /-
theorem Wcovby.le_and_le_iff (h : a ⩿ b) : a ≤ c ∧ c ≤ b ↔ c = a ∨ c = b := by
  refine' ⟨fun h2 => h.eq_or_eq h2.1 h2.2, _⟩; rintro (rfl | rfl);
  exacts[⟨le_rfl, h.le⟩, ⟨h.le, le_rfl⟩]
#align wcovby.le_and_le_iff Wcovby.le_and_le_iff
-/

#print Wcovby.Icc_eq /-
theorem Wcovby.Icc_eq (h : a ⩿ b) : Icc a b = {a, b} :=
  by
  ext c
  exact h.le_and_le_iff
#align wcovby.Icc_eq Wcovby.Icc_eq
-/

#print Wcovby.Ico_subset /-
theorem Wcovby.Ico_subset (h : a ⩿ b) : Ico a b ⊆ {a} := by
  rw [← Icc_diff_right, h.Icc_eq, diff_singleton_subset_iff, pair_comm]
#align wcovby.Ico_subset Wcovby.Ico_subset
-/

#print Wcovby.Ioc_subset /-
theorem Wcovby.Ioc_subset (h : a ⩿ b) : Ioc a b ⊆ {b} := by
  rw [← Icc_diff_left, h.Icc_eq, diff_singleton_subset_iff]
#align wcovby.Ioc_subset Wcovby.Ioc_subset
-/

end PartialOrder

section SemilatticeSup

variable [SemilatticeSup α] {a b c : α}

#print Wcovby.sup_eq /-
theorem Wcovby.sup_eq (hac : a ⩿ c) (hbc : b ⩿ c) (hab : a ≠ b) : a ⊔ b = c :=
  (sup_le hac.le hbc.le).eq_of_not_lt fun h =>
    hab.lt_sup_or_lt_sup.elim (fun h' => hac.2 h' h) fun h' => hbc.2 h' h
#align wcovby.sup_eq Wcovby.sup_eq
-/

end SemilatticeSup

section SemilatticeInf

variable [SemilatticeInf α] {a b c : α}

#print Wcovby.inf_eq /-
theorem Wcovby.inf_eq (hca : c ⩿ a) (hcb : c ⩿ b) (hab : a ≠ b) : a ⊓ b = c :=
  (le_inf hca.le hcb.le).eq_of_not_gt fun h => hab.inf_lt_or_inf_lt.elim (hca.2 h) (hcb.2 h)
#align wcovby.inf_eq Wcovby.inf_eq
-/

end SemilatticeInf

end WeaklyCovers

section LT

variable [LT α] {a b : α}

#print Covby /-
/-- `covby a b` means that `b` covers `a`: `a < b` and there is no element in between. -/
def Covby (a b : α) : Prop :=
  a < b ∧ ∀ ⦃c⦄, a < c → ¬c < b
#align covby Covby
-/

-- mathport name: «expr ⋖ »
infixl:50 " ⋖ " => Covby

#print Covby.lt /-
theorem Covby.lt (h : a ⋖ b) : a < b :=
  h.1
#align covby.lt Covby.lt
-/

#print not_covby_iff /-
/-- If `a < b`, then `b` does not cover `a` iff there's an element in between. -/
theorem not_covby_iff (h : a < b) : ¬a ⋖ b ↔ ∃ c, a < c ∧ c < b := by
  simp_rw [Covby, h, true_and_iff, not_forall, exists_prop, not_not]
#align not_covby_iff not_covby_iff
-/

alias not_covby_iff ↔ exists_lt_lt_of_not_covby _

alias exists_lt_lt_of_not_covby ← LT.lt.exists_lt_lt

#print not_covby /-
/-- In a dense order, nothing covers anything. -/
theorem not_covby [DenselyOrdered α] : ¬a ⋖ b := fun h =>
  let ⟨c, hc⟩ := exists_between h.1
  h.2 hc.1 hc.2
#align not_covby not_covby
-/

#print densely_ordered_iff_forall_not_covby /-
theorem densely_ordered_iff_forall_not_covby : DenselyOrdered α ↔ ∀ a b : α, ¬a ⋖ b :=
  ⟨fun h a b => @not_covby _ _ _ _ h, fun h =>
    ⟨fun a b hab => exists_lt_lt_of_not_covby hab <| h _ _⟩⟩
#align densely_ordered_iff_forall_not_covby densely_ordered_iff_forall_not_covby
-/

#print toDual_covby_toDual_iff /-
@[simp]
theorem toDual_covby_toDual_iff : toDual b ⋖ toDual a ↔ a ⋖ b :=
  and_congr_right' <| forall_congr' fun c => forall_swap
#align to_dual_covby_to_dual_iff toDual_covby_toDual_iff
-/

#print ofDual_covby_ofDual_iff /-
@[simp]
theorem ofDual_covby_ofDual_iff {a b : αᵒᵈ} : ofDual a ⋖ ofDual b ↔ b ⋖ a :=
  and_congr_right' <| forall_congr' fun c => forall_swap
#align of_dual_covby_of_dual_iff ofDual_covby_ofDual_iff
-/

alias toDual_covby_toDual_iff ↔ _ Covby.to_dual

alias ofDual_covby_ofDual_iff ↔ _ Covby.of_dual

end LT

section Preorder

variable [Preorder α] [Preorder β] {a b c : α}

#print Covby.le /-
theorem Covby.le (h : a ⋖ b) : a ≤ b :=
  h.1.le
#align covby.le Covby.le
-/

#print Covby.ne /-
protected theorem Covby.ne (h : a ⋖ b) : a ≠ b :=
  h.lt.Ne
#align covby.ne Covby.ne
-/

#print Covby.ne' /-
theorem Covby.ne' (h : a ⋖ b) : b ≠ a :=
  h.lt.ne'
#align covby.ne' Covby.ne'
-/

#print Covby.wcovby /-
protected theorem Covby.wcovby (h : a ⋖ b) : a ⩿ b :=
  ⟨h.le, h.2⟩
#align covby.wcovby Covby.wcovby
-/

#print Wcovby.covby_of_not_le /-
theorem Wcovby.covby_of_not_le (h : a ⩿ b) (h2 : ¬b ≤ a) : a ⋖ b :=
  ⟨h.le.lt_of_not_le h2, h.2⟩
#align wcovby.covby_of_not_le Wcovby.covby_of_not_le
-/

#print Wcovby.covby_of_lt /-
theorem Wcovby.covby_of_lt (h : a ⩿ b) (h2 : a < b) : a ⋖ b :=
  ⟨h2, h.2⟩
#align wcovby.covby_of_lt Wcovby.covby_of_lt
-/

#print not_covby_of_lt_of_lt /-
theorem not_covby_of_lt_of_lt (h₁ : a < b) (h₂ : b < c) : ¬a ⋖ c :=
  (not_covby_iff (h₁.trans h₂)).2 ⟨b, h₁, h₂⟩
#align not_covby_of_lt_of_lt not_covby_of_lt_of_lt
-/

#print covby_iff_wcovby_and_lt /-
theorem covby_iff_wcovby_and_lt : a ⋖ b ↔ a ⩿ b ∧ a < b :=
  ⟨fun h => ⟨h.Wcovby, h.lt⟩, fun h => h.1.covby_of_lt h.2⟩
#align covby_iff_wcovby_and_lt covby_iff_wcovby_and_lt
-/

#print covby_iff_wcovby_and_not_le /-
theorem covby_iff_wcovby_and_not_le : a ⋖ b ↔ a ⩿ b ∧ ¬b ≤ a :=
  ⟨fun h => ⟨h.Wcovby, h.lt.not_le⟩, fun h => h.1.covby_of_not_le h.2⟩
#align covby_iff_wcovby_and_not_le covby_iff_wcovby_and_not_le
-/

#print wcovby_iff_covby_or_le_and_le /-
theorem wcovby_iff_covby_or_le_and_le : a ⩿ b ↔ a ⋖ b ∨ a ≤ b ∧ b ≤ a :=
  ⟨fun h => or_iff_not_imp_right.mpr fun h' => h.covby_of_not_le fun hba => h' ⟨h.le, hba⟩,
    fun h' => h'.elim (fun h => h.Wcovby) fun h => h.1.wcovby_of_le h.2⟩
#align wcovby_iff_covby_or_le_and_le wcovby_iff_covby_or_le_and_le
-/

#print AntisymmRel.trans_covby /-
theorem AntisymmRel.trans_covby (hab : AntisymmRel (· ≤ ·) a b) (hbc : b ⋖ c) : a ⋖ c :=
  ⟨hab.1.trans_lt hbc.lt, fun d had hdc => hbc.2 (hab.2.trans_lt had) hdc⟩
#align antisymm_rel.trans_covby AntisymmRel.trans_covby
-/

#print covby_congr_left /-
theorem covby_congr_left (hab : AntisymmRel (· ≤ ·) a b) : a ⋖ c ↔ b ⋖ c :=
  ⟨hab.symm.trans_covby, hab.trans_covby⟩
#align covby_congr_left covby_congr_left
-/

#print Covby.trans_antisymmRel /-
theorem Covby.trans_antisymmRel (hab : a ⋖ b) (hbc : AntisymmRel (· ≤ ·) b c) : a ⋖ c :=
  ⟨hab.lt.trans_le hbc.1, fun d had hdb => hab.2 had <| hdb.trans_le hbc.2⟩
#align covby.trans_antisymm_rel Covby.trans_antisymmRel
-/

#print covby_congr_right /-
theorem covby_congr_right (hab : AntisymmRel (· ≤ ·) a b) : c ⋖ a ↔ c ⋖ b :=
  ⟨fun h => h.trans_antisymm_rel hab, fun h => h.trans_antisymm_rel hab.symm⟩
#align covby_congr_right covby_congr_right
-/

instance : IsNonstrictStrictOrder α (· ⩿ ·) (· ⋖ ·) :=
  ⟨fun a b =>
    covby_iff_wcovby_and_not_le.trans <| and_congr_right fun h => h.wcovby_iff_le.Not.symm⟩

#print Covby.isIrrefl /-
instance Covby.isIrrefl : IsIrrefl α (· ⋖ ·) :=
  ⟨fun a ha => ha.Ne rfl⟩
#align covby.is_irrefl Covby.isIrrefl
-/

#print Covby.Ioo_eq /-
theorem Covby.Ioo_eq (h : a ⋖ b) : Ioo a b = ∅ :=
  h.Wcovby.Ioo_eq
#align covby.Ioo_eq Covby.Ioo_eq
-/

#print covby_iff_Ioo_eq /-
theorem covby_iff_Ioo_eq : a ⋖ b ↔ a < b ∧ Ioo a b = ∅ :=
  and_congr_right' <| by simp [eq_empty_iff_forall_not_mem]
#align covby_iff_Ioo_eq covby_iff_Ioo_eq
-/

/- warning: covby.of_image -> Covby.of_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {a : α} {b : α} (f : OrderEmbedding.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)), (Covby.{u2} β (Preorder.toLT.{u2} β _inst_2) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderEmbedding.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)) (fun (_x : RelEmbedding.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) f a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderEmbedding.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)) (fun (_x : RelEmbedding.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) f b)) -> (Covby.{u1} α (Preorder.toLT.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {a : α} {b : α} (f : OrderEmbedding.{u2, u1} α β (Preorder.toLE.{u2} α _inst_1) (Preorder.toLE.{u1} β _inst_2)), (Covby.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (Preorder.toLT.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) _inst_2) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.744 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.746 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.744 x._@.Mathlib.Order.Hom.Basic._hyg.746) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.759 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.761 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) x._@.Mathlib.Order.Hom.Basic._hyg.759 x._@.Mathlib.Order.Hom.Basic._hyg.761) f) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.744 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.746 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.744 x._@.Mathlib.Order.Hom.Basic._hyg.746) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.759 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.761 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) x._@.Mathlib.Order.Hom.Basic._hyg.759 x._@.Mathlib.Order.Hom.Basic._hyg.761) f) b)) -> (Covby.{u2} α (Preorder.toLT.{u2} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align covby.of_image Covby.of_imageₓ'. -/
theorem Covby.of_image (f : α ↪o β) (h : f a ⋖ f b) : a ⋖ b :=
  ⟨f.lt_iff_lt.mp h.lt, fun c hac hcb => h.2 (f.lt_iff_lt.mpr hac) (f.lt_iff_lt.mpr hcb)⟩
#align covby.of_image Covby.of_image

/- warning: covby.image -> Covby.image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {a : α} {b : α} (f : OrderEmbedding.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)), (Covby.{u1} α (Preorder.toLT.{u1} α _inst_1) a b) -> (Set.OrdConnected.{u2} β _inst_2 (Set.range.{u2, succ u1} β α (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderEmbedding.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)) (fun (_x : RelEmbedding.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) f))) -> (Covby.{u2} β (Preorder.toLT.{u2} β _inst_2) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderEmbedding.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)) (fun (_x : RelEmbedding.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) f a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderEmbedding.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)) (fun (_x : RelEmbedding.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) f b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {a : α} {b : α} (f : OrderEmbedding.{u2, u1} α β (Preorder.toLE.{u2} α _inst_1) (Preorder.toLE.{u1} β _inst_2)), (Covby.{u2} α (Preorder.toLT.{u2} α _inst_1) a b) -> (Set.OrdConnected.{u1} β _inst_2 (Set.range.{u1, succ u2} β α (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.744 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.746 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.744 x._@.Mathlib.Order.Hom.Basic._hyg.746) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.759 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.761 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) x._@.Mathlib.Order.Hom.Basic._hyg.759 x._@.Mathlib.Order.Hom.Basic._hyg.761) f)))) -> (Covby.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (Preorder.toLT.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) _inst_2) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.744 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.746 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.744 x._@.Mathlib.Order.Hom.Basic._hyg.746) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.759 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.761 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) x._@.Mathlib.Order.Hom.Basic._hyg.759 x._@.Mathlib.Order.Hom.Basic._hyg.761) f) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.744 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.746 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.744 x._@.Mathlib.Order.Hom.Basic._hyg.746) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.759 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.761 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) x._@.Mathlib.Order.Hom.Basic._hyg.759 x._@.Mathlib.Order.Hom.Basic._hyg.761) f) b))
Case conversion may be inaccurate. Consider using '#align covby.image Covby.imageₓ'. -/
theorem Covby.image (f : α ↪o β) (hab : a ⋖ b) (h : (range f).OrdConnected) : f a ⋖ f b :=
  (hab.Wcovby.image f h).covby_of_lt <| f.StrictMono hab.lt
#align covby.image Covby.image

/- warning: set.ord_connected.apply_covby_apply_iff -> Set.OrdConnected.apply_covby_apply_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {a : α} {b : α} (f : OrderEmbedding.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)), (Set.OrdConnected.{u2} β _inst_2 (Set.range.{u2, succ u1} β α (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderEmbedding.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)) (fun (_x : RelEmbedding.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) f))) -> (Iff (Covby.{u2} β (Preorder.toLT.{u2} β _inst_2) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderEmbedding.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)) (fun (_x : RelEmbedding.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) f a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderEmbedding.{u1, u2} α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)) (fun (_x : RelEmbedding.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) f b)) (Covby.{u1} α (Preorder.toLT.{u1} α _inst_1) a b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {a : α} {b : α} (f : OrderEmbedding.{u2, u1} α β (Preorder.toLE.{u2} α _inst_1) (Preorder.toLE.{u1} β _inst_2)), (Set.OrdConnected.{u1} β _inst_2 (Set.range.{u1, succ u2} β α (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.744 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.746 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.744 x._@.Mathlib.Order.Hom.Basic._hyg.746) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.759 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.761 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) x._@.Mathlib.Order.Hom.Basic._hyg.759 x._@.Mathlib.Order.Hom.Basic._hyg.761) f)))) -> (Iff (Covby.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (Preorder.toLT.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) _inst_2) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.744 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.746 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.744 x._@.Mathlib.Order.Hom.Basic._hyg.746) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.759 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.761 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) x._@.Mathlib.Order.Hom.Basic._hyg.759 x._@.Mathlib.Order.Hom.Basic._hyg.761) f) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.744 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.746 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.744 x._@.Mathlib.Order.Hom.Basic._hyg.746) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.759 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.761 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) x._@.Mathlib.Order.Hom.Basic._hyg.759 x._@.Mathlib.Order.Hom.Basic._hyg.761) f) b)) (Covby.{u2} α (Preorder.toLT.{u2} α _inst_1) a b))
Case conversion may be inaccurate. Consider using '#align set.ord_connected.apply_covby_apply_iff Set.OrdConnected.apply_covby_apply_iffₓ'. -/
theorem Set.OrdConnected.apply_covby_apply_iff (f : α ↪o β) (h : (range f).OrdConnected) :
    f a ⋖ f b ↔ a ⋖ b :=
  ⟨Covby.of_image f, fun hab => hab.image f h⟩
#align set.ord_connected.apply_covby_apply_iff Set.OrdConnected.apply_covby_apply_iff

/- warning: apply_covby_apply_iff -> apply_covby_apply_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {a : α} {b : α} {E : Type.{u3}} [_inst_3 : OrderIsoClass.{u3, u1, u2} E α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2)] (e : E), Iff (Covby.{u2} β (Preorder.toLT.{u2} β _inst_2) (coeFn.{succ u3, max (succ u1) (succ u2)} E (fun (_x : E) => α -> β) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} E α (fun (_x : α) => β) (RelHomClass.toFunLike.{u3, u1, u2} E α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2)) (OrderIsoClass.toOrderHomClass.{u3, u1, u2} E α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2) _inst_3))) e a) (coeFn.{succ u3, max (succ u1) (succ u2)} E (fun (_x : E) => α -> β) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} E α (fun (_x : α) => β) (RelHomClass.toFunLike.{u3, u1, u2} E α β (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2)) (OrderIsoClass.toOrderHomClass.{u3, u1, u2} E α β (Preorder.toLE.{u1} α _inst_1) (Preorder.toLE.{u2} β _inst_2) _inst_3))) e b)) (Covby.{u1} α (Preorder.toLT.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {a : α} {b : α} {E : Type.{u3}} [_inst_3 : OrderIsoClass.{u3, u2, u1} E α β (Preorder.toLE.{u2} α _inst_1) (Preorder.toLE.{u1} β _inst_2)] (e : E), Iff (Covby.{u1} ((fun (x._@.Mathlib.Order.RelIso.Basic._hyg.931 : α) => β) a) (Preorder.toLT.{u1} ((fun (x._@.Mathlib.Order.RelIso.Basic._hyg.931 : α) => β) a) _inst_2) (FunLike.coe.{succ u3, succ u2, succ u1} E α (fun (_x : α) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.931 : α) => β) _x) (RelHomClass.toFunLike.{u3, u2, u1} E α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.2092 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.2094 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.2092 x._@.Mathlib.Order.Hom.Basic._hyg.2094) (fun (_x : β) (x._@.Mathlib.Order.Hom.Basic._hyg.2116 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) _x x._@.Mathlib.Order.Hom.Basic._hyg.2116) (OrderIsoClass.toOrderHomClass.{u3, u2, u1} E α β (Preorder.toLE.{u2} α _inst_1) (Preorder.toLE.{u1} β _inst_2) _inst_3)) e a) (FunLike.coe.{succ u3, succ u2, succ u1} E α (fun (_x : α) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.931 : α) => β) _x) (RelHomClass.toFunLike.{u3, u2, u1} E α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.2092 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.2094 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.2092 x._@.Mathlib.Order.Hom.Basic._hyg.2094) (fun (_x : β) (x._@.Mathlib.Order.Hom.Basic._hyg.2116 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) _x x._@.Mathlib.Order.Hom.Basic._hyg.2116) (OrderIsoClass.toOrderHomClass.{u3, u2, u1} E α β (Preorder.toLE.{u2} α _inst_1) (Preorder.toLE.{u1} β _inst_2) _inst_3)) e b)) (Covby.{u2} α (Preorder.toLT.{u2} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align apply_covby_apply_iff apply_covby_apply_iffₓ'. -/
@[simp]
theorem apply_covby_apply_iff {E : Type _} [OrderIsoClass E α β] (e : E) : e a ⋖ e b ↔ a ⋖ b :=
  (ordConnected_range (e : α ≃o β)).apply_covby_apply_iff ((e : α ≃o β) : α ↪o β)
#align apply_covby_apply_iff apply_covby_apply_iff

#print covby_of_eq_or_eq /-
theorem covby_of_eq_or_eq (hab : a < b) (h : ∀ c, a ≤ c → c ≤ b → c = a ∨ c = b) : a ⋖ b :=
  ⟨hab, fun c ha hb => (h c ha.le hb.le).elim ha.ne' hb.Ne⟩
#align covby_of_eq_or_eq covby_of_eq_or_eq
-/

end Preorder

section PartialOrder

variable [PartialOrder α] {a b c : α}

#print Wcovby.covby_of_ne /-
theorem Wcovby.covby_of_ne (h : a ⩿ b) (h2 : a ≠ b) : a ⋖ b :=
  ⟨h.le.lt_of_ne h2, h.2⟩
#align wcovby.covby_of_ne Wcovby.covby_of_ne
-/

#print covby_iff_wcovby_and_ne /-
theorem covby_iff_wcovby_and_ne : a ⋖ b ↔ a ⩿ b ∧ a ≠ b :=
  ⟨fun h => ⟨h.Wcovby, h.Ne⟩, fun h => h.1.covby_of_ne h.2⟩
#align covby_iff_wcovby_and_ne covby_iff_wcovby_and_ne
-/

#print wcovby_iff_covby_or_eq /-
theorem wcovby_iff_covby_or_eq : a ⩿ b ↔ a ⋖ b ∨ a = b := by
  rw [le_antisymm_iff, wcovby_iff_covby_or_le_and_le]
#align wcovby_iff_covby_or_eq wcovby_iff_covby_or_eq
-/

#print wcovby_iff_eq_or_covby /-
theorem wcovby_iff_eq_or_covby : a ⩿ b ↔ a = b ∨ a ⋖ b :=
  wcovby_iff_covby_or_eq.trans or_comm
#align wcovby_iff_eq_or_covby wcovby_iff_eq_or_covby
-/

alias wcovby_iff_covby_or_eq ↔ Wcovby.covby_or_eq _

alias wcovby_iff_eq_or_covby ↔ Wcovby.eq_or_covby _

#print Covby.eq_or_eq /-
theorem Covby.eq_or_eq (h : a ⋖ b) (h2 : a ≤ c) (h3 : c ≤ b) : c = a ∨ c = b :=
  h.Wcovby.eq_or_eq h2 h3
#align covby.eq_or_eq Covby.eq_or_eq
-/

#print covby_iff_lt_and_eq_or_eq /-
/-- An `iff` version of `covby.eq_or_eq` and `covby_of_eq_or_eq`. -/
theorem covby_iff_lt_and_eq_or_eq : a ⋖ b ↔ a < b ∧ ∀ c, a ≤ c → c ≤ b → c = a ∨ c = b :=
  ⟨fun h => ⟨h.lt, fun c => h.eq_or_eq⟩, And.ndrec covby_of_eq_or_eq⟩
#align covby_iff_lt_and_eq_or_eq covby_iff_lt_and_eq_or_eq
-/

#print Covby.Ico_eq /-
theorem Covby.Ico_eq (h : a ⋖ b) : Ico a b = {a} := by
  rw [← Ioo_union_left h.lt, h.Ioo_eq, empty_union]
#align covby.Ico_eq Covby.Ico_eq
-/

#print Covby.Ioc_eq /-
theorem Covby.Ioc_eq (h : a ⋖ b) : Ioc a b = {b} := by
  rw [← Ioo_union_right h.lt, h.Ioo_eq, empty_union]
#align covby.Ioc_eq Covby.Ioc_eq
-/

#print Covby.Icc_eq /-
theorem Covby.Icc_eq (h : a ⋖ b) : Icc a b = {a, b} :=
  h.Wcovby.Icc_eq
#align covby.Icc_eq Covby.Icc_eq
-/

end PartialOrder

section LinearOrder

variable [LinearOrder α] {a b c : α}

#print Covby.Ioi_eq /-
theorem Covby.Ioi_eq (h : a ⋖ b) : Ioi a = Ici b := by
  rw [← Ioo_union_Ici_eq_Ioi h.lt, h.Ioo_eq, empty_union]
#align covby.Ioi_eq Covby.Ioi_eq
-/

#print Covby.Iio_eq /-
theorem Covby.Iio_eq (h : a ⋖ b) : Iio b = Iic a := by
  rw [← Iic_union_Ioo_eq_Iio h.lt, h.Ioo_eq, union_empty]
#align covby.Iio_eq Covby.Iio_eq
-/

#print Wcovby.le_of_lt /-
theorem Wcovby.le_of_lt (hab : a ⩿ b) (hcb : c < b) : c ≤ a :=
  not_lt.1 fun hac => hab.2 hac hcb
#align wcovby.le_of_lt Wcovby.le_of_lt
-/

#print Wcovby.ge_of_gt /-
theorem Wcovby.ge_of_gt (hab : a ⩿ b) (hac : a < c) : b ≤ c :=
  not_lt.1 <| hab.2 hac
#align wcovby.ge_of_gt Wcovby.ge_of_gt
-/

#print Covby.le_of_lt /-
theorem Covby.le_of_lt (hab : a ⋖ b) : c < b → c ≤ a :=
  hab.Wcovby.le_of_lt
#align covby.le_of_lt Covby.le_of_lt
-/

#print Covby.ge_of_gt /-
theorem Covby.ge_of_gt (hab : a ⋖ b) : a < c → b ≤ c :=
  hab.Wcovby.ge_of_gt
#align covby.ge_of_gt Covby.ge_of_gt
-/

#print Covby.unique_left /-
theorem Covby.unique_left (ha : a ⋖ c) (hb : b ⋖ c) : a = b :=
  (hb.le_of_lt ha.lt).antisymm <| ha.le_of_lt hb.lt
#align covby.unique_left Covby.unique_left
-/

#print Covby.unique_right /-
theorem Covby.unique_right (hb : a ⋖ b) (hc : a ⋖ c) : b = c :=
  (hb.ge_of_gt hc.lt).antisymm <| hc.ge_of_gt hb.lt
#align covby.unique_right Covby.unique_right
-/

#print Covby.eq_of_between /-
/-- If `a`, `b`, `c` are consecutive and `a < x < c` then `x = b`. -/
theorem Covby.eq_of_between {x : α} (hab : a ⋖ b) (hbc : b ⋖ c) (hax : a < x) (hxc : x < c) :
    x = b :=
  le_antisymm (le_of_not_lt fun h => hbc.2 h hxc) (le_of_not_lt <| hab.2 hax)
#align covby.eq_of_between Covby.eq_of_between
-/

end LinearOrder

namespace Set

/- warning: set.wcovby_insert -> Set.wcovby_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (x : α) (s : Set.{u1} α), Wcovby.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) s (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) x s)
but is expected to have type
  forall {α : Type.{u1}} (x : α) (s : Set.{u1} α), Wcovby.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) s (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) x s)
Case conversion may be inaccurate. Consider using '#align set.wcovby_insert Set.wcovby_insertₓ'. -/
theorem wcovby_insert (x : α) (s : Set α) : s ⩿ insert x s :=
  by
  refine' wcovby_of_eq_or_eq (subset_insert x s) fun t hst h2t => _
  by_cases h : x ∈ t
  · exact Or.inr (subset_antisymm h2t <| insert_subset.mpr ⟨h, hst⟩)
  · refine' Or.inl (subset_antisymm _ hst)
    rwa [← diff_singleton_eq_self h, diff_singleton_subset_iff]
#align set.wcovby_insert Set.wcovby_insert

/- warning: set.covby_insert -> Set.covby_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {x : α} {s : Set.{u1} α}, (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) -> (Covby.{u1} (Set.{u1} α) (Preorder.toLT.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))))) s (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) x s))
but is expected to have type
  forall {α : Type.{u1}} {x : α} {s : Set.{u1} α}, (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)) -> (Covby.{u1} (Set.{u1} α) (Preorder.toLT.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) s (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) x s))
Case conversion may be inaccurate. Consider using '#align set.covby_insert Set.covby_insertₓ'. -/
theorem covby_insert {x : α} {s : Set α} (hx : x ∉ s) : s ⋖ insert x s :=
  (wcovby_insert x s).covby_of_lt <| ssubset_insert hx
#align set.covby_insert Set.covby_insert

end Set

namespace Prod

variable [PartialOrder α] [PartialOrder β] {a a₁ a₂ : α} {b b₁ b₂ : β} {x y : α × β}

/- warning: prod.swap_wcovby_swap -> Prod.swap_wcovby_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] {x : Prod.{u1, u2} α β} {y : Prod.{u1, u2} α β}, Iff (Wcovby.{max u2 u1} (Prod.{u2, u1} β α) (Prod.preorder.{u2, u1} β α (PartialOrder.toPreorder.{u2} β _inst_2) (PartialOrder.toPreorder.{u1} α _inst_1)) (Prod.swap.{u1, u2} α β x) (Prod.swap.{u1, u2} α β y)) (Wcovby.{max u1 u2} (Prod.{u1, u2} α β) (Prod.preorder.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2)) x y)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : PartialOrder.{u1} β] {x : Prod.{u2, u1} α β} {y : Prod.{u2, u1} α β}, Iff (Wcovby.{max u2 u1} (Prod.{u1, u2} β α) (Prod.instPreorderProd.{u1, u2} β α (PartialOrder.toPreorder.{u1} β _inst_2) (PartialOrder.toPreorder.{u2} α _inst_1)) (Prod.swap.{u2, u1} α β x) (Prod.swap.{u2, u1} α β y)) (Wcovby.{max u2 u1} (Prod.{u2, u1} α β) (Prod.instPreorderProd.{u2, u1} α β (PartialOrder.toPreorder.{u2} α _inst_1) (PartialOrder.toPreorder.{u1} β _inst_2)) x y)
Case conversion may be inaccurate. Consider using '#align prod.swap_wcovby_swap Prod.swap_wcovby_swapₓ'. -/
@[simp]
theorem swap_wcovby_swap : x.swap ⩿ y.swap ↔ x ⩿ y :=
  apply_wcovby_apply_iff (OrderIso.prodComm : α × β ≃o β × α)
#align prod.swap_wcovby_swap Prod.swap_wcovby_swap

/- warning: prod.swap_covby_swap -> Prod.swap_covby_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] {x : Prod.{u1, u2} α β} {y : Prod.{u1, u2} α β}, Iff (Covby.{max u2 u1} (Prod.{u2, u1} β α) (Preorder.toLT.{max u2 u1} (Prod.{u2, u1} β α) (Prod.preorder.{u2, u1} β α (PartialOrder.toPreorder.{u2} β _inst_2) (PartialOrder.toPreorder.{u1} α _inst_1))) (Prod.swap.{u1, u2} α β x) (Prod.swap.{u1, u2} α β y)) (Covby.{max u1 u2} (Prod.{u1, u2} α β) (Preorder.toLT.{max u1 u2} (Prod.{u1, u2} α β) (Prod.preorder.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2))) x y)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : PartialOrder.{u1} β] {x : Prod.{u2, u1} α β} {y : Prod.{u2, u1} α β}, Iff (Covby.{max u2 u1} (Prod.{u1, u2} β α) (Preorder.toLT.{max u2 u1} (Prod.{u1, u2} β α) (Prod.instPreorderProd.{u1, u2} β α (PartialOrder.toPreorder.{u1} β _inst_2) (PartialOrder.toPreorder.{u2} α _inst_1))) (Prod.swap.{u2, u1} α β x) (Prod.swap.{u2, u1} α β y)) (Covby.{max u2 u1} (Prod.{u2, u1} α β) (Preorder.toLT.{max u2 u1} (Prod.{u2, u1} α β) (Prod.instPreorderProd.{u2, u1} α β (PartialOrder.toPreorder.{u2} α _inst_1) (PartialOrder.toPreorder.{u1} β _inst_2))) x y)
Case conversion may be inaccurate. Consider using '#align prod.swap_covby_swap Prod.swap_covby_swapₓ'. -/
@[simp]
theorem swap_covby_swap : x.swap ⋖ y.swap ↔ x ⋖ y :=
  apply_covby_apply_iff (OrderIso.prodComm : α × β ≃o β × α)
#align prod.swap_covby_swap Prod.swap_covby_swap

/- warning: prod.fst_eq_or_snd_eq_of_wcovby -> Prod.fst_eq_or_snd_eq_of_wcovby is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] {x : Prod.{u1, u2} α β} {y : Prod.{u1, u2} α β}, (Wcovby.{max u1 u2} (Prod.{u1, u2} α β) (Prod.preorder.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2)) x y) -> (Or (Eq.{succ u1} α (Prod.fst.{u1, u2} α β x) (Prod.fst.{u1, u2} α β y)) (Eq.{succ u2} β (Prod.snd.{u1, u2} α β x) (Prod.snd.{u1, u2} α β y)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : PartialOrder.{u1} β] {x : Prod.{u2, u1} α β} {y : Prod.{u2, u1} α β}, (Wcovby.{max u2 u1} (Prod.{u2, u1} α β) (Prod.instPreorderProd.{u2, u1} α β (PartialOrder.toPreorder.{u2} α _inst_1) (PartialOrder.toPreorder.{u1} β _inst_2)) x y) -> (Or (Eq.{succ u2} α (Prod.fst.{u2, u1} α β x) (Prod.fst.{u2, u1} α β y)) (Eq.{succ u1} β (Prod.snd.{u2, u1} α β x) (Prod.snd.{u2, u1} α β y)))
Case conversion may be inaccurate. Consider using '#align prod.fst_eq_or_snd_eq_of_wcovby Prod.fst_eq_or_snd_eq_of_wcovbyₓ'. -/
theorem fst_eq_or_snd_eq_of_wcovby : x ⩿ y → x.1 = y.1 ∨ x.2 = y.2 :=
  by
  refine' fun h => of_not_not fun hab => _
  push_neg  at hab
  exact
    h.2 (mk_lt_mk.2 <| Or.inl ⟨hab.1.lt_of_le h.1.1, le_rfl⟩)
      (mk_lt_mk.2 <| Or.inr ⟨le_rfl, hab.2.lt_of_le h.1.2⟩)
#align prod.fst_eq_or_snd_eq_of_wcovby Prod.fst_eq_or_snd_eq_of_wcovby

/- warning: wcovby.fst -> Wcovby.fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] {x : Prod.{u1, u2} α β} {y : Prod.{u1, u2} α β}, (Wcovby.{max u1 u2} (Prod.{u1, u2} α β) (Prod.preorder.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2)) x y) -> (Wcovby.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) (Prod.fst.{u1, u2} α β x) (Prod.fst.{u1, u2} α β y))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : PartialOrder.{u1} β] {x : Prod.{u2, u1} α β} {y : Prod.{u2, u1} α β}, (Wcovby.{max u2 u1} (Prod.{u2, u1} α β) (Prod.instPreorderProd.{u2, u1} α β (PartialOrder.toPreorder.{u2} α _inst_1) (PartialOrder.toPreorder.{u1} β _inst_2)) x y) -> (Wcovby.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) (Prod.fst.{u2, u1} α β x) (Prod.fst.{u2, u1} α β y))
Case conversion may be inaccurate. Consider using '#align wcovby.fst Wcovby.fstₓ'. -/
theorem Wcovby.fst (h : x ⩿ y) : x.1 ⩿ y.1 :=
  ⟨h.1.1, fun c h₁ h₂ => h.2 (mk_lt_mk_iff_left.2 h₁) ⟨⟨h₂.le, h.1.2⟩, fun hc => h₂.not_le hc.1⟩⟩
#align wcovby.fst Wcovby.fst

/- warning: wcovby.snd -> Wcovby.snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] {x : Prod.{u1, u2} α β} {y : Prod.{u1, u2} α β}, (Wcovby.{max u1 u2} (Prod.{u1, u2} α β) (Prod.preorder.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2)) x y) -> (Wcovby.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2) (Prod.snd.{u1, u2} α β x) (Prod.snd.{u1, u2} α β y))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : PartialOrder.{u1} β] {x : Prod.{u2, u1} α β} {y : Prod.{u2, u1} α β}, (Wcovby.{max u2 u1} (Prod.{u2, u1} α β) (Prod.instPreorderProd.{u2, u1} α β (PartialOrder.toPreorder.{u2} α _inst_1) (PartialOrder.toPreorder.{u1} β _inst_2)) x y) -> (Wcovby.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2) (Prod.snd.{u2, u1} α β x) (Prod.snd.{u2, u1} α β y))
Case conversion may be inaccurate. Consider using '#align wcovby.snd Wcovby.sndₓ'. -/
theorem Wcovby.snd (h : x ⩿ y) : x.2 ⩿ y.2 :=
  ⟨h.1.2, fun c h₁ h₂ => h.2 (mk_lt_mk_iff_right.2 h₁) ⟨⟨h.1.1, h₂.le⟩, fun hc => h₂.not_le hc.2⟩⟩
#align wcovby.snd Wcovby.snd

/- warning: prod.mk_wcovby_mk_iff_left -> Prod.mk_wcovby_mk_iff_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] {a₁ : α} {a₂ : α} {b : β}, Iff (Wcovby.{max u1 u2} (Prod.{u1, u2} α β) (Prod.preorder.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2)) (Prod.mk.{u1, u2} α β a₁ b) (Prod.mk.{u1, u2} α β a₂ b)) (Wcovby.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) a₁ a₂)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] {a₁ : α} {a₂ : α} {b : β}, Iff (Wcovby.{max u2 u1} (Prod.{u1, u2} α β) (Prod.instPreorderProd.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2)) (Prod.mk.{u1, u2} α β a₁ b) (Prod.mk.{u1, u2} α β a₂ b)) (Wcovby.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) a₁ a₂)
Case conversion may be inaccurate. Consider using '#align prod.mk_wcovby_mk_iff_left Prod.mk_wcovby_mk_iff_leftₓ'. -/
theorem mk_wcovby_mk_iff_left : (a₁, b) ⩿ (a₂, b) ↔ a₁ ⩿ a₂ :=
  by
  refine' ⟨Wcovby.fst, (And.imp mk_le_mk_iff_left.2) fun h c h₁ h₂ => _⟩
  have : c.2 = b := h₂.le.2.antisymm h₁.le.2
  rw [← @Prod.mk.eta _ _ c, this, mk_lt_mk_iff_left] at h₁ h₂
  exact h h₁ h₂
#align prod.mk_wcovby_mk_iff_left Prod.mk_wcovby_mk_iff_left

/- warning: prod.mk_wcovby_mk_iff_right -> Prod.mk_wcovby_mk_iff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] {a : α} {b₁ : β} {b₂ : β}, Iff (Wcovby.{max u1 u2} (Prod.{u1, u2} α β) (Prod.preorder.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2)) (Prod.mk.{u1, u2} α β a b₁) (Prod.mk.{u1, u2} α β a b₂)) (Wcovby.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2) b₁ b₂)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] {a : α} {b₁ : β} {b₂ : β}, Iff (Wcovby.{max u2 u1} (Prod.{u1, u2} α β) (Prod.instPreorderProd.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2)) (Prod.mk.{u1, u2} α β a b₁) (Prod.mk.{u1, u2} α β a b₂)) (Wcovby.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2) b₁ b₂)
Case conversion may be inaccurate. Consider using '#align prod.mk_wcovby_mk_iff_right Prod.mk_wcovby_mk_iff_rightₓ'. -/
theorem mk_wcovby_mk_iff_right : (a, b₁) ⩿ (a, b₂) ↔ b₁ ⩿ b₂ :=
  swap_wcovby_swap.trans mk_wcovby_mk_iff_left
#align prod.mk_wcovby_mk_iff_right Prod.mk_wcovby_mk_iff_right

/- warning: prod.mk_covby_mk_iff_left -> Prod.mk_covby_mk_iff_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] {a₁ : α} {a₂ : α} {b : β}, Iff (Covby.{max u1 u2} (Prod.{u1, u2} α β) (Preorder.toLT.{max u1 u2} (Prod.{u1, u2} α β) (Prod.preorder.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2))) (Prod.mk.{u1, u2} α β a₁ b) (Prod.mk.{u1, u2} α β a₂ b)) (Covby.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a₁ a₂)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] {a₁ : α} {a₂ : α} {b : β}, Iff (Covby.{max u2 u1} (Prod.{u1, u2} α β) (Preorder.toLT.{max u1 u2} (Prod.{u1, u2} α β) (Prod.instPreorderProd.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2))) (Prod.mk.{u1, u2} α β a₁ b) (Prod.mk.{u1, u2} α β a₂ b)) (Covby.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a₁ a₂)
Case conversion may be inaccurate. Consider using '#align prod.mk_covby_mk_iff_left Prod.mk_covby_mk_iff_leftₓ'. -/
theorem mk_covby_mk_iff_left : (a₁, b) ⋖ (a₂, b) ↔ a₁ ⋖ a₂ := by
  simp_rw [covby_iff_wcovby_and_lt, mk_wcovby_mk_iff_left, mk_lt_mk_iff_left]
#align prod.mk_covby_mk_iff_left Prod.mk_covby_mk_iff_left

/- warning: prod.mk_covby_mk_iff_right -> Prod.mk_covby_mk_iff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] {a : α} {b₁ : β} {b₂ : β}, Iff (Covby.{max u1 u2} (Prod.{u1, u2} α β) (Preorder.toLT.{max u1 u2} (Prod.{u1, u2} α β) (Prod.preorder.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2))) (Prod.mk.{u1, u2} α β a b₁) (Prod.mk.{u1, u2} α β a b₂)) (Covby.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2)) b₁ b₂)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] {a : α} {b₁ : β} {b₂ : β}, Iff (Covby.{max u2 u1} (Prod.{u1, u2} α β) (Preorder.toLT.{max u1 u2} (Prod.{u1, u2} α β) (Prod.instPreorderProd.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2))) (Prod.mk.{u1, u2} α β a b₁) (Prod.mk.{u1, u2} α β a b₂)) (Covby.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2)) b₁ b₂)
Case conversion may be inaccurate. Consider using '#align prod.mk_covby_mk_iff_right Prod.mk_covby_mk_iff_rightₓ'. -/
theorem mk_covby_mk_iff_right : (a, b₁) ⋖ (a, b₂) ↔ b₁ ⋖ b₂ := by
  simp_rw [covby_iff_wcovby_and_lt, mk_wcovby_mk_iff_right, mk_lt_mk_iff_right]
#align prod.mk_covby_mk_iff_right Prod.mk_covby_mk_iff_right

/- warning: prod.mk_wcovby_mk_iff -> Prod.mk_wcovby_mk_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] {a₁ : α} {a₂ : α} {b₁ : β} {b₂ : β}, Iff (Wcovby.{max u1 u2} (Prod.{u1, u2} α β) (Prod.preorder.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2)) (Prod.mk.{u1, u2} α β a₁ b₁) (Prod.mk.{u1, u2} α β a₂ b₂)) (Or (And (Wcovby.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) a₁ a₂) (Eq.{succ u2} β b₁ b₂)) (And (Wcovby.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2) b₁ b₂) (Eq.{succ u1} α a₁ a₂)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] {a₁ : α} {a₂ : α} {b₁ : β} {b₂ : β}, Iff (Wcovby.{max u2 u1} (Prod.{u1, u2} α β) (Prod.instPreorderProd.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2)) (Prod.mk.{u1, u2} α β a₁ b₁) (Prod.mk.{u1, u2} α β a₂ b₂)) (Or (And (Wcovby.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) a₁ a₂) (Eq.{succ u2} β b₁ b₂)) (And (Wcovby.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2) b₁ b₂) (Eq.{succ u1} α a₁ a₂)))
Case conversion may be inaccurate. Consider using '#align prod.mk_wcovby_mk_iff Prod.mk_wcovby_mk_iffₓ'. -/
theorem mk_wcovby_mk_iff : (a₁, b₁) ⩿ (a₂, b₂) ↔ a₁ ⩿ a₂ ∧ b₁ = b₂ ∨ b₁ ⩿ b₂ ∧ a₁ = a₂ :=
  by
  refine' ⟨fun h => _, _⟩
  · obtain rfl | rfl : a₁ = a₂ ∨ b₁ = b₂ := fst_eq_or_snd_eq_of_wcovby h
    · exact Or.inr ⟨mk_wcovby_mk_iff_right.1 h, rfl⟩
    · exact Or.inl ⟨mk_wcovby_mk_iff_left.1 h, rfl⟩
  · rintro (⟨h, rfl⟩ | ⟨h, rfl⟩)
    · exact mk_wcovby_mk_iff_left.2 h
    · exact mk_wcovby_mk_iff_right.2 h
#align prod.mk_wcovby_mk_iff Prod.mk_wcovby_mk_iff

/- warning: prod.mk_covby_mk_iff -> Prod.mk_covby_mk_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] {a₁ : α} {a₂ : α} {b₁ : β} {b₂ : β}, Iff (Covby.{max u1 u2} (Prod.{u1, u2} α β) (Preorder.toLT.{max u1 u2} (Prod.{u1, u2} α β) (Prod.preorder.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2))) (Prod.mk.{u1, u2} α β a₁ b₁) (Prod.mk.{u1, u2} α β a₂ b₂)) (Or (And (Covby.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a₁ a₂) (Eq.{succ u2} β b₁ b₂)) (And (Covby.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2)) b₁ b₂) (Eq.{succ u1} α a₁ a₂)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] {a₁ : α} {a₂ : α} {b₁ : β} {b₂ : β}, Iff (Covby.{max u2 u1} (Prod.{u1, u2} α β) (Preorder.toLT.{max u1 u2} (Prod.{u1, u2} α β) (Prod.instPreorderProd.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2))) (Prod.mk.{u1, u2} α β a₁ b₁) (Prod.mk.{u1, u2} α β a₂ b₂)) (Or (And (Covby.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a₁ a₂) (Eq.{succ u2} β b₁ b₂)) (And (Covby.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2)) b₁ b₂) (Eq.{succ u1} α a₁ a₂)))
Case conversion may be inaccurate. Consider using '#align prod.mk_covby_mk_iff Prod.mk_covby_mk_iffₓ'. -/
theorem mk_covby_mk_iff : (a₁, b₁) ⋖ (a₂, b₂) ↔ a₁ ⋖ a₂ ∧ b₁ = b₂ ∨ b₁ ⋖ b₂ ∧ a₁ = a₂ :=
  by
  refine' ⟨fun h => _, _⟩
  · obtain rfl | rfl : a₁ = a₂ ∨ b₁ = b₂ := fst_eq_or_snd_eq_of_wcovby h.wcovby
    · exact Or.inr ⟨mk_covby_mk_iff_right.1 h, rfl⟩
    · exact Or.inl ⟨mk_covby_mk_iff_left.1 h, rfl⟩
  · rintro (⟨h, rfl⟩ | ⟨h, rfl⟩)
    · exact mk_covby_mk_iff_left.2 h
    · exact mk_covby_mk_iff_right.2 h
#align prod.mk_covby_mk_iff Prod.mk_covby_mk_iff

/- warning: prod.wcovby_iff -> Prod.wcovby_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] {x : Prod.{u1, u2} α β} {y : Prod.{u1, u2} α β}, Iff (Wcovby.{max u1 u2} (Prod.{u1, u2} α β) (Prod.preorder.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2)) x y) (Or (And (Wcovby.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) (Prod.fst.{u1, u2} α β x) (Prod.fst.{u1, u2} α β y)) (Eq.{succ u2} β (Prod.snd.{u1, u2} α β x) (Prod.snd.{u1, u2} α β y))) (And (Wcovby.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2) (Prod.snd.{u1, u2} α β x) (Prod.snd.{u1, u2} α β y)) (Eq.{succ u1} α (Prod.fst.{u1, u2} α β x) (Prod.fst.{u1, u2} α β y))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : PartialOrder.{u1} β] {x : Prod.{u2, u1} α β} {y : Prod.{u2, u1} α β}, Iff (Wcovby.{max u2 u1} (Prod.{u2, u1} α β) (Prod.instPreorderProd.{u2, u1} α β (PartialOrder.toPreorder.{u2} α _inst_1) (PartialOrder.toPreorder.{u1} β _inst_2)) x y) (Or (And (Wcovby.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) (Prod.fst.{u2, u1} α β x) (Prod.fst.{u2, u1} α β y)) (Eq.{succ u1} β (Prod.snd.{u2, u1} α β x) (Prod.snd.{u2, u1} α β y))) (And (Wcovby.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2) (Prod.snd.{u2, u1} α β x) (Prod.snd.{u2, u1} α β y)) (Eq.{succ u2} α (Prod.fst.{u2, u1} α β x) (Prod.fst.{u2, u1} α β y))))
Case conversion may be inaccurate. Consider using '#align prod.wcovby_iff Prod.wcovby_iffₓ'. -/
theorem wcovby_iff : x ⩿ y ↔ x.1 ⩿ y.1 ∧ x.2 = y.2 ∨ x.2 ⩿ y.2 ∧ x.1 = y.1 :=
  by
  cases x
  cases y
  exact mk_wcovby_mk_iff
#align prod.wcovby_iff Prod.wcovby_iff

/- warning: prod.covby_iff -> Prod.covby_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] {x : Prod.{u1, u2} α β} {y : Prod.{u1, u2} α β}, Iff (Covby.{max u1 u2} (Prod.{u1, u2} α β) (Preorder.toLT.{max u1 u2} (Prod.{u1, u2} α β) (Prod.preorder.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2))) x y) (Or (And (Covby.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (Prod.fst.{u1, u2} α β x) (Prod.fst.{u1, u2} α β y)) (Eq.{succ u2} β (Prod.snd.{u1, u2} α β x) (Prod.snd.{u1, u2} α β y))) (And (Covby.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2)) (Prod.snd.{u1, u2} α β x) (Prod.snd.{u1, u2} α β y)) (Eq.{succ u1} α (Prod.fst.{u1, u2} α β x) (Prod.fst.{u1, u2} α β y))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : PartialOrder.{u1} β] {x : Prod.{u2, u1} α β} {y : Prod.{u2, u1} α β}, Iff (Covby.{max u2 u1} (Prod.{u2, u1} α β) (Preorder.toLT.{max u2 u1} (Prod.{u2, u1} α β) (Prod.instPreorderProd.{u2, u1} α β (PartialOrder.toPreorder.{u2} α _inst_1) (PartialOrder.toPreorder.{u1} β _inst_2))) x y) (Or (And (Covby.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) (Prod.fst.{u2, u1} α β x) (Prod.fst.{u2, u1} α β y)) (Eq.{succ u1} β (Prod.snd.{u2, u1} α β x) (Prod.snd.{u2, u1} α β y))) (And (Covby.{u1} β (Preorder.toLT.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)) (Prod.snd.{u2, u1} α β x) (Prod.snd.{u2, u1} α β y)) (Eq.{succ u2} α (Prod.fst.{u2, u1} α β x) (Prod.fst.{u2, u1} α β y))))
Case conversion may be inaccurate. Consider using '#align prod.covby_iff Prod.covby_iffₓ'. -/
theorem covby_iff : x ⋖ y ↔ x.1 ⋖ y.1 ∧ x.2 = y.2 ∨ x.2 ⋖ y.2 ∧ x.1 = y.1 :=
  by
  cases x
  cases y
  exact mk_covby_mk_iff
#align prod.covby_iff Prod.covby_iff

end Prod

