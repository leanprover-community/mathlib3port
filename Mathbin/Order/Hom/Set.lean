/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module order.hom.set
! leanprover-community/mathlib commit 2445c98ae4b87eabebdde552593519b9b6dc350c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Hom.Basic
import Mathbin.Logic.Equiv.Set
import Mathbin.Data.Set.Image

/-!
# Order homomorphisms and sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open OrderDual

variable {F α β γ δ : Type _}

namespace OrderIso

section LE

variable [LE α] [LE β] [LE γ]

/- warning: order_iso.range_eq -> OrderIso.range_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LE.{u1} α] [_inst_2 : LE.{u2} β] (e : OrderIso.{u1, u2} α β _inst_1 _inst_2), Eq.{succ u2} (Set.{u2} β) (Set.range.{u2, succ u1} β α (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β _inst_1 _inst_2) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α _inst_1) (LE.le.{u2} β _inst_2)) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α _inst_1) (LE.le.{u2} β _inst_2)) e)) (Set.univ.{u2} β)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LE.{u2} α] [_inst_2 : LE.{u1} β] (e : OrderIso.{u2, u1} α β _inst_1 _inst_2), Eq.{succ u1} (Set.{u1} β) (Set.range.{u1, succ u2} β α (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) e)))) (Set.univ.{u1} β)
Case conversion may be inaccurate. Consider using '#align order_iso.range_eq OrderIso.range_eqₓ'. -/
theorem range_eq (e : α ≃o β) : Set.range e = Set.univ :=
  e.Surjective.range_eq
#align order_iso.range_eq OrderIso.range_eq

/- warning: order_iso.symm_image_image -> OrderIso.symm_image_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LE.{u1} α] [_inst_2 : LE.{u2} β] (e : OrderIso.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.image.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (OrderIso.{u2, u1} β α _inst_2 _inst_1) (fun (_x : RelIso.{u2, u1} β α (LE.le.{u2} β _inst_2) (LE.le.{u1} α _inst_1)) => β -> α) (RelIso.hasCoeToFun.{u2, u1} β α (LE.le.{u2} β _inst_2) (LE.le.{u1} α _inst_1)) (OrderIso.symm.{u1, u2} α β _inst_1 _inst_2 e)) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β _inst_1 _inst_2) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α _inst_1) (LE.le.{u2} β _inst_2)) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α _inst_1) (LE.le.{u2} β _inst_2)) e) s)) s
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LE.{u2} α] [_inst_2 : LE.{u1} β] (e : OrderIso.{u2, u1} α β _inst_1 _inst_2) (s : Set.{u2} α), Eq.{succ u2} (Set.{u2} α) (Set.image.{u1, u2} β α (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} β α) β α (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} β α)) (RelEmbedding.toEmbedding.{u1, u2} β α (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u1, u2} β α (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (OrderIso.symm.{u2, u1} α β _inst_1 _inst_2 e)))) (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) e))) s)) s
Case conversion may be inaccurate. Consider using '#align order_iso.symm_image_image OrderIso.symm_image_imageₓ'. -/
@[simp]
theorem symm_image_image (e : α ≃o β) (s : Set α) : e.symm '' (e '' s) = s :=
  e.toEquiv.symm_image_image s
#align order_iso.symm_image_image OrderIso.symm_image_image

/- warning: order_iso.image_symm_image -> OrderIso.image_symm_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LE.{u1} α] [_inst_2 : LE.{u2} β] (e : OrderIso.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u2} β), Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β _inst_1 _inst_2) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α _inst_1) (LE.le.{u2} β _inst_2)) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α _inst_1) (LE.le.{u2} β _inst_2)) e) (Set.image.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (OrderIso.{u2, u1} β α _inst_2 _inst_1) (fun (_x : RelIso.{u2, u1} β α (LE.le.{u2} β _inst_2) (LE.le.{u1} α _inst_1)) => β -> α) (RelIso.hasCoeToFun.{u2, u1} β α (LE.le.{u2} β _inst_2) (LE.le.{u1} α _inst_1)) (OrderIso.symm.{u1, u2} α β _inst_1 _inst_2 e)) s)) s
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LE.{u2} α] [_inst_2 : LE.{u1} β] (e : OrderIso.{u2, u1} α β _inst_1 _inst_2) (s : Set.{u1} β), Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) e))) (Set.image.{u1, u2} β α (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} β α) β α (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} β α)) (RelEmbedding.toEmbedding.{u1, u2} β α (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u1, u2} β α (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (OrderIso.symm.{u2, u1} α β _inst_1 _inst_2 e)))) s)) s
Case conversion may be inaccurate. Consider using '#align order_iso.image_symm_image OrderIso.image_symm_imageₓ'. -/
@[simp]
theorem image_symm_image (e : α ≃o β) (s : Set β) : e '' (e.symm '' s) = s :=
  e.toEquiv.image_symm_image s
#align order_iso.image_symm_image OrderIso.image_symm_image

/- warning: order_iso.image_eq_preimage -> OrderIso.image_eq_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LE.{u1} α] [_inst_2 : LE.{u2} β] (e : OrderIso.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u1} α), Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β _inst_1 _inst_2) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α _inst_1) (LE.le.{u2} β _inst_2)) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α _inst_1) (LE.le.{u2} β _inst_2)) e) s) (Set.preimage.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (OrderIso.{u2, u1} β α _inst_2 _inst_1) (fun (_x : RelIso.{u2, u1} β α (LE.le.{u2} β _inst_2) (LE.le.{u1} α _inst_1)) => β -> α) (RelIso.hasCoeToFun.{u2, u1} β α (LE.le.{u2} β _inst_2) (LE.le.{u1} α _inst_1)) (OrderIso.symm.{u1, u2} α β _inst_1 _inst_2 e)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LE.{u2} α] [_inst_2 : LE.{u1} β] (e : OrderIso.{u2, u1} α β _inst_1 _inst_2) (s : Set.{u2} α), Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) e))) s) (Set.preimage.{u1, u2} β α (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} β α) β α (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} β α)) (RelEmbedding.toEmbedding.{u1, u2} β α (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u1, u2} β α (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (OrderIso.symm.{u2, u1} α β _inst_1 _inst_2 e)))) s)
Case conversion may be inaccurate. Consider using '#align order_iso.image_eq_preimage OrderIso.image_eq_preimageₓ'. -/
theorem image_eq_preimage (e : α ≃o β) (s : Set α) : e '' s = e.symm ⁻¹' s :=
  e.toEquiv.image_eq_preimage s
#align order_iso.image_eq_preimage OrderIso.image_eq_preimage

/- warning: order_iso.preimage_symm_preimage -> OrderIso.preimage_symm_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LE.{u1} α] [_inst_2 : LE.{u2} β] (e : OrderIso.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β _inst_1 _inst_2) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α _inst_1) (LE.le.{u2} β _inst_2)) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α _inst_1) (LE.le.{u2} β _inst_2)) e) (Set.preimage.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (OrderIso.{u2, u1} β α _inst_2 _inst_1) (fun (_x : RelIso.{u2, u1} β α (LE.le.{u2} β _inst_2) (LE.le.{u1} α _inst_1)) => β -> α) (RelIso.hasCoeToFun.{u2, u1} β α (LE.le.{u2} β _inst_2) (LE.le.{u1} α _inst_1)) (OrderIso.symm.{u1, u2} α β _inst_1 _inst_2 e)) s)) s
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LE.{u2} α] [_inst_2 : LE.{u1} β] (e : OrderIso.{u2, u1} α β _inst_1 _inst_2) (s : Set.{u2} α), Eq.{succ u2} (Set.{u2} α) (Set.preimage.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) e))) (Set.preimage.{u1, u2} β α (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} β α) β α (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} β α)) (RelEmbedding.toEmbedding.{u1, u2} β α (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u1, u2} β α (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (OrderIso.symm.{u2, u1} α β _inst_1 _inst_2 e)))) s)) s
Case conversion may be inaccurate. Consider using '#align order_iso.preimage_symm_preimage OrderIso.preimage_symm_preimageₓ'. -/
@[simp]
theorem preimage_symm_preimage (e : α ≃o β) (s : Set α) : e ⁻¹' (e.symm ⁻¹' s) = s :=
  e.toEquiv.preimage_symm_preimage s
#align order_iso.preimage_symm_preimage OrderIso.preimage_symm_preimage

/- warning: order_iso.symm_preimage_preimage -> OrderIso.symm_preimage_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LE.{u1} α] [_inst_2 : LE.{u2} β] (e : OrderIso.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u2} β), Eq.{succ u2} (Set.{u2} β) (Set.preimage.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (OrderIso.{u2, u1} β α _inst_2 _inst_1) (fun (_x : RelIso.{u2, u1} β α (LE.le.{u2} β _inst_2) (LE.le.{u1} α _inst_1)) => β -> α) (RelIso.hasCoeToFun.{u2, u1} β α (LE.le.{u2} β _inst_2) (LE.le.{u1} α _inst_1)) (OrderIso.symm.{u1, u2} α β _inst_1 _inst_2 e)) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β _inst_1 _inst_2) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α _inst_1) (LE.le.{u2} β _inst_2)) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α _inst_1) (LE.le.{u2} β _inst_2)) e) s)) s
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LE.{u2} α] [_inst_2 : LE.{u1} β] (e : OrderIso.{u2, u1} α β _inst_1 _inst_2) (s : Set.{u1} β), Eq.{succ u1} (Set.{u1} β) (Set.preimage.{u1, u2} β α (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} β α) β α (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} β α)) (RelEmbedding.toEmbedding.{u1, u2} β α (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u1, u2} β α (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (OrderIso.symm.{u2, u1} α β _inst_1 _inst_2 e)))) (Set.preimage.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) e))) s)) s
Case conversion may be inaccurate. Consider using '#align order_iso.symm_preimage_preimage OrderIso.symm_preimage_preimageₓ'. -/
@[simp]
theorem symm_preimage_preimage (e : α ≃o β) (s : Set β) : e.symm ⁻¹' (e ⁻¹' s) = s :=
  e.toEquiv.symm_preimage_preimage s
#align order_iso.symm_preimage_preimage OrderIso.symm_preimage_preimage

/- warning: order_iso.image_preimage -> OrderIso.image_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LE.{u1} α] [_inst_2 : LE.{u2} β] (e : OrderIso.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u2} β), Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β _inst_1 _inst_2) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α _inst_1) (LE.le.{u2} β _inst_2)) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α _inst_1) (LE.le.{u2} β _inst_2)) e) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β _inst_1 _inst_2) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α _inst_1) (LE.le.{u2} β _inst_2)) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α _inst_1) (LE.le.{u2} β _inst_2)) e) s)) s
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LE.{u2} α] [_inst_2 : LE.{u1} β] (e : OrderIso.{u2, u1} α β _inst_1 _inst_2) (s : Set.{u1} β), Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) e))) (Set.preimage.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) e))) s)) s
Case conversion may be inaccurate. Consider using '#align order_iso.image_preimage OrderIso.image_preimageₓ'. -/
@[simp]
theorem image_preimage (e : α ≃o β) (s : Set β) : e '' (e ⁻¹' s) = s :=
  e.toEquiv.image_preimage s
#align order_iso.image_preimage OrderIso.image_preimage

/- warning: order_iso.preimage_image -> OrderIso.preimage_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LE.{u1} α] [_inst_2 : LE.{u2} β] (e : OrderIso.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β _inst_1 _inst_2) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α _inst_1) (LE.le.{u2} β _inst_2)) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α _inst_1) (LE.le.{u2} β _inst_2)) e) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β _inst_1 _inst_2) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α _inst_1) (LE.le.{u2} β _inst_2)) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α _inst_1) (LE.le.{u2} β _inst_2)) e) s)) s
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LE.{u2} α] [_inst_2 : LE.{u1} β] (e : OrderIso.{u2, u1} α β _inst_1 _inst_2) (s : Set.{u2} α), Eq.{succ u2} (Set.{u2} α) (Set.preimage.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) e))) (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) e))) s)) s
Case conversion may be inaccurate. Consider using '#align order_iso.preimage_image OrderIso.preimage_imageₓ'. -/
@[simp]
theorem preimage_image (e : α ≃o β) (s : Set α) : e ⁻¹' (e '' s) = s :=
  e.toEquiv.preimage_image s
#align order_iso.preimage_image OrderIso.preimage_image

end LE

open Set

variable [Preorder α] [Preorder β] [Preorder γ]

#print OrderIso.setCongr /-
/-- Order isomorphism between two equal sets. -/
def setCongr (s t : Set α) (h : s = t) : s ≃o t
    where
  toEquiv := Equiv.setCongr h
  map_rel_iff' x y := Iff.rfl
#align order_iso.set_congr OrderIso.setCongr
-/

#print OrderIso.Set.univ /-
/-- Order isomorphism between `univ : set α` and `α`. -/
def Set.univ : (Set.univ : Set α) ≃o α
    where
  toEquiv := Equiv.Set.univ α
  map_rel_iff' x y := Iff.rfl
#align order_iso.set.univ OrderIso.Set.univ
-/

end OrderIso

#print StrictMonoOn.orderIso /-
/-- If a function `f` is strictly monotone on a set `s`, then it defines an order isomorphism
between `s` and its image. -/
protected noncomputable def StrictMonoOn.orderIso {α β} [LinearOrder α] [Preorder β] (f : α → β)
    (s : Set α) (hf : StrictMonoOn f s) : s ≃o f '' s
    where
  toEquiv := hf.InjOn.bij_on_image.Equiv _
  map_rel_iff' x y := hf.le_iff_le x.2 y.2
#align strict_mono_on.order_iso StrictMonoOn.orderIso
-/

namespace StrictMono

variable {α β} [LinearOrder α] [Preorder β]

variable (f : α → β) (h_mono : StrictMono f) (h_surj : Function.Surjective f)

#print StrictMono.orderIso /-
/-- A strictly monotone function from a linear order is an order isomorphism between its domain and
its range. -/
@[simps apply]
protected noncomputable def orderIso : α ≃o Set.range f
    where
  toEquiv := Equiv.ofInjective f h_mono.Injective
  map_rel_iff' a b := h_mono.le_iff_le
#align strict_mono.order_iso StrictMono.orderIso
-/

#print StrictMono.orderIsoOfSurjective /-
/-- A strictly monotone surjective function from a linear order is an order isomorphism. -/
noncomputable def orderIsoOfSurjective : α ≃o β :=
  (h_mono.OrderIso f).trans <| (OrderIso.setCongr _ _ h_surj.range_eq).trans OrderIso.Set.univ
#align strict_mono.order_iso_of_surjective StrictMono.orderIsoOfSurjective
-/

/- warning: strict_mono.coe_order_iso_of_surjective -> StrictMono.coe_orderIsoOfSurjective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : Preorder.{u2} β] (f : α -> β) (h_mono : StrictMono.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 f) (h_surj : Function.Surjective.{succ u1, succ u2} α β f), Eq.{max (succ u1) (succ u2)} ((fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) => α -> β) (StrictMono.orderIsoOfSurjective.{u1, u2} α β _inst_1 _inst_2 f h_mono h_surj)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (Preorder.toLE.{u2} β _inst_2)) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2))) (StrictMono.orderIsoOfSurjective.{u1, u2} α β _inst_1 _inst_2 f h_mono h_surj)) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] [_inst_2 : Preorder.{u1} β] (f : α -> β) (h_mono : StrictMono.{u2, u1} α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) _inst_2 f) (h_surj : Function.Surjective.{succ u2, succ u1} α β f), Eq.{max (succ u2) (succ u1)} (forall (a : α), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (StrictMono.orderIsoOfSurjective.{u2, u1} α β _inst_1 _inst_2 f h_mono h_surj)))) f
Case conversion may be inaccurate. Consider using '#align strict_mono.coe_order_iso_of_surjective StrictMono.coe_orderIsoOfSurjectiveₓ'. -/
@[simp]
theorem coe_orderIsoOfSurjective : (orderIsoOfSurjective f h_mono h_surj : α → β) = f :=
  rfl
#align strict_mono.coe_order_iso_of_surjective StrictMono.coe_orderIsoOfSurjective

/- warning: strict_mono.order_iso_of_surjective_symm_apply_self -> StrictMono.orderIsoOfSurjective_symm_apply_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : Preorder.{u2} β] (f : α -> β) (h_mono : StrictMono.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 f) (h_surj : Function.Surjective.{succ u1, succ u2} α β f) (a : α), Eq.{succ u1} α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (OrderIso.{u2, u1} β α (Preorder.toLE.{u2} β _inst_2) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) (fun (_x : RelIso.{u2, u1} β α (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))))) => β -> α) (RelIso.hasCoeToFun.{u2, u1} β α (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))))) (OrderIso.symm.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (Preorder.toLE.{u2} β _inst_2) (StrictMono.orderIsoOfSurjective.{u1, u2} α β _inst_1 _inst_2 f h_mono h_surj)) (f a)) a
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] [_inst_2 : Preorder.{u1} β] (f : α -> β) (h_mono : StrictMono.{u2, u1} α β (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) _inst_2 f) (h_surj : Function.Surjective.{succ u2, succ u1} α β f) (a : α), Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) (f a)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} β α) β α (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} β α)) (RelEmbedding.toEmbedding.{u1, u2} β α (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u1, u2} β α (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (OrderIso.symm.{u2, u1} α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) (Preorder.toLE.{u1} β _inst_2) (StrictMono.orderIsoOfSurjective.{u2, u1} α β _inst_1 _inst_2 f h_mono h_surj)))) (f a)) a
Case conversion may be inaccurate. Consider using '#align strict_mono.order_iso_of_surjective_symm_apply_self StrictMono.orderIsoOfSurjective_symm_apply_selfₓ'. -/
@[simp]
theorem orderIsoOfSurjective_symm_apply_self (a : α) :
    (orderIsoOfSurjective f h_mono h_surj).symm (f a) = a :=
  (orderIsoOfSurjective f h_mono h_surj).symm_apply_apply _
#align strict_mono.order_iso_of_surjective_symm_apply_self StrictMono.orderIsoOfSurjective_symm_apply_self

/- warning: strict_mono.order_iso_of_surjective_self_symm_apply -> StrictMono.orderIsoOfSurjective_self_symm_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : Preorder.{u2} β] (f : α -> β) (h_mono : StrictMono.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) _inst_2 f) (h_surj : Function.Surjective.{succ u1, succ u2} α β f) (b : β), Eq.{succ u2} β (f (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (OrderIso.{u2, u1} β α (Preorder.toLE.{u2} β _inst_2) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) (fun (_x : RelIso.{u2, u1} β α (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))))) => β -> α) (RelIso.hasCoeToFun.{u2, u1} β α (LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))))) (OrderIso.symm.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (Preorder.toLE.{u2} β _inst_2) (StrictMono.orderIsoOfSurjective.{u1, u2} α β _inst_1 _inst_2 f h_mono h_surj)) b)) b
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : Preorder.{u2} β] (f : α -> β) (h_mono : StrictMono.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) _inst_2 f) (h_surj : Function.Surjective.{succ u1, succ u2} α β f) (b : β), Eq.{succ u2} β (f (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β α) β α (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β α)) (RelEmbedding.toEmbedding.{u2, u1} β α (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u2, u1} β α (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (OrderIso.symm.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (Preorder.toLE.{u2} β _inst_2) (StrictMono.orderIsoOfSurjective.{u1, u2} α β _inst_1 _inst_2 f h_mono h_surj)))) b)) b
Case conversion may be inaccurate. Consider using '#align strict_mono.order_iso_of_surjective_self_symm_apply StrictMono.orderIsoOfSurjective_self_symm_applyₓ'. -/
theorem orderIsoOfSurjective_self_symm_apply (b : β) :
    f ((orderIsoOfSurjective f h_mono h_surj).symm b) = b :=
  (orderIsoOfSurjective f h_mono h_surj).apply_symm_apply _
#align strict_mono.order_iso_of_surjective_self_symm_apply StrictMono.orderIsoOfSurjective_self_symm_apply

end StrictMono

section BooleanAlgebra

variable (α) [BooleanAlgebra α]

#print OrderIso.compl /-
/-- Taking complements as an order isomorphism to the order dual. -/
@[simps]
def OrderIso.compl : α ≃o αᵒᵈ where
  toFun := OrderDual.toDual ∘ compl
  invFun := compl ∘ OrderDual.ofDual
  left_inv := compl_compl
  right_inv := compl_compl
  map_rel_iff' x y := compl_le_compl_iff_le
#align order_iso.compl OrderIso.compl
-/

#print compl_strictAnti /-
theorem compl_strictAnti : StrictAnti (compl : α → α) :=
  (OrderIso.compl α).StrictMono
#align compl_strict_anti compl_strictAnti
-/

#print compl_antitone /-
theorem compl_antitone : Antitone (compl : α → α) :=
  (OrderIso.compl α).Monotone
#align compl_antitone compl_antitone
-/

end BooleanAlgebra

