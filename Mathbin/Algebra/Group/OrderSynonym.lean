/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies

! This file was ported from Lean 3 source module algebra.group.order_synonym
! leanprover-community/mathlib commit 59694bd07f0a39c5beccba34bd9f413a160782bf
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.Defs
import Mathbin.Order.Synonym

/-!
# Group structure on the order type synonyms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Transfer algebraic instances from `α` to `αᵒᵈ` and `lex α`.
-/


open OrderDual

variable {α β : Type _}

/-! ### `order_dual` -/


@[to_additive]
instance [h : One α] : One αᵒᵈ :=
  h

@[to_additive]
instance [h : Mul α] : Mul αᵒᵈ :=
  h

@[to_additive]
instance [h : Inv α] : Inv αᵒᵈ :=
  h

@[to_additive]
instance [h : Div α] : Div αᵒᵈ :=
  h

@[to_additive]
instance [h : SMul α β] : SMul α βᵒᵈ :=
  h

#print instSMulOrderDual' /-
@[to_additive]
instance instSMulOrderDual' [h : SMul α β] : SMul αᵒᵈ β :=
  h
#align order_dual.has_smul' instSMulOrderDual'
-/

#print instPowOrderDual /-
@[to_additive instSMulOrderDual]
instance instPowOrderDual [h : Pow α β] : Pow αᵒᵈ β :=
  h
#align order_dual.has_pow instPowOrderDual
#align order_dual.has_smul instSMulOrderDual
-/

#print instPowOrderDual' /-
@[to_additive instSMulOrderDual']
instance instPowOrderDual' [h : Pow α β] : Pow α βᵒᵈ :=
  h
#align order_dual.has_pow' instPowOrderDual'
#align order_dual.has_smul' instSMulOrderDual'
-/

@[to_additive]
instance [h : Semigroup α] : Semigroup αᵒᵈ :=
  h

@[to_additive]
instance [h : CommSemigroup α] : CommSemigroup αᵒᵈ :=
  h

@[to_additive]
instance [h : LeftCancelSemigroup α] : LeftCancelSemigroup αᵒᵈ :=
  h

@[to_additive]
instance [h : RightCancelSemigroup α] : RightCancelSemigroup αᵒᵈ :=
  h

@[to_additive]
instance [h : MulOneClass α] : MulOneClass αᵒᵈ :=
  h

@[to_additive]
instance [h : Monoid α] : Monoid αᵒᵈ :=
  h

@[to_additive]
instance [h : CommMonoid α] : CommMonoid αᵒᵈ :=
  h

@[to_additive]
instance [h : LeftCancelMonoid α] : LeftCancelMonoid αᵒᵈ :=
  h

@[to_additive]
instance [h : RightCancelMonoid α] : RightCancelMonoid αᵒᵈ :=
  h

@[to_additive]
instance [h : CancelMonoid α] : CancelMonoid αᵒᵈ :=
  h

@[to_additive]
instance [h : CancelCommMonoid α] : CancelCommMonoid αᵒᵈ :=
  h

@[to_additive]
instance [h : InvolutiveInv α] : InvolutiveInv αᵒᵈ :=
  h

@[to_additive]
instance [h : DivInvMonoid α] : DivInvMonoid αᵒᵈ :=
  h

@[to_additive OrderDual.subtractionMonoid]
instance [h : DivisionMonoid α] : DivisionMonoid αᵒᵈ :=
  h

@[to_additive OrderDual.subtractionCommMonoid]
instance [h : DivisionCommMonoid α] : DivisionCommMonoid αᵒᵈ :=
  h

@[to_additive]
instance [h : Group α] : Group αᵒᵈ :=
  h

@[to_additive]
instance [h : CommGroup α] : CommGroup αᵒᵈ :=
  h

#print toDual_one /-
@[simp, to_additive]
theorem toDual_one [One α] : toDual (1 : α) = 1 :=
  rfl
#align to_dual_one toDual_one
#align to_dual_zero toDual_zero
-/

#print ofDual_one /-
@[simp, to_additive]
theorem ofDual_one [One α] : (ofDual 1 : α) = 1 :=
  rfl
#align of_dual_one ofDual_one
#align of_dual_zero ofDual_zero
-/

#print toDual_mul /-
@[simp, to_additive]
theorem toDual_mul [Mul α] (a b : α) : toDual (a * b) = toDual a * toDual b :=
  rfl
#align to_dual_mul toDual_mul
#align to_dual_add toDual_add
-/

#print ofDual_mul /-
@[simp, to_additive]
theorem ofDual_mul [Mul α] (a b : αᵒᵈ) : ofDual (a * b) = ofDual a * ofDual b :=
  rfl
#align of_dual_mul ofDual_mul
#align of_dual_add ofDual_add
-/

#print toDual_inv /-
@[simp, to_additive]
theorem toDual_inv [Inv α] (a : α) : toDual a⁻¹ = (toDual a)⁻¹ :=
  rfl
#align to_dual_inv toDual_inv
#align to_dual_neg toDual_neg
-/

#print ofDual_inv /-
@[simp, to_additive]
theorem ofDual_inv [Inv α] (a : αᵒᵈ) : ofDual a⁻¹ = (ofDual a)⁻¹ :=
  rfl
#align of_dual_inv ofDual_inv
#align of_dual_neg ofDual_neg
-/

#print toDual_div /-
@[simp, to_additive]
theorem toDual_div [Div α] (a b : α) : toDual (a / b) = toDual a / toDual b :=
  rfl
#align to_dual_div toDual_div
#align to_dual_sub toDual_sub
-/

#print ofDual_div /-
@[simp, to_additive]
theorem ofDual_div [Div α] (a b : αᵒᵈ) : ofDual (a / b) = ofDual a / ofDual b :=
  rfl
#align of_dual_div ofDual_div
#align of_dual_sub ofDual_sub
-/

/- warning: to_dual_smul -> toDual_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u2} α β] (a : α) (b : β), Eq.{succ u2} (OrderDual.{u2} β) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} β (OrderDual.{u2} β)) (fun (_x : Equiv.{succ u2, succ u2} β (OrderDual.{u2} β)) => β -> (OrderDual.{u2} β)) (Equiv.hasCoeToFun.{succ u2, succ u2} β (OrderDual.{u2} β)) (OrderDual.toDual.{u2} β) (SMul.smul.{u1, u2} α β _inst_1 a b)) (SMul.smul.{u1, u2} α (OrderDual.{u2} β) (instSMulOrderDual.{u1, u2} α β _inst_1) a (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} β (OrderDual.{u2} β)) (fun (_x : Equiv.{succ u2, succ u2} β (OrderDual.{u2} β)) => β -> (OrderDual.{u2} β)) (Equiv.hasCoeToFun.{succ u2, succ u2} β (OrderDual.{u2} β)) (OrderDual.toDual.{u2} β) b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SMul.{u2, u1} α β] (a : α) (b : β), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => OrderDual.{u1} β) (HSMul.hSMul.{u2, u1, u1} α β β (instHSMul.{u2, u1} α β _inst_1) a b)) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (OrderDual.{u1} β)) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => OrderDual.{u1} β) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (OrderDual.{u1} β)) β (OrderDual.{u1} β) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (OrderDual.{u1} β)) β (OrderDual.{u1} β) (Equiv.instEquivLikeEquiv.{succ u1, succ u1} β (OrderDual.{u1} β)))) (OrderDual.toDual.{u1} β) (HSMul.hSMul.{u2, u1, u1} α β β (instHSMul.{u2, u1} α β _inst_1) a b)) (HSMul.hSMul.{u2, u1, u1} α ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => OrderDual.{u1} β) b) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => OrderDual.{u1} β) b) (instHSMul.{u2, u1} α ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => OrderDual.{u1} β) b) (instSMulOrderDual.{u2, u1} α β _inst_1)) a (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (OrderDual.{u1} β)) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => OrderDual.{u1} β) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (OrderDual.{u1} β)) β (OrderDual.{u1} β) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (OrderDual.{u1} β)) β (OrderDual.{u1} β) (Equiv.instEquivLikeEquiv.{succ u1, succ u1} β (OrderDual.{u1} β)))) (OrderDual.toDual.{u1} β) b))
Case conversion may be inaccurate. Consider using '#align to_dual_smul toDual_smulₓ'. -/
@[simp, to_additive]
theorem toDual_smul [SMul α β] (a : α) (b : β) : toDual (a • b) = a • toDual b :=
  rfl
#align to_dual_smul toDual_smul
#align to_dual_vadd toDual_vadd

/- warning: of_dual_smul -> ofDual_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u2} α β] (a : α) (b : OrderDual.{u2} β), Eq.{succ u2} β (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} β) β) (fun (_x : Equiv.{succ u2, succ u2} (OrderDual.{u2} β) β) => (OrderDual.{u2} β) -> β) (Equiv.hasCoeToFun.{succ u2, succ u2} (OrderDual.{u2} β) β) (OrderDual.ofDual.{u2} β) (SMul.smul.{u1, u2} α (OrderDual.{u2} β) (instSMulOrderDual.{u1, u2} α β _inst_1) a b)) (SMul.smul.{u1, u2} α β _inst_1 a (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} β) β) (fun (_x : Equiv.{succ u2, succ u2} (OrderDual.{u2} β) β) => (OrderDual.{u2} β) -> β) (Equiv.hasCoeToFun.{succ u2, succ u2} (OrderDual.{u2} β) β) (OrderDual.ofDual.{u2} β) b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SMul.{u2, u1} α β] (a : α) (b : OrderDual.{u1} β), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : OrderDual.{u1} β) => β) (HSMul.hSMul.{u2, u1, u1} α (OrderDual.{u1} β) (OrderDual.{u1} β) (instHSMul.{u2, u1} α (OrderDual.{u1} β) (instSMulOrderDual.{u2, u1} α β _inst_1)) a b)) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} β) β) (OrderDual.{u1} β) (fun (_x : OrderDual.{u1} β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : OrderDual.{u1} β) => β) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} β) β) (OrderDual.{u1} β) β (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} β) β) (OrderDual.{u1} β) β (Equiv.instEquivLikeEquiv.{succ u1, succ u1} (OrderDual.{u1} β) β))) (OrderDual.ofDual.{u1} β) (HSMul.hSMul.{u2, u1, u1} α (OrderDual.{u1} β) (OrderDual.{u1} β) (instHSMul.{u2, u1} α (OrderDual.{u1} β) (instSMulOrderDual.{u2, u1} α β _inst_1)) a b)) (HSMul.hSMul.{u2, u1, u1} α ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : OrderDual.{u1} β) => β) b) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : OrderDual.{u1} β) => β) b) (instHSMul.{u2, u1} α ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : OrderDual.{u1} β) => β) b) _inst_1) a (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} β) β) (OrderDual.{u1} β) (fun (_x : OrderDual.{u1} β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : OrderDual.{u1} β) => β) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} β) β) (OrderDual.{u1} β) β (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} β) β) (OrderDual.{u1} β) β (Equiv.instEquivLikeEquiv.{succ u1, succ u1} (OrderDual.{u1} β) β))) (OrderDual.ofDual.{u1} β) b))
Case conversion may be inaccurate. Consider using '#align of_dual_smul ofDual_smulₓ'. -/
@[simp, to_additive]
theorem ofDual_smul [SMul α β] (a : α) (b : βᵒᵈ) : ofDual (a • b) = a • ofDual b :=
  rfl
#align of_dual_smul ofDual_smul
#align of_dual_vadd ofDual_vadd

/- warning: to_dual_smul' -> toDual_smul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u2} α β] (a : α) (b : β), Eq.{succ u2} β (SMul.smul.{u1, u2} (OrderDual.{u1} α) β (instSMulOrderDual'.{u1, u2} α β _inst_1) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) => α -> (OrderDual.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (OrderDual.{u1} α)) (OrderDual.toDual.{u1} α) a) b) (SMul.smul.{u1, u2} α β _inst_1 a b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SMul.{u2, u1} α β] (a : α) (b : β), Eq.{succ u1} β (HSMul.hSMul.{u2, u1, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => OrderDual.{u2} α) a) β β (instHSMul.{u2, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => OrderDual.{u2} α) a) β (instSMulOrderDual'.{u2, u1} α β _inst_1)) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => OrderDual.{u2} α) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (OrderDual.{u2} α) (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (OrderDual.{u2} α) (Equiv.instEquivLikeEquiv.{succ u2, succ u2} α (OrderDual.{u2} α)))) (OrderDual.toDual.{u2} α) a) b) (HSMul.hSMul.{u2, u1, u1} α β β (instHSMul.{u2, u1} α β _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align to_dual_smul' toDual_smul'ₓ'. -/
@[simp, to_additive]
theorem toDual_smul' [SMul α β] (a : α) (b : β) : toDual a • b = a • b :=
  rfl
#align to_dual_smul' toDual_smul'
#align to_dual_vadd' toDual_vadd'

/- warning: of_dual_smul' -> ofDual_smul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u2} α β] (a : OrderDual.{u1} α) (b : β), Eq.{succ u2} β (SMul.smul.{u1, u2} α β _inst_1 (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) => (OrderDual.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.ofDual.{u1} α) a) b) (SMul.smul.{u1, u2} (OrderDual.{u1} α) β (instSMulOrderDual'.{u1, u2} α β _inst_1) a b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SMul.{u2, u1} α β] (a : OrderDual.{u2} α) (b : β), Eq.{succ u1} β (HSMul.hSMul.{u2, u1, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : OrderDual.{u2} α) => α) a) β β (instHSMul.{u2, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : OrderDual.{u2} α) => α) a) β _inst_1) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.{u2} α) (fun (_x : OrderDual.{u2} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : OrderDual.{u2} α) => α) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.{u2} α) α (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.{u2} α) α (Equiv.instEquivLikeEquiv.{succ u2, succ u2} (OrderDual.{u2} α) α))) (OrderDual.ofDual.{u2} α) a) b) (HSMul.hSMul.{u2, u1, u1} (OrderDual.{u2} α) β β (instHSMul.{u2, u1} (OrderDual.{u2} α) β (instSMulOrderDual'.{u2, u1} α β _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align of_dual_smul' ofDual_smul'ₓ'. -/
@[simp, to_additive]
theorem ofDual_smul' [SMul α β] (a : αᵒᵈ) (b : β) : ofDual a • b = a • b :=
  rfl
#align of_dual_smul' ofDual_smul'
#align of_dual_vadd' ofDual_vadd'

/- warning: to_dual_pow -> toDual_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Pow.{u1, u2} α β] (a : α) (b : β), Eq.{succ u1} (OrderDual.{u1} α) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) => α -> (OrderDual.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (OrderDual.{u1} α)) (OrderDual.toDual.{u1} α) (HPow.hPow.{u1, u2, u1} α β α (instHPow.{u1, u2} α β _inst_1) a b)) (HPow.hPow.{u1, u2, u1} (OrderDual.{u1} α) β (OrderDual.{u1} α) (instHPow.{u1, u2} (OrderDual.{u1} α) β (instPowOrderDual.{u1, u2} α β _inst_1)) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) => α -> (OrderDual.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (OrderDual.{u1} α)) (OrderDual.toDual.{u1} α) a) b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Pow.{u2, u1} α β] (a : α) (b : β), Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => OrderDual.{u2} α) (HPow.hPow.{u2, u1, u2} α β α (instHPow.{u2, u1} α β _inst_1) a b)) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => OrderDual.{u2} α) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (OrderDual.{u2} α) (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (OrderDual.{u2} α) (Equiv.instEquivLikeEquiv.{succ u2, succ u2} α (OrderDual.{u2} α)))) (OrderDual.toDual.{u2} α) (HPow.hPow.{u2, u1, u2} α β α (instHPow.{u2, u1} α β _inst_1) a b)) (HPow.hPow.{u2, u1, u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => OrderDual.{u2} α) a) β ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => OrderDual.{u2} α) a) (instHPow.{u2, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => OrderDual.{u2} α) a) β (instPowOrderDual.{u2, u1} α β _inst_1)) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => OrderDual.{u2} α) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (OrderDual.{u2} α) (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (OrderDual.{u2} α) (Equiv.instEquivLikeEquiv.{succ u2, succ u2} α (OrderDual.{u2} α)))) (OrderDual.toDual.{u2} α) a) b)
Case conversion may be inaccurate. Consider using '#align to_dual_pow toDual_powₓ'. -/
@[simp, to_additive toDual_smul, to_additive_reorder 1 4]
theorem toDual_pow [Pow α β] (a : α) (b : β) : toDual (a ^ b) = toDual a ^ b :=
  rfl
#align to_dual_pow toDual_pow
#align to_dual_smul toDual_smul

/- warning: of_dual_pow -> ofDual_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Pow.{u1, u2} α β] (a : OrderDual.{u1} α) (b : β), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) => (OrderDual.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.ofDual.{u1} α) (HPow.hPow.{u1, u2, u1} (OrderDual.{u1} α) β (OrderDual.{u1} α) (instHPow.{u1, u2} (OrderDual.{u1} α) β (instPowOrderDual.{u1, u2} α β _inst_1)) a b)) (HPow.hPow.{u1, u2, u1} α β α (instHPow.{u1, u2} α β _inst_1) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) => (OrderDual.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.ofDual.{u1} α) a) b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Pow.{u2, u1} α β] (a : OrderDual.{u2} α) (b : β), Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : OrderDual.{u2} α) => α) (HPow.hPow.{u2, u1, u2} (OrderDual.{u2} α) β (OrderDual.{u2} α) (instHPow.{u2, u1} (OrderDual.{u2} α) β (instPowOrderDual.{u2, u1} α β _inst_1)) a b)) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.{u2} α) (fun (_x : OrderDual.{u2} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : OrderDual.{u2} α) => α) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.{u2} α) α (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.{u2} α) α (Equiv.instEquivLikeEquiv.{succ u2, succ u2} (OrderDual.{u2} α) α))) (OrderDual.ofDual.{u2} α) (HPow.hPow.{u2, u1, u2} (OrderDual.{u2} α) β (OrderDual.{u2} α) (instHPow.{u2, u1} (OrderDual.{u2} α) β (instPowOrderDual.{u2, u1} α β _inst_1)) a b)) (HPow.hPow.{u2, u1, u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : OrderDual.{u2} α) => α) a) β ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : OrderDual.{u2} α) => α) a) (instHPow.{u2, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : OrderDual.{u2} α) => α) a) β _inst_1) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.{u2} α) (fun (_x : OrderDual.{u2} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : OrderDual.{u2} α) => α) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.{u2} α) α (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.{u2} α) α (Equiv.instEquivLikeEquiv.{succ u2, succ u2} (OrderDual.{u2} α) α))) (OrderDual.ofDual.{u2} α) a) b)
Case conversion may be inaccurate. Consider using '#align of_dual_pow ofDual_powₓ'. -/
@[simp, to_additive ofDual_smul, to_additive_reorder 1 4]
theorem ofDual_pow [Pow α β] (a : αᵒᵈ) (b : β) : ofDual (a ^ b) = ofDual a ^ b :=
  rfl
#align of_dual_pow ofDual_pow
#align of_dual_smul ofDual_smul

/- warning: pow_to_dual -> pow_toDual is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Pow.{u1, u2} α β] (a : α) (b : β), Eq.{succ u1} α (HPow.hPow.{u1, u2, u1} α (OrderDual.{u2} β) α (instHPow.{u1, u2} α (OrderDual.{u2} β) (instPowOrderDual'.{u1, u2} α β _inst_1)) a (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} β (OrderDual.{u2} β)) (fun (_x : Equiv.{succ u2, succ u2} β (OrderDual.{u2} β)) => β -> (OrderDual.{u2} β)) (Equiv.hasCoeToFun.{succ u2, succ u2} β (OrderDual.{u2} β)) (OrderDual.toDual.{u2} β) b)) (HPow.hPow.{u1, u2, u1} α β α (instHPow.{u1, u2} α β _inst_1) a b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Pow.{u2, u1} α β] (a : α) (b : β), Eq.{succ u2} α (HPow.hPow.{u2, u1, u2} α ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => OrderDual.{u1} β) b) α (instHPow.{u2, u1} α ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => OrderDual.{u1} β) b) (instPowOrderDual'.{u2, u1} α β _inst_1)) a (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (OrderDual.{u1} β)) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => OrderDual.{u1} β) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (OrderDual.{u1} β)) β (OrderDual.{u1} β) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (OrderDual.{u1} β)) β (OrderDual.{u1} β) (Equiv.instEquivLikeEquiv.{succ u1, succ u1} β (OrderDual.{u1} β)))) (OrderDual.toDual.{u1} β) b)) (HPow.hPow.{u2, u1, u2} α β α (instHPow.{u2, u1} α β _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align pow_to_dual pow_toDualₓ'. -/
@[simp, to_additive toDual_smul', to_additive_reorder 1 4]
theorem pow_toDual [Pow α β] (a : α) (b : β) : a ^ toDual b = a ^ b :=
  rfl
#align pow_to_dual pow_toDual
#align to_dual_smul' toDual_smul'

/- warning: pow_of_dual -> pow_ofDual is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Pow.{u1, u2} α β] (a : α) (b : OrderDual.{u2} β), Eq.{succ u1} α (HPow.hPow.{u1, u2, u1} α β α (instHPow.{u1, u2} α β _inst_1) a (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} β) β) (fun (_x : Equiv.{succ u2, succ u2} (OrderDual.{u2} β) β) => (OrderDual.{u2} β) -> β) (Equiv.hasCoeToFun.{succ u2, succ u2} (OrderDual.{u2} β) β) (OrderDual.ofDual.{u2} β) b)) (HPow.hPow.{u1, u2, u1} α (OrderDual.{u2} β) α (instHPow.{u1, u2} α (OrderDual.{u2} β) (instPowOrderDual'.{u1, u2} α β _inst_1)) a b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Pow.{u2, u1} α β] (a : α) (b : OrderDual.{u1} β), Eq.{succ u2} α (HPow.hPow.{u2, u1, u2} α ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : OrderDual.{u1} β) => β) b) α (instHPow.{u2, u1} α ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : OrderDual.{u1} β) => β) b) _inst_1) a (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} β) β) (OrderDual.{u1} β) (fun (_x : OrderDual.{u1} β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : OrderDual.{u1} β) => β) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} β) β) (OrderDual.{u1} β) β (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} β) β) (OrderDual.{u1} β) β (Equiv.instEquivLikeEquiv.{succ u1, succ u1} (OrderDual.{u1} β) β))) (OrderDual.ofDual.{u1} β) b)) (HPow.hPow.{u2, u1, u2} α (OrderDual.{u1} β) α (instHPow.{u2, u1} α (OrderDual.{u1} β) (instPowOrderDual'.{u2, u1} α β _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align pow_of_dual pow_ofDualₓ'. -/
@[simp, to_additive ofDual_smul', to_additive_reorder 1 4]
theorem pow_ofDual [Pow α β] (a : α) (b : βᵒᵈ) : a ^ ofDual b = a ^ b :=
  rfl
#align pow_of_dual pow_ofDual
#align of_dual_smul' ofDual_smul'

/-! ### Lexicographical order -/


@[to_additive]
instance [h : One α] : One (Lex α) :=
  h

@[to_additive]
instance [h : Mul α] : Mul (Lex α) :=
  h

@[to_additive]
instance [h : Inv α] : Inv (Lex α) :=
  h

@[to_additive]
instance [h : Div α] : Div (Lex α) :=
  h

@[to_additive]
instance [h : SMul α β] : SMul α (Lex β) :=
  h

#print instSMulLex' /-
@[to_additive]
instance instSMulLex' [h : SMul α β] : SMul (Lex α) β :=
  h
#align lex.has_smul' instSMulLex'
-/

#print instPowLex /-
@[to_additive instSMulLex]
instance instPowLex [h : Pow α β] : Pow (Lex α) β :=
  h
#align lex.has_pow instPowLex
#align lex.has_smul instSMulLex
-/

#print instPowLex' /-
@[to_additive instSMulLex']
instance instPowLex' [h : Pow α β] : Pow α (Lex β) :=
  h
#align lex.has_pow' instPowLex'
#align lex.has_smul' instSMulLex'
-/

@[to_additive]
instance [h : Semigroup α] : Semigroup (Lex α) :=
  h

@[to_additive]
instance [h : CommSemigroup α] : CommSemigroup (Lex α) :=
  h

@[to_additive]
instance [h : LeftCancelSemigroup α] : LeftCancelSemigroup (Lex α) :=
  h

@[to_additive]
instance [h : RightCancelSemigroup α] : RightCancelSemigroup (Lex α) :=
  h

@[to_additive]
instance [h : MulOneClass α] : MulOneClass (Lex α) :=
  h

@[to_additive]
instance [h : Monoid α] : Monoid (Lex α) :=
  h

@[to_additive]
instance [h : CommMonoid α] : CommMonoid (Lex α) :=
  h

@[to_additive]
instance [h : LeftCancelMonoid α] : LeftCancelMonoid (Lex α) :=
  h

@[to_additive]
instance [h : RightCancelMonoid α] : RightCancelMonoid (Lex α) :=
  h

@[to_additive]
instance [h : CancelMonoid α] : CancelMonoid (Lex α) :=
  h

@[to_additive]
instance [h : CancelCommMonoid α] : CancelCommMonoid (Lex α) :=
  h

@[to_additive]
instance [h : InvolutiveInv α] : InvolutiveInv (Lex α) :=
  h

@[to_additive]
instance [h : DivInvMonoid α] : DivInvMonoid (Lex α) :=
  h

@[to_additive OrderDual.subtractionMonoid]
instance [h : DivisionMonoid α] : DivisionMonoid (Lex α) :=
  h

@[to_additive OrderDual.subtractionCommMonoid]
instance [h : DivisionCommMonoid α] : DivisionCommMonoid (Lex α) :=
  h

@[to_additive]
instance [h : Group α] : Group (Lex α) :=
  h

@[to_additive]
instance [h : CommGroup α] : CommGroup (Lex α) :=
  h

#print toLex_one /-
@[simp, to_additive]
theorem toLex_one [One α] : toLex (1 : α) = 1 :=
  rfl
#align to_lex_one toLex_one
#align to_lex_zero toLex_zero
-/

#print ofLex_one /-
@[simp, to_additive]
theorem ofLex_one [One α] : (ofLex 1 : α) = 1 :=
  rfl
#align of_lex_one ofLex_one
#align of_lex_zero ofLex_zero
-/

#print toLex_mul /-
@[simp, to_additive]
theorem toLex_mul [Mul α] (a b : α) : toLex (a * b) = toLex a * toLex b :=
  rfl
#align to_lex_mul toLex_mul
#align to_lex_add toLex_add
-/

#print ofLex_mul /-
@[simp, to_additive]
theorem ofLex_mul [Mul α] (a b : Lex α) : ofLex (a * b) = ofLex a * ofLex b :=
  rfl
#align of_lex_mul ofLex_mul
#align of_lex_add ofLex_add
-/

#print toLex_inv /-
@[simp, to_additive]
theorem toLex_inv [Inv α] (a : α) : toLex a⁻¹ = (toLex a)⁻¹ :=
  rfl
#align to_lex_inv toLex_inv
#align to_lex_neg toLex_neg
-/

#print ofLex_inv /-
@[simp, to_additive]
theorem ofLex_inv [Inv α] (a : Lex α) : ofLex a⁻¹ = (ofLex a)⁻¹ :=
  rfl
#align of_lex_inv ofLex_inv
#align of_lex_neg ofLex_neg
-/

#print toLex_div /-
@[simp, to_additive]
theorem toLex_div [Div α] (a b : α) : toLex (a / b) = toLex a / toLex b :=
  rfl
#align to_lex_div toLex_div
#align to_lex_sub toLex_sub
-/

#print ofLex_div /-
@[simp, to_additive]
theorem ofLex_div [Div α] (a b : Lex α) : ofLex (a / b) = ofLex a / ofLex b :=
  rfl
#align of_lex_div ofLex_div
#align of_lex_sub ofLex_sub
-/

/- warning: to_lex_smul -> toLex_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u2} α β] (a : α) (b : β), Eq.{succ u2} (Lex.{u2} β) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} β (Lex.{u2} β)) (fun (_x : Equiv.{succ u2, succ u2} β (Lex.{u2} β)) => β -> (Lex.{u2} β)) (Equiv.hasCoeToFun.{succ u2, succ u2} β (Lex.{u2} β)) (toLex.{u2} β) (SMul.smul.{u1, u2} α β _inst_1 a b)) (SMul.smul.{u1, u2} α (Lex.{u2} β) (instSMulLex.{u1, u2} α β _inst_1) a (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} β (Lex.{u2} β)) (fun (_x : Equiv.{succ u2, succ u2} β (Lex.{u2} β)) => β -> (Lex.{u2} β)) (Equiv.hasCoeToFun.{succ u2, succ u2} β (Lex.{u2} β)) (toLex.{u2} β) b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SMul.{u2, u1} α β] (a : α) (b : β), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => Lex.{u1} β) (HSMul.hSMul.{u2, u1, u1} α β β (instHSMul.{u2, u1} α β _inst_1) a b)) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (Lex.{u1} β)) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => Lex.{u1} β) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (Lex.{u1} β)) β (Lex.{u1} β) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (Lex.{u1} β)) β (Lex.{u1} β) (Equiv.instEquivLikeEquiv.{succ u1, succ u1} β (Lex.{u1} β)))) (toLex.{u1} β) (HSMul.hSMul.{u2, u1, u1} α β β (instHSMul.{u2, u1} α β _inst_1) a b)) (HSMul.hSMul.{u2, u1, u1} α ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => Lex.{u1} β) b) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => Lex.{u1} β) b) (instHSMul.{u2, u1} α ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => Lex.{u1} β) b) (instSMulLex.{u2, u1} α β _inst_1)) a (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (Lex.{u1} β)) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => Lex.{u1} β) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (Lex.{u1} β)) β (Lex.{u1} β) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (Lex.{u1} β)) β (Lex.{u1} β) (Equiv.instEquivLikeEquiv.{succ u1, succ u1} β (Lex.{u1} β)))) (toLex.{u1} β) b))
Case conversion may be inaccurate. Consider using '#align to_lex_smul toLex_smulₓ'. -/
@[simp, to_additive]
theorem toLex_smul [SMul α β] (a : α) (b : β) : toLex (a • b) = a • toLex b :=
  rfl
#align to_lex_smul toLex_smul
#align to_lex_vadd toLex_vadd

/- warning: of_lex_smul -> ofLex_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u2} α β] (a : α) (b : Lex.{u2} β), Eq.{succ u2} β (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} (Lex.{u2} β) β) (fun (_x : Equiv.{succ u2, succ u2} (Lex.{u2} β) β) => (Lex.{u2} β) -> β) (Equiv.hasCoeToFun.{succ u2, succ u2} (Lex.{u2} β) β) (ofLex.{u2} β) (SMul.smul.{u1, u2} α (Lex.{u2} β) (instSMulLex.{u1, u2} α β _inst_1) a b)) (SMul.smul.{u1, u2} α β _inst_1 a (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} (Lex.{u2} β) β) (fun (_x : Equiv.{succ u2, succ u2} (Lex.{u2} β) β) => (Lex.{u2} β) -> β) (Equiv.hasCoeToFun.{succ u2, succ u2} (Lex.{u2} β) β) (ofLex.{u2} β) b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SMul.{u2, u1} α β] (a : α) (b : Lex.{u1} β), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Lex.{u1} β) => β) (HSMul.hSMul.{u2, u1, u1} α (Lex.{u1} β) (Lex.{u1} β) (instHSMul.{u2, u1} α (Lex.{u1} β) (instSMulLex.{u2, u1} α β _inst_1)) a b)) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Lex.{u1} β) β) (Lex.{u1} β) (fun (_x : Lex.{u1} β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Lex.{u1} β) => β) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Lex.{u1} β) β) (Lex.{u1} β) β (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Lex.{u1} β) β) (Lex.{u1} β) β (Equiv.instEquivLikeEquiv.{succ u1, succ u1} (Lex.{u1} β) β))) (ofLex.{u1} β) (HSMul.hSMul.{u2, u1, u1} α (Lex.{u1} β) (Lex.{u1} β) (instHSMul.{u2, u1} α (Lex.{u1} β) (instSMulLex.{u2, u1} α β _inst_1)) a b)) (HSMul.hSMul.{u2, u1, u1} α ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Lex.{u1} β) => β) b) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Lex.{u1} β) => β) b) (instHSMul.{u2, u1} α ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Lex.{u1} β) => β) b) _inst_1) a (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Lex.{u1} β) β) (Lex.{u1} β) (fun (_x : Lex.{u1} β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Lex.{u1} β) => β) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Lex.{u1} β) β) (Lex.{u1} β) β (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Lex.{u1} β) β) (Lex.{u1} β) β (Equiv.instEquivLikeEquiv.{succ u1, succ u1} (Lex.{u1} β) β))) (ofLex.{u1} β) b))
Case conversion may be inaccurate. Consider using '#align of_lex_smul ofLex_smulₓ'. -/
@[simp, to_additive]
theorem ofLex_smul [SMul α β] (a : α) (b : Lex β) : ofLex (a • b) = a • ofLex b :=
  rfl
#align of_lex_smul ofLex_smul
#align of_lex_vadd ofLex_vadd

/- warning: to_lex_smul' -> toLex_smul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u2} α β] (a : α) (b : β), Eq.{succ u2} β (SMul.smul.{u1, u2} (Lex.{u1} α) β (instSMulLex'.{u1, u2} α β _inst_1) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (Lex.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (Lex.{u1} α)) => α -> (Lex.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (Lex.{u1} α)) (toLex.{u1} α) a) b) (SMul.smul.{u1, u2} α β _inst_1 a b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SMul.{u2, u1} α β] (a : α) (b : β), Eq.{succ u1} β (HSMul.hSMul.{u2, u1, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => Lex.{u2} α) a) β β (instHSMul.{u2, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => Lex.{u2} α) a) β (instSMulLex'.{u2, u1} α β _inst_1)) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (Lex.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => Lex.{u2} α) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (Lex.{u2} α)) α (Lex.{u2} α) (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (Lex.{u2} α)) α (Lex.{u2} α) (Equiv.instEquivLikeEquiv.{succ u2, succ u2} α (Lex.{u2} α)))) (toLex.{u2} α) a) b) (HSMul.hSMul.{u2, u1, u1} α β β (instHSMul.{u2, u1} α β _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align to_lex_smul' toLex_smul'ₓ'. -/
@[simp, to_additive]
theorem toLex_smul' [SMul α β] (a : α) (b : β) : toLex a • b = a • b :=
  rfl
#align to_lex_smul' toLex_smul'
#align to_lex_vadd' toLex_vadd'

/- warning: of_lex_smul' -> ofLex_smul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u2} α β] (a : Lex.{u1} α) (b : β), Eq.{succ u2} β (SMul.smul.{u1, u2} α β _inst_1 (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Lex.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (Lex.{u1} α) α) => (Lex.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (Lex.{u1} α) α) (ofLex.{u1} α) a) b) (SMul.smul.{u1, u2} (Lex.{u1} α) β (instSMulLex'.{u1, u2} α β _inst_1) a b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SMul.{u2, u1} α β] (a : Lex.{u2} α) (b : β), Eq.{succ u1} β (HSMul.hSMul.{u2, u1, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Lex.{u2} α) => α) a) β β (instHSMul.{u2, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Lex.{u2} α) => α) a) β _inst_1) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (Lex.{u2} α) α) (Lex.{u2} α) (fun (_x : Lex.{u2} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Lex.{u2} α) => α) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (Lex.{u2} α) α) (Lex.{u2} α) α (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (Lex.{u2} α) α) (Lex.{u2} α) α (Equiv.instEquivLikeEquiv.{succ u2, succ u2} (Lex.{u2} α) α))) (ofLex.{u2} α) a) b) (HSMul.hSMul.{u2, u1, u1} (Lex.{u2} α) β β (instHSMul.{u2, u1} (Lex.{u2} α) β (instSMulLex'.{u2, u1} α β _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align of_lex_smul' ofLex_smul'ₓ'. -/
@[simp, to_additive]
theorem ofLex_smul' [SMul α β] (a : Lex α) (b : β) : ofLex a • b = a • b :=
  rfl
#align of_lex_smul' ofLex_smul'
#align of_lex_vadd' ofLex_vadd'

/- warning: to_lex_pow -> toLex_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Pow.{u1, u2} α β] (a : α) (b : β), Eq.{succ u1} (Lex.{u1} α) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (Lex.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (Lex.{u1} α)) => α -> (Lex.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (Lex.{u1} α)) (toLex.{u1} α) (HPow.hPow.{u1, u2, u1} α β α (instHPow.{u1, u2} α β _inst_1) a b)) (HPow.hPow.{u1, u2, u1} (Lex.{u1} α) β (Lex.{u1} α) (instHPow.{u1, u2} (Lex.{u1} α) β (instPowLex.{u1, u2} α β _inst_1)) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (Lex.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (Lex.{u1} α)) => α -> (Lex.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (Lex.{u1} α)) (toLex.{u1} α) a) b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Pow.{u2, u1} α β] (a : α) (b : β), Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => Lex.{u2} α) (HPow.hPow.{u2, u1, u2} α β α (instHPow.{u2, u1} α β _inst_1) a b)) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (Lex.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => Lex.{u2} α) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (Lex.{u2} α)) α (Lex.{u2} α) (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (Lex.{u2} α)) α (Lex.{u2} α) (Equiv.instEquivLikeEquiv.{succ u2, succ u2} α (Lex.{u2} α)))) (toLex.{u2} α) (HPow.hPow.{u2, u1, u2} α β α (instHPow.{u2, u1} α β _inst_1) a b)) (HPow.hPow.{u2, u1, u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => Lex.{u2} α) a) β ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => Lex.{u2} α) a) (instHPow.{u2, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => Lex.{u2} α) a) β (instPowLex.{u2, u1} α β _inst_1)) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (Lex.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => Lex.{u2} α) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (Lex.{u2} α)) α (Lex.{u2} α) (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (Lex.{u2} α)) α (Lex.{u2} α) (Equiv.instEquivLikeEquiv.{succ u2, succ u2} α (Lex.{u2} α)))) (toLex.{u2} α) a) b)
Case conversion may be inaccurate. Consider using '#align to_lex_pow toLex_powₓ'. -/
@[simp, to_additive toLex_smul, to_additive_reorder 1 4]
theorem toLex_pow [Pow α β] (a : α) (b : β) : toLex (a ^ b) = toLex a ^ b :=
  rfl
#align to_lex_pow toLex_pow
#align to_lex_smul toLex_smul

/- warning: of_lex_pow -> ofLex_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Pow.{u1, u2} α β] (a : Lex.{u1} α) (b : β), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Lex.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (Lex.{u1} α) α) => (Lex.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (Lex.{u1} α) α) (ofLex.{u1} α) (HPow.hPow.{u1, u2, u1} (Lex.{u1} α) β (Lex.{u1} α) (instHPow.{u1, u2} (Lex.{u1} α) β (instPowLex.{u1, u2} α β _inst_1)) a b)) (HPow.hPow.{u1, u2, u1} α β α (instHPow.{u1, u2} α β _inst_1) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Lex.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (Lex.{u1} α) α) => (Lex.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (Lex.{u1} α) α) (ofLex.{u1} α) a) b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Pow.{u2, u1} α β] (a : Lex.{u2} α) (b : β), Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Lex.{u2} α) => α) (HPow.hPow.{u2, u1, u2} (Lex.{u2} α) β (Lex.{u2} α) (instHPow.{u2, u1} (Lex.{u2} α) β (instPowLex.{u2, u1} α β _inst_1)) a b)) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (Lex.{u2} α) α) (Lex.{u2} α) (fun (_x : Lex.{u2} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Lex.{u2} α) => α) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (Lex.{u2} α) α) (Lex.{u2} α) α (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (Lex.{u2} α) α) (Lex.{u2} α) α (Equiv.instEquivLikeEquiv.{succ u2, succ u2} (Lex.{u2} α) α))) (ofLex.{u2} α) (HPow.hPow.{u2, u1, u2} (Lex.{u2} α) β (Lex.{u2} α) (instHPow.{u2, u1} (Lex.{u2} α) β (instPowLex.{u2, u1} α β _inst_1)) a b)) (HPow.hPow.{u2, u1, u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Lex.{u2} α) => α) a) β ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Lex.{u2} α) => α) a) (instHPow.{u2, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Lex.{u2} α) => α) a) β _inst_1) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (Lex.{u2} α) α) (Lex.{u2} α) (fun (_x : Lex.{u2} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Lex.{u2} α) => α) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (Lex.{u2} α) α) (Lex.{u2} α) α (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (Lex.{u2} α) α) (Lex.{u2} α) α (Equiv.instEquivLikeEquiv.{succ u2, succ u2} (Lex.{u2} α) α))) (ofLex.{u2} α) a) b)
Case conversion may be inaccurate. Consider using '#align of_lex_pow ofLex_powₓ'. -/
@[simp, to_additive ofLex_smul, to_additive_reorder 1 4]
theorem ofLex_pow [Pow α β] (a : Lex α) (b : β) : ofLex (a ^ b) = ofLex a ^ b :=
  rfl
#align of_lex_pow ofLex_pow
#align of_lex_smul ofLex_smul

/- warning: pow_to_lex -> pow_toLex is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Pow.{u1, u2} α β] (a : α) (b : β), Eq.{succ u1} α (HPow.hPow.{u1, u2, u1} α (Lex.{u2} β) α (instHPow.{u1, u2} α (Lex.{u2} β) (instPowLex'.{u1, u2} α β _inst_1)) a (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} β (Lex.{u2} β)) (fun (_x : Equiv.{succ u2, succ u2} β (Lex.{u2} β)) => β -> (Lex.{u2} β)) (Equiv.hasCoeToFun.{succ u2, succ u2} β (Lex.{u2} β)) (toLex.{u2} β) b)) (HPow.hPow.{u1, u2, u1} α β α (instHPow.{u1, u2} α β _inst_1) a b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Pow.{u2, u1} α β] (a : α) (b : β), Eq.{succ u2} α (HPow.hPow.{u2, u1, u2} α ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => Lex.{u1} β) b) α (instHPow.{u2, u1} α ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => Lex.{u1} β) b) (instPowLex'.{u2, u1} α β _inst_1)) a (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (Lex.{u1} β)) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => Lex.{u1} β) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (Lex.{u1} β)) β (Lex.{u1} β) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} β (Lex.{u1} β)) β (Lex.{u1} β) (Equiv.instEquivLikeEquiv.{succ u1, succ u1} β (Lex.{u1} β)))) (toLex.{u1} β) b)) (HPow.hPow.{u2, u1, u2} α β α (instHPow.{u2, u1} α β _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align pow_to_lex pow_toLexₓ'. -/
@[simp, to_additive toLex_smul, to_additive_reorder 1 4]
theorem pow_toLex [Pow α β] (a : α) (b : β) : a ^ toLex b = a ^ b :=
  rfl
#align pow_to_lex pow_toLex
#align to_lex_smul' toLex_smul'

/- warning: pow_of_lex -> pow_ofLex is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Pow.{u1, u2} α β] (a : α) (b : Lex.{u2} β), Eq.{succ u1} α (HPow.hPow.{u1, u2, u1} α β α (instHPow.{u1, u2} α β _inst_1) a (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} (Lex.{u2} β) β) (fun (_x : Equiv.{succ u2, succ u2} (Lex.{u2} β) β) => (Lex.{u2} β) -> β) (Equiv.hasCoeToFun.{succ u2, succ u2} (Lex.{u2} β) β) (ofLex.{u2} β) b)) (HPow.hPow.{u1, u2, u1} α (Lex.{u2} β) α (instHPow.{u1, u2} α (Lex.{u2} β) (instPowLex'.{u1, u2} α β _inst_1)) a b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Pow.{u2, u1} α β] (a : α) (b : Lex.{u1} β), Eq.{succ u2} α (HPow.hPow.{u2, u1, u2} α ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Lex.{u1} β) => β) b) α (instHPow.{u2, u1} α ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Lex.{u1} β) => β) b) _inst_1) a (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Lex.{u1} β) β) (Lex.{u1} β) (fun (_x : Lex.{u1} β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Lex.{u1} β) => β) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Lex.{u1} β) β) (Lex.{u1} β) β (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Lex.{u1} β) β) (Lex.{u1} β) β (Equiv.instEquivLikeEquiv.{succ u1, succ u1} (Lex.{u1} β) β))) (ofLex.{u1} β) b)) (HPow.hPow.{u2, u1, u2} α (Lex.{u1} β) α (instHPow.{u2, u1} α (Lex.{u1} β) (instPowLex'.{u2, u1} α β _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align pow_of_lex pow_ofLexₓ'. -/
@[simp, to_additive ofLex_smul, to_additive_reorder 1 4]
theorem pow_ofLex [Pow α β] (a : α) (b : Lex β) : a ^ ofLex b = a ^ b :=
  rfl
#align pow_of_lex pow_ofLex
#align of_lex_smul' ofLex_smul'

