/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies
-/
import Mathbin.Algebra.Group.Defs
import Mathbin.Order.Synonym

/-!
# Group structure on the order type synonyms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/651
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
instance [h : HasSmul α β] : HasSmul α βᵒᵈ :=
  h

/- warning: order_dual.has_smul' -> OrderDual.hasSmul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [h : HasSmul.{u_1, u_2} α β], HasSmul.{u_1, u_2} (OrderDual.{u_1} α) β
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [h : SMul.{u_1, u_2} α β], SMul.{u_1, u_2} (OrderDual.{u_1} α) β
Case conversion may be inaccurate. Consider using '#align order_dual.has_smul' OrderDual.hasSmul'ₓ'. -/
@[to_additive]
instance OrderDual.hasSmul' [h : HasSmul α β] : HasSmul αᵒᵈ β :=
  h
#align order_dual.has_smul' OrderDual.hasSmul'

#print OrderDual.hasPow /-
@[to_additive OrderDual.hasSmul]
instance OrderDual.hasPow [h : Pow α β] : Pow αᵒᵈ β :=
  h
#align order_dual.has_pow OrderDual.hasPow
-/

#print OrderDual.hasPow' /-
@[to_additive OrderDual.hasSmul']
instance OrderDual.hasPow' [h : Pow α β] : Pow α βᵒᵈ :=
  h
#align order_dual.has_pow' OrderDual.hasPow'
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
instance [h : HasInvolutiveInv α] : HasInvolutiveInv αᵒᵈ :=
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
-/

#print ofDual_one /-
@[simp, to_additive]
theorem ofDual_one [One α] : (ofDual 1 : α) = 1 :=
  rfl
#align of_dual_one ofDual_one
-/

#print toDual_mul /-
@[simp, to_additive]
theorem toDual_mul [Mul α] (a b : α) : toDual (a * b) = toDual a * toDual b :=
  rfl
#align to_dual_mul toDual_mul
-/

#print ofDual_mul /-
@[simp, to_additive]
theorem ofDual_mul [Mul α] (a b : αᵒᵈ) : ofDual (a * b) = ofDual a * ofDual b :=
  rfl
#align of_dual_mul ofDual_mul
-/

#print toDual_inv /-
@[simp, to_additive]
theorem toDual_inv [Inv α] (a : α) : toDual a⁻¹ = (toDual a)⁻¹ :=
  rfl
#align to_dual_inv toDual_inv
-/

#print ofDual_inv /-
@[simp, to_additive]
theorem ofDual_inv [Inv α] (a : αᵒᵈ) : ofDual a⁻¹ = (ofDual a)⁻¹ :=
  rfl
#align of_dual_inv ofDual_inv
-/

#print toDual_div /-
@[simp, to_additive]
theorem toDual_div [Div α] (a b : α) : toDual (a / b) = toDual a / toDual b :=
  rfl
#align to_dual_div toDual_div
-/

#print ofDual_div /-
@[simp, to_additive]
theorem ofDual_div [Div α] (a b : αᵒᵈ) : ofDual (a / b) = ofDual a / ofDual b :=
  rfl
#align of_dual_div ofDual_div
-/

/- warning: to_dual_smul -> toDual_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : HasSmul.{u_1, u_2} α β] (a : α) (b : β), Eq.{succ u_2} (OrderDual.{u_2} β) (coeFn.{max 1 (succ u_2), succ u_2} (Equiv.{succ u_2, succ u_2} β (OrderDual.{u_2} β)) (fun (_x : Equiv.{succ u_2, succ u_2} β (OrderDual.{u_2} β)) => β -> (OrderDual.{u_2} β)) (Equiv.hasCoeToFun.{succ u_2, succ u_2} β (OrderDual.{u_2} β)) (OrderDual.toDual.{u_2} β) (HasSmul.smul.{u_1, u_2} α β _inst_1 a b)) (HasSmul.smul.{u_1, u_2} α (OrderDual.{u_2} β) (OrderDual.hasSmul.{u_1, u_2} α β _inst_1) a (coeFn.{max 1 (succ u_2), succ u_2} (Equiv.{succ u_2, succ u_2} β (OrderDual.{u_2} β)) (fun (_x : Equiv.{succ u_2, succ u_2} β (OrderDual.{u_2} β)) => β -> (OrderDual.{u_2} β)) (Equiv.hasCoeToFun.{succ u_2, succ u_2} β (OrderDual.{u_2} β)) (OrderDual.toDual.{u_2} β) b))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.515 : SMul.{u_1, u_2} α β] (a : α) (b : β), Eq.{succ u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : β) => OrderDual.{u_2} β) (HSMul.hSMul.{u_1, u_2, u_2} α β β (instHSMul.{u_1, u_2} α β inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.515) a b)) (FunLike.coe.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} β (OrderDual.{u_2} β)) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : β) => OrderDual.{u_2} β) a) (EmbeddingLike.toFunLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} β (OrderDual.{u_2} β)) β (OrderDual.{u_2} β) (EquivLike.toEmbeddingLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} β (OrderDual.{u_2} β)) β (OrderDual.{u_2} β) (Equiv.instEquivLikeEquiv.{succ u_2, succ u_2} β (OrderDual.{u_2} β)))) (OrderDual.toDual.{u_2} β) (HSMul.hSMul.{u_1, u_2, u_2} α β β (instHSMul.{u_1, u_2} α β inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.515) a b)) (HSMul.hSMul.{u_1, u_2, u_2} α ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : β) => OrderDual.{u_2} β) b) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : β) => OrderDual.{u_2} β) b) (instHSMul.{u_1, u_2} α ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : β) => OrderDual.{u_2} β) b) (instSMulOrderDual.{u_1, u_2} α β inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.515)) a (FunLike.coe.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} β (OrderDual.{u_2} β)) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : β) => OrderDual.{u_2} β) a) (EmbeddingLike.toFunLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} β (OrderDual.{u_2} β)) β (OrderDual.{u_2} β) (EquivLike.toEmbeddingLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} β (OrderDual.{u_2} β)) β (OrderDual.{u_2} β) (Equiv.instEquivLikeEquiv.{succ u_2, succ u_2} β (OrderDual.{u_2} β)))) (OrderDual.toDual.{u_2} β) b))
Case conversion may be inaccurate. Consider using '#align to_dual_smul toDual_smulₓ'. -/
@[simp, to_additive]
theorem toDual_smul [HasSmul α β] (a : α) (b : β) : toDual (a • b) = a • toDual b :=
  rfl
#align to_dual_smul toDual_smul

/- warning: of_dual_smul -> ofDual_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : HasSmul.{u_1, u_2} α β] (a : α) (b : OrderDual.{u_2} β), Eq.{succ u_2} β (coeFn.{max 1 (succ u_2), succ u_2} (Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) (fun (_x : Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) => (OrderDual.{u_2} β) -> β) (Equiv.hasCoeToFun.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) (OrderDual.ofDual.{u_2} β) (HasSmul.smul.{u_1, u_2} α (OrderDual.{u_2} β) (OrderDual.hasSmul.{u_1, u_2} α β _inst_1) a b)) (HasSmul.smul.{u_1, u_2} α β _inst_1 a (coeFn.{max 1 (succ u_2), succ u_2} (Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) (fun (_x : Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) => (OrderDual.{u_2} β) -> β) (Equiv.hasCoeToFun.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) (OrderDual.ofDual.{u_2} β) b))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.544 : SMul.{u_1, u_2} α β] (a : α) (b : OrderDual.{u_2} β), Eq.{succ u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : OrderDual.{u_2} β) => β) (HSMul.hSMul.{u_1, u_2, u_2} α (OrderDual.{u_2} β) (OrderDual.{u_2} β) (instHSMul.{u_1, u_2} α (OrderDual.{u_2} β) (instSMulOrderDual.{u_1, u_2} α β inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.544)) a b)) (FunLike.coe.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) (OrderDual.{u_2} β) (fun (a : OrderDual.{u_2} β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : OrderDual.{u_2} β) => β) a) (EmbeddingLike.toFunLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) (OrderDual.{u_2} β) β (EquivLike.toEmbeddingLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) (OrderDual.{u_2} β) β (Equiv.instEquivLikeEquiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β))) (OrderDual.ofDual.{u_2} β) (HSMul.hSMul.{u_1, u_2, u_2} α (OrderDual.{u_2} β) (OrderDual.{u_2} β) (instHSMul.{u_1, u_2} α (OrderDual.{u_2} β) (instSMulOrderDual.{u_1, u_2} α β inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.544)) a b)) (HSMul.hSMul.{u_1, u_2, u_2} α ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : OrderDual.{u_2} β) => β) b) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : OrderDual.{u_2} β) => β) b) (instHSMul.{u_1, u_2} α ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : OrderDual.{u_2} β) => β) b) inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.544) a (FunLike.coe.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) (OrderDual.{u_2} β) (fun (a : OrderDual.{u_2} β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : OrderDual.{u_2} β) => β) a) (EmbeddingLike.toFunLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) (OrderDual.{u_2} β) β (EquivLike.toEmbeddingLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) (OrderDual.{u_2} β) β (Equiv.instEquivLikeEquiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β))) (OrderDual.ofDual.{u_2} β) b))
Case conversion may be inaccurate. Consider using '#align of_dual_smul ofDual_smulₓ'. -/
@[simp, to_additive]
theorem ofDual_smul [HasSmul α β] (a : α) (b : βᵒᵈ) : ofDual (a • b) = a • ofDual b :=
  rfl
#align of_dual_smul ofDual_smul

/- warning: to_dual_smul' -> toDual_smul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : HasSmul.{u_1, u_2} α β] (a : α) (b : β), Eq.{succ u_2} β (HasSmul.smul.{u_1, u_2} (OrderDual.{u_1} α) β (OrderDual.hasSmul'.{u_1, u_2} α β _inst_1) (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} α (OrderDual.{u_1} α)) (fun (_x : Equiv.{succ u_1, succ u_1} α (OrderDual.{u_1} α)) => α -> (OrderDual.{u_1} α)) (Equiv.hasCoeToFun.{succ u_1, succ u_1} α (OrderDual.{u_1} α)) (OrderDual.toDual.{u_1} α) a) b) (HasSmul.smul.{u_1, u_2} α β _inst_1 a b)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.576 : SMul.{u_1, u_2} α β] (a : α) (b : β), Eq.{succ u_2} β (HSMul.hSMul.{u_1, u_2, u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => OrderDual.{u_1} α) a) β β (instHSMul.{u_1, u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => OrderDual.{u_1} α) a) β (OrderDual.hasSmul'.{u_1, u_2} α β inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.576)) (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} α (OrderDual.{u_1} α)) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => OrderDual.{u_1} α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} α (OrderDual.{u_1} α)) α (OrderDual.{u_1} α) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} α (OrderDual.{u_1} α)) α (OrderDual.{u_1} α) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} α (OrderDual.{u_1} α)))) (OrderDual.toDual.{u_1} α) a) b) (HSMul.hSMul.{u_1, u_2, u_2} α β β (instHSMul.{u_1, u_2} α β inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.576) a b)
Case conversion may be inaccurate. Consider using '#align to_dual_smul' toDual_smul'ₓ'. -/
@[simp, to_additive]
theorem toDual_smul' [HasSmul α β] (a : α) (b : β) : toDual a • b = a • b :=
  rfl
#align to_dual_smul' toDual_smul'

/- warning: of_dual_smul' -> ofDual_smul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : HasSmul.{u_1, u_2} α β] (a : OrderDual.{u_1} α) (b : β), Eq.{succ u_2} β (HasSmul.smul.{u_1, u_2} α β _inst_1 (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (OrderDual.{u_1} α) α) (fun (_x : Equiv.{succ u_1, succ u_1} (OrderDual.{u_1} α) α) => (OrderDual.{u_1} α) -> α) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (OrderDual.{u_1} α) α) (OrderDual.ofDual.{u_1} α) a) b) (HasSmul.smul.{u_1, u_2} (OrderDual.{u_1} α) β (OrderDual.hasSmul'.{u_1, u_2} α β _inst_1) a b)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.603 : SMul.{u_1, u_2} α β] (a : OrderDual.{u_1} α) (b : β), Eq.{succ u_2} β (HSMul.hSMul.{u_1, u_2, u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : OrderDual.{u_1} α) => α) a) β β (instHSMul.{u_1, u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : OrderDual.{u_1} α) => α) a) β inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.603) (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (OrderDual.{u_1} α) α) (OrderDual.{u_1} α) (fun (a : OrderDual.{u_1} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : OrderDual.{u_1} α) => α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (OrderDual.{u_1} α) α) (OrderDual.{u_1} α) α (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (OrderDual.{u_1} α) α) (OrderDual.{u_1} α) α (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (OrderDual.{u_1} α) α))) (OrderDual.ofDual.{u_1} α) a) b) (HSMul.hSMul.{u_1, u_2, u_2} (OrderDual.{u_1} α) β β (instHSMul.{u_1, u_2} (OrderDual.{u_1} α) β (OrderDual.hasSmul'.{u_1, u_2} α β inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.603)) a b)
Case conversion may be inaccurate. Consider using '#align of_dual_smul' ofDual_smul'ₓ'. -/
@[simp, to_additive]
theorem ofDual_smul' [HasSmul α β] (a : αᵒᵈ) (b : β) : ofDual a • b = a • b :=
  rfl
#align of_dual_smul' ofDual_smul'

/- warning: to_dual_pow -> toDual_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Pow.{u_1, u_2} α β] (a : α) (b : β), Eq.{succ u_1} (OrderDual.{u_1} α) (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} α (OrderDual.{u_1} α)) (fun (_x : Equiv.{succ u_1, succ u_1} α (OrderDual.{u_1} α)) => α -> (OrderDual.{u_1} α)) (Equiv.hasCoeToFun.{succ u_1, succ u_1} α (OrderDual.{u_1} α)) (OrderDual.toDual.{u_1} α) (HPow.hPow.{u_1, u_2, u_1} α β α (instHPow.{u_1, u_2} α β _inst_1) a b)) (HPow.hPow.{u_1, u_2, u_1} (OrderDual.{u_1} α) β (OrderDual.{u_1} α) (instHPow.{u_1, u_2} (OrderDual.{u_1} α) β (OrderDual.hasPow.{u_1, u_2} α β _inst_1)) (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} α (OrderDual.{u_1} α)) (fun (_x : Equiv.{succ u_1, succ u_1} α (OrderDual.{u_1} α)) => α -> (OrderDual.{u_1} α)) (Equiv.hasCoeToFun.{succ u_1, succ u_1} α (OrderDual.{u_1} α)) (OrderDual.toDual.{u_1} α) a) b)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.633 : Pow.{u_1, u_2} α β] (a : α) (b : β), Eq.{succ u_1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => OrderDual.{u_1} α) (HPow.hPow.{u_1, u_2, u_1} α β α (instHPow.{u_1, u_2} α β inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.633) a b)) (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} α (OrderDual.{u_1} α)) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => OrderDual.{u_1} α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} α (OrderDual.{u_1} α)) α (OrderDual.{u_1} α) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} α (OrderDual.{u_1} α)) α (OrderDual.{u_1} α) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} α (OrderDual.{u_1} α)))) (OrderDual.toDual.{u_1} α) (HPow.hPow.{u_1, u_2, u_1} α β α (instHPow.{u_1, u_2} α β inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.633) a b)) (HPow.hPow.{u_1, u_2, u_1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => OrderDual.{u_1} α) a) β ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => OrderDual.{u_1} α) a) (instHPow.{u_1, u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => OrderDual.{u_1} α) a) β (OrderDual.hasPow.{u_1, u_2} α β inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.633)) (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} α (OrderDual.{u_1} α)) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => OrderDual.{u_1} α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} α (OrderDual.{u_1} α)) α (OrderDual.{u_1} α) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} α (OrderDual.{u_1} α)) α (OrderDual.{u_1} α) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} α (OrderDual.{u_1} α)))) (OrderDual.toDual.{u_1} α) a) b)
Case conversion may be inaccurate. Consider using '#align to_dual_pow toDual_powₓ'. -/
@[simp, to_additive toDual_smul, to_additive_reorder 1 4]
theorem toDual_pow [Pow α β] (a : α) (b : β) : toDual (a ^ b) = toDual a ^ b :=
  rfl
#align to_dual_pow toDual_pow

/- warning: of_dual_pow -> ofDual_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Pow.{u_1, u_2} α β] (a : OrderDual.{u_1} α) (b : β), Eq.{succ u_1} α (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (OrderDual.{u_1} α) α) (fun (_x : Equiv.{succ u_1, succ u_1} (OrderDual.{u_1} α) α) => (OrderDual.{u_1} α) -> α) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (OrderDual.{u_1} α) α) (OrderDual.ofDual.{u_1} α) (HPow.hPow.{u_1, u_2, u_1} (OrderDual.{u_1} α) β (OrderDual.{u_1} α) (instHPow.{u_1, u_2} (OrderDual.{u_1} α) β (OrderDual.hasPow.{u_1, u_2} α β _inst_1)) a b)) (HPow.hPow.{u_1, u_2, u_1} α β α (instHPow.{u_1, u_2} α β _inst_1) (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (OrderDual.{u_1} α) α) (fun (_x : Equiv.{succ u_1, succ u_1} (OrderDual.{u_1} α) α) => (OrderDual.{u_1} α) -> α) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (OrderDual.{u_1} α) α) (OrderDual.ofDual.{u_1} α) a) b)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.659 : Pow.{u_1, u_2} α β] (a : OrderDual.{u_1} α) (b : β), Eq.{succ u_1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : OrderDual.{u_1} α) => α) (HPow.hPow.{u_1, u_2, u_1} (OrderDual.{u_1} α) β (OrderDual.{u_1} α) (instHPow.{u_1, u_2} (OrderDual.{u_1} α) β (OrderDual.hasPow.{u_1, u_2} α β inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.659)) a b)) (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (OrderDual.{u_1} α) α) (OrderDual.{u_1} α) (fun (a : OrderDual.{u_1} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : OrderDual.{u_1} α) => α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (OrderDual.{u_1} α) α) (OrderDual.{u_1} α) α (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (OrderDual.{u_1} α) α) (OrderDual.{u_1} α) α (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (OrderDual.{u_1} α) α))) (OrderDual.ofDual.{u_1} α) (HPow.hPow.{u_1, u_2, u_1} (OrderDual.{u_1} α) β (OrderDual.{u_1} α) (instHPow.{u_1, u_2} (OrderDual.{u_1} α) β (OrderDual.hasPow.{u_1, u_2} α β inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.659)) a b)) (HPow.hPow.{u_1, u_2, u_1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : OrderDual.{u_1} α) => α) a) β ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : OrderDual.{u_1} α) => α) a) (instHPow.{u_1, u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : OrderDual.{u_1} α) => α) a) β inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.659) (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (OrderDual.{u_1} α) α) (OrderDual.{u_1} α) (fun (a : OrderDual.{u_1} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : OrderDual.{u_1} α) => α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (OrderDual.{u_1} α) α) (OrderDual.{u_1} α) α (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (OrderDual.{u_1} α) α) (OrderDual.{u_1} α) α (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (OrderDual.{u_1} α) α))) (OrderDual.ofDual.{u_1} α) a) b)
Case conversion may be inaccurate. Consider using '#align of_dual_pow ofDual_powₓ'. -/
@[simp, to_additive ofDual_smul, to_additive_reorder 1 4]
theorem ofDual_pow [Pow α β] (a : αᵒᵈ) (b : β) : ofDual (a ^ b) = ofDual a ^ b :=
  rfl
#align of_dual_pow ofDual_pow

/- warning: pow_to_dual -> pow_toDual is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Pow.{u_1, u_2} α β] (a : α) (b : β), Eq.{succ u_1} α (HPow.hPow.{u_1, u_2, u_1} α (OrderDual.{u_2} β) α (instHPow.{u_1, u_2} α (OrderDual.{u_2} β) (OrderDual.hasPow'.{u_1, u_2} α β _inst_1)) a (coeFn.{max 1 (succ u_2), succ u_2} (Equiv.{succ u_2, succ u_2} β (OrderDual.{u_2} β)) (fun (_x : Equiv.{succ u_2, succ u_2} β (OrderDual.{u_2} β)) => β -> (OrderDual.{u_2} β)) (Equiv.hasCoeToFun.{succ u_2, succ u_2} β (OrderDual.{u_2} β)) (OrderDual.toDual.{u_2} β) b)) (HPow.hPow.{u_1, u_2, u_1} α β α (instHPow.{u_1, u_2} α β _inst_1) a b)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.688 : Pow.{u_1, u_2} α β] (a : α) (b : β), Eq.{succ u_1} α (HPow.hPow.{u_1, u_2, u_1} α ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : β) => OrderDual.{u_2} β) b) α (instHPow.{u_1, u_2} α ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : β) => OrderDual.{u_2} β) b) (OrderDual.hasPow'.{u_1, u_2} α β inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.688)) a (FunLike.coe.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} β (OrderDual.{u_2} β)) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : β) => OrderDual.{u_2} β) a) (EmbeddingLike.toFunLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} β (OrderDual.{u_2} β)) β (OrderDual.{u_2} β) (EquivLike.toEmbeddingLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} β (OrderDual.{u_2} β)) β (OrderDual.{u_2} β) (Equiv.instEquivLikeEquiv.{succ u_2, succ u_2} β (OrderDual.{u_2} β)))) (OrderDual.toDual.{u_2} β) b)) (HPow.hPow.{u_1, u_2, u_1} α β α (instHPow.{u_1, u_2} α β inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.688) a b)
Case conversion may be inaccurate. Consider using '#align pow_to_dual pow_toDualₓ'. -/
@[simp, to_additive toDual_smul', to_additive_reorder 1 4]
theorem pow_toDual [Pow α β] (a : α) (b : β) : a ^ toDual b = a ^ b :=
  rfl
#align pow_to_dual pow_toDual

/- warning: pow_of_dual -> pow_ofDual is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Pow.{u_1, u_2} α β] (a : α) (b : OrderDual.{u_2} β), Eq.{succ u_1} α (HPow.hPow.{u_1, u_2, u_1} α β α (instHPow.{u_1, u_2} α β _inst_1) a (coeFn.{max 1 (succ u_2), succ u_2} (Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) (fun (_x : Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) => (OrderDual.{u_2} β) -> β) (Equiv.hasCoeToFun.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) (OrderDual.ofDual.{u_2} β) b)) (HPow.hPow.{u_1, u_2, u_1} α (OrderDual.{u_2} β) α (instHPow.{u_1, u_2} α (OrderDual.{u_2} β) (OrderDual.hasPow'.{u_1, u_2} α β _inst_1)) a b)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.709 : Pow.{u_1, u_2} α β] (a : α) (b : OrderDual.{u_2} β), Eq.{succ u_1} α (HPow.hPow.{u_1, u_2, u_1} α ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : OrderDual.{u_2} β) => β) b) α (instHPow.{u_1, u_2} α ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : OrderDual.{u_2} β) => β) b) inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.709) a (FunLike.coe.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) (OrderDual.{u_2} β) (fun (a : OrderDual.{u_2} β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : OrderDual.{u_2} β) => β) a) (EmbeddingLike.toFunLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) (OrderDual.{u_2} β) β (EquivLike.toEmbeddingLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β) (OrderDual.{u_2} β) β (Equiv.instEquivLikeEquiv.{succ u_2, succ u_2} (OrderDual.{u_2} β) β))) (OrderDual.ofDual.{u_2} β) b)) (HPow.hPow.{u_1, u_2, u_1} α (OrderDual.{u_2} β) α (instHPow.{u_1, u_2} α (OrderDual.{u_2} β) (OrderDual.hasPow'.{u_1, u_2} α β inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.709)) a b)
Case conversion may be inaccurate. Consider using '#align pow_of_dual pow_ofDualₓ'. -/
@[simp, to_additive ofDual_smul', to_additive_reorder 1 4]
theorem pow_ofDual [Pow α β] (a : α) (b : βᵒᵈ) : a ^ ofDual b = a ^ b :=
  rfl
#align pow_of_dual pow_ofDual

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
instance [h : HasSmul α β] : HasSmul α (Lex β) :=
  h

/- warning: lex.has_smul' -> Lex.hasSmul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [h : HasSmul.{u_1, u_2} α β], HasSmul.{u_1, u_2} (Lex.{u_1} α) β
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [h : SMul.{u_1, u_2} α β], SMul.{u_1, u_2} (Lex.{u_1} α) β
Case conversion may be inaccurate. Consider using '#align lex.has_smul' Lex.hasSmul'ₓ'. -/
@[to_additive]
instance Lex.hasSmul' [h : HasSmul α β] : HasSmul (Lex α) β :=
  h
#align lex.has_smul' Lex.hasSmul'

#print Lex.hasPow /-
@[to_additive Lex.hasSmul]
instance Lex.hasPow [h : Pow α β] : Pow (Lex α) β :=
  h
#align lex.has_pow Lex.hasPow
-/

#print Lex.hasPow' /-
@[to_additive Lex.hasSmul']
instance Lex.hasPow' [h : Pow α β] : Pow α (Lex β) :=
  h
#align lex.has_pow' Lex.hasPow'
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
instance [h : HasInvolutiveInv α] : HasInvolutiveInv (Lex α) :=
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
-/

#print ofLex_one /-
@[simp, to_additive]
theorem ofLex_one [One α] : (ofLex 1 : α) = 1 :=
  rfl
#align of_lex_one ofLex_one
-/

#print toLex_mul /-
@[simp, to_additive]
theorem toLex_mul [Mul α] (a b : α) : toLex (a * b) = toLex a * toLex b :=
  rfl
#align to_lex_mul toLex_mul
-/

#print ofLex_mul /-
@[simp, to_additive]
theorem ofLex_mul [Mul α] (a b : Lex α) : ofLex (a * b) = ofLex a * ofLex b :=
  rfl
#align of_lex_mul ofLex_mul
-/

#print toLex_inv /-
@[simp, to_additive]
theorem toLex_inv [Inv α] (a : α) : toLex a⁻¹ = (toLex a)⁻¹ :=
  rfl
#align to_lex_inv toLex_inv
-/

#print ofLex_inv /-
@[simp, to_additive]
theorem ofLex_inv [Inv α] (a : Lex α) : ofLex a⁻¹ = (ofLex a)⁻¹ :=
  rfl
#align of_lex_inv ofLex_inv
-/

#print toLex_div /-
@[simp, to_additive]
theorem toLex_div [Div α] (a b : α) : toLex (a / b) = toLex a / toLex b :=
  rfl
#align to_lex_div toLex_div
-/

#print ofLex_div /-
@[simp, to_additive]
theorem ofLex_div [Div α] (a b : Lex α) : ofLex (a / b) = ofLex a / ofLex b :=
  rfl
#align of_lex_div ofLex_div
-/

/- warning: to_lex_smul -> toLex_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : HasSmul.{u_1, u_2} α β] (a : α) (b : β), Eq.{succ u_2} (Lex.{u_2} β) (coeFn.{max 1 (succ u_2), succ u_2} (Equiv.{succ u_2, succ u_2} β (Lex.{u_2} β)) (fun (_x : Equiv.{succ u_2, succ u_2} β (Lex.{u_2} β)) => β -> (Lex.{u_2} β)) (Equiv.hasCoeToFun.{succ u_2, succ u_2} β (Lex.{u_2} β)) (toLex.{u_2} β) (HasSmul.smul.{u_1, u_2} α β _inst_1 a b)) (HasSmul.smul.{u_1, u_2} α (Lex.{u_2} β) (Lex.hasSmul.{u_1, u_2} α β _inst_1) a (coeFn.{max 1 (succ u_2), succ u_2} (Equiv.{succ u_2, succ u_2} β (Lex.{u_2} β)) (fun (_x : Equiv.{succ u_2, succ u_2} β (Lex.{u_2} β)) => β -> (Lex.{u_2} β)) (Equiv.hasCoeToFun.{succ u_2, succ u_2} β (Lex.{u_2} β)) (toLex.{u_2} β) b))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.1226 : SMul.{u_1, u_2} α β] (a : α) (b : β), Eq.{succ u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : β) => Lex.{u_2} β) (HSMul.hSMul.{u_1, u_2, u_2} α β β (instHSMul.{u_1, u_2} α β inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.1226) a b)) (FunLike.coe.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} β (Lex.{u_2} β)) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : β) => Lex.{u_2} β) a) (EmbeddingLike.toFunLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} β (Lex.{u_2} β)) β (Lex.{u_2} β) (EquivLike.toEmbeddingLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} β (Lex.{u_2} β)) β (Lex.{u_2} β) (Equiv.instEquivLikeEquiv.{succ u_2, succ u_2} β (Lex.{u_2} β)))) (toLex.{u_2} β) (HSMul.hSMul.{u_1, u_2, u_2} α β β (instHSMul.{u_1, u_2} α β inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.1226) a b)) (HSMul.hSMul.{u_1, u_2, u_2} α ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : β) => Lex.{u_2} β) b) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : β) => Lex.{u_2} β) b) (instHSMul.{u_1, u_2} α ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : β) => Lex.{u_2} β) b) (instSMulLex.{u_1, u_2} α β inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.1226)) a (FunLike.coe.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} β (Lex.{u_2} β)) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : β) => Lex.{u_2} β) a) (EmbeddingLike.toFunLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} β (Lex.{u_2} β)) β (Lex.{u_2} β) (EquivLike.toEmbeddingLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} β (Lex.{u_2} β)) β (Lex.{u_2} β) (Equiv.instEquivLikeEquiv.{succ u_2, succ u_2} β (Lex.{u_2} β)))) (toLex.{u_2} β) b))
Case conversion may be inaccurate. Consider using '#align to_lex_smul toLex_smulₓ'. -/
@[simp, to_additive]
theorem toLex_smul [HasSmul α β] (a : α) (b : β) : toLex (a • b) = a • toLex b :=
  rfl
#align to_lex_smul toLex_smul

/- warning: of_lex_smul -> ofLex_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : HasSmul.{u_1, u_2} α β] (a : α) (b : Lex.{u_2} β), Eq.{succ u_2} β (coeFn.{max 1 (succ u_2), succ u_2} (Equiv.{succ u_2, succ u_2} (Lex.{u_2} β) β) (fun (_x : Equiv.{succ u_2, succ u_2} (Lex.{u_2} β) β) => (Lex.{u_2} β) -> β) (Equiv.hasCoeToFun.{succ u_2, succ u_2} (Lex.{u_2} β) β) (ofLex.{u_2} β) (HasSmul.smul.{u_1, u_2} α (Lex.{u_2} β) (Lex.hasSmul.{u_1, u_2} α β _inst_1) a b)) (HasSmul.smul.{u_1, u_2} α β _inst_1 a (coeFn.{max 1 (succ u_2), succ u_2} (Equiv.{succ u_2, succ u_2} (Lex.{u_2} β) β) (fun (_x : Equiv.{succ u_2, succ u_2} (Lex.{u_2} β) β) => (Lex.{u_2} β) -> β) (Equiv.hasCoeToFun.{succ u_2, succ u_2} (Lex.{u_2} β) β) (ofLex.{u_2} β) b))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.1255 : SMul.{u_1, u_2} α β] (a : α) (b : Lex.{u_2} β), Eq.{succ u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : Lex.{u_2} β) => β) (HSMul.hSMul.{u_1, u_2, u_2} α (Lex.{u_2} β) (Lex.{u_2} β) (instHSMul.{u_1, u_2} α (Lex.{u_2} β) (instSMulLex.{u_1, u_2} α β inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.1255)) a b)) (FunLike.coe.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (Lex.{u_2} β) β) (Lex.{u_2} β) (fun (a : Lex.{u_2} β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : Lex.{u_2} β) => β) a) (EmbeddingLike.toFunLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (Lex.{u_2} β) β) (Lex.{u_2} β) β (EquivLike.toEmbeddingLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (Lex.{u_2} β) β) (Lex.{u_2} β) β (Equiv.instEquivLikeEquiv.{succ u_2, succ u_2} (Lex.{u_2} β) β))) (ofLex.{u_2} β) (HSMul.hSMul.{u_1, u_2, u_2} α (Lex.{u_2} β) (Lex.{u_2} β) (instHSMul.{u_1, u_2} α (Lex.{u_2} β) (instSMulLex.{u_1, u_2} α β inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.1255)) a b)) (HSMul.hSMul.{u_1, u_2, u_2} α ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : Lex.{u_2} β) => β) b) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : Lex.{u_2} β) => β) b) (instHSMul.{u_1, u_2} α ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : Lex.{u_2} β) => β) b) inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.1255) a (FunLike.coe.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (Lex.{u_2} β) β) (Lex.{u_2} β) (fun (a : Lex.{u_2} β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : Lex.{u_2} β) => β) a) (EmbeddingLike.toFunLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (Lex.{u_2} β) β) (Lex.{u_2} β) β (EquivLike.toEmbeddingLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (Lex.{u_2} β) β) (Lex.{u_2} β) β (Equiv.instEquivLikeEquiv.{succ u_2, succ u_2} (Lex.{u_2} β) β))) (ofLex.{u_2} β) b))
Case conversion may be inaccurate. Consider using '#align of_lex_smul ofLex_smulₓ'. -/
@[simp, to_additive]
theorem ofLex_smul [HasSmul α β] (a : α) (b : Lex β) : ofLex (a • b) = a • ofLex b :=
  rfl
#align of_lex_smul ofLex_smul

/- warning: to_lex_smul' -> toLex_smul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : HasSmul.{u_1, u_2} α β] (a : α) (b : β), Eq.{succ u_2} β (HasSmul.smul.{u_1, u_2} (Lex.{u_1} α) β (Lex.hasSmul'.{u_1, u_2} α β _inst_1) (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} α (Lex.{u_1} α)) (fun (_x : Equiv.{succ u_1, succ u_1} α (Lex.{u_1} α)) => α -> (Lex.{u_1} α)) (Equiv.hasCoeToFun.{succ u_1, succ u_1} α (Lex.{u_1} α)) (toLex.{u_1} α) a) b) (HasSmul.smul.{u_1, u_2} α β _inst_1 a b)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.1285 : SMul.{u_1, u_2} α β] (a : α) (b : β), Eq.{succ u_2} β (HSMul.hSMul.{u_1, u_2, u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => Lex.{u_1} α) a) β β (instHSMul.{u_1, u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => Lex.{u_1} α) a) β (Lex.hasSmul'.{u_1, u_2} α β inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.1285)) (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} α (Lex.{u_1} α)) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => Lex.{u_1} α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} α (Lex.{u_1} α)) α (Lex.{u_1} α) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} α (Lex.{u_1} α)) α (Lex.{u_1} α) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} α (Lex.{u_1} α)))) (toLex.{u_1} α) a) b) (HSMul.hSMul.{u_1, u_2, u_2} α β β (instHSMul.{u_1, u_2} α β inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.1285) a b)
Case conversion may be inaccurate. Consider using '#align to_lex_smul' toLex_smul'ₓ'. -/
@[simp, to_additive]
theorem toLex_smul' [HasSmul α β] (a : α) (b : β) : toLex a • b = a • b :=
  rfl
#align to_lex_smul' toLex_smul'

/- warning: of_lex_smul' -> ofLex_smul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : HasSmul.{u_1, u_2} α β] (a : Lex.{u_1} α) (b : β), Eq.{succ u_2} β (HasSmul.smul.{u_1, u_2} α β _inst_1 (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (Lex.{u_1} α) α) (fun (_x : Equiv.{succ u_1, succ u_1} (Lex.{u_1} α) α) => (Lex.{u_1} α) -> α) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (Lex.{u_1} α) α) (ofLex.{u_1} α) a) b) (HasSmul.smul.{u_1, u_2} (Lex.{u_1} α) β (Lex.hasSmul'.{u_1, u_2} α β _inst_1) a b)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.1312 : SMul.{u_1, u_2} α β] (a : Lex.{u_1} α) (b : β), Eq.{succ u_2} β (HSMul.hSMul.{u_1, u_2, u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : Lex.{u_1} α) => α) a) β β (instHSMul.{u_1, u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : Lex.{u_1} α) => α) a) β inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.1312) (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (Lex.{u_1} α) α) (Lex.{u_1} α) (fun (a : Lex.{u_1} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : Lex.{u_1} α) => α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (Lex.{u_1} α) α) (Lex.{u_1} α) α (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (Lex.{u_1} α) α) (Lex.{u_1} α) α (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (Lex.{u_1} α) α))) (ofLex.{u_1} α) a) b) (HSMul.hSMul.{u_1, u_2, u_2} (Lex.{u_1} α) β β (instHSMul.{u_1, u_2} (Lex.{u_1} α) β (Lex.hasSmul'.{u_1, u_2} α β inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.1312)) a b)
Case conversion may be inaccurate. Consider using '#align of_lex_smul' ofLex_smul'ₓ'. -/
@[simp, to_additive]
theorem ofLex_smul' [HasSmul α β] (a : Lex α) (b : β) : ofLex a • b = a • b :=
  rfl
#align of_lex_smul' ofLex_smul'

/- warning: to_lex_pow -> toLex_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Pow.{u_1, u_2} α β] (a : α) (b : β), Eq.{succ u_1} (Lex.{u_1} α) (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} α (Lex.{u_1} α)) (fun (_x : Equiv.{succ u_1, succ u_1} α (Lex.{u_1} α)) => α -> (Lex.{u_1} α)) (Equiv.hasCoeToFun.{succ u_1, succ u_1} α (Lex.{u_1} α)) (toLex.{u_1} α) (HPow.hPow.{u_1, u_2, u_1} α β α (instHPow.{u_1, u_2} α β _inst_1) a b)) (HPow.hPow.{u_1, u_2, u_1} (Lex.{u_1} α) β (Lex.{u_1} α) (instHPow.{u_1, u_2} (Lex.{u_1} α) β (Lex.hasPow.{u_1, u_2} α β _inst_1)) (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} α (Lex.{u_1} α)) (fun (_x : Equiv.{succ u_1, succ u_1} α (Lex.{u_1} α)) => α -> (Lex.{u_1} α)) (Equiv.hasCoeToFun.{succ u_1, succ u_1} α (Lex.{u_1} α)) (toLex.{u_1} α) a) b)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.1340 : Pow.{u_1, u_2} α β] (a : α) (b : β), Eq.{succ u_1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => Lex.{u_1} α) (HPow.hPow.{u_1, u_2, u_1} α β α (instHPow.{u_1, u_2} α β inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.1340) a b)) (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} α (Lex.{u_1} α)) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => Lex.{u_1} α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} α (Lex.{u_1} α)) α (Lex.{u_1} α) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} α (Lex.{u_1} α)) α (Lex.{u_1} α) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} α (Lex.{u_1} α)))) (toLex.{u_1} α) (HPow.hPow.{u_1, u_2, u_1} α β α (instHPow.{u_1, u_2} α β inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.1340) a b)) (HPow.hPow.{u_1, u_2, u_1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => Lex.{u_1} α) a) β ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => Lex.{u_1} α) a) (instHPow.{u_1, u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => Lex.{u_1} α) a) β (Lex.hasPow.{u_1, u_2} α β inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.1340)) (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} α (Lex.{u_1} α)) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : α) => Lex.{u_1} α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} α (Lex.{u_1} α)) α (Lex.{u_1} α) (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} α (Lex.{u_1} α)) α (Lex.{u_1} α) (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} α (Lex.{u_1} α)))) (toLex.{u_1} α) a) b)
Case conversion may be inaccurate. Consider using '#align to_lex_pow toLex_powₓ'. -/
@[simp, to_additive toLex_smul, to_additive_reorder 1 4]
theorem toLex_pow [Pow α β] (a : α) (b : β) : toLex (a ^ b) = toLex a ^ b :=
  rfl
#align to_lex_pow toLex_pow

/- warning: of_lex_pow -> ofLex_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Pow.{u_1, u_2} α β] (a : Lex.{u_1} α) (b : β), Eq.{succ u_1} α (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (Lex.{u_1} α) α) (fun (_x : Equiv.{succ u_1, succ u_1} (Lex.{u_1} α) α) => (Lex.{u_1} α) -> α) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (Lex.{u_1} α) α) (ofLex.{u_1} α) (HPow.hPow.{u_1, u_2, u_1} (Lex.{u_1} α) β (Lex.{u_1} α) (instHPow.{u_1, u_2} (Lex.{u_1} α) β (Lex.hasPow.{u_1, u_2} α β _inst_1)) a b)) (HPow.hPow.{u_1, u_2, u_1} α β α (instHPow.{u_1, u_2} α β _inst_1) (coeFn.{max 1 (succ u_1), succ u_1} (Equiv.{succ u_1, succ u_1} (Lex.{u_1} α) α) (fun (_x : Equiv.{succ u_1, succ u_1} (Lex.{u_1} α) α) => (Lex.{u_1} α) -> α) (Equiv.hasCoeToFun.{succ u_1, succ u_1} (Lex.{u_1} α) α) (ofLex.{u_1} α) a) b)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.1366 : Pow.{u_1, u_2} α β] (a : Lex.{u_1} α) (b : β), Eq.{succ u_1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : Lex.{u_1} α) => α) (HPow.hPow.{u_1, u_2, u_1} (Lex.{u_1} α) β (Lex.{u_1} α) (instHPow.{u_1, u_2} (Lex.{u_1} α) β (Lex.hasPow.{u_1, u_2} α β inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.1366)) a b)) (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (Lex.{u_1} α) α) (Lex.{u_1} α) (fun (a : Lex.{u_1} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : Lex.{u_1} α) => α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (Lex.{u_1} α) α) (Lex.{u_1} α) α (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (Lex.{u_1} α) α) (Lex.{u_1} α) α (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (Lex.{u_1} α) α))) (ofLex.{u_1} α) (HPow.hPow.{u_1, u_2, u_1} (Lex.{u_1} α) β (Lex.{u_1} α) (instHPow.{u_1, u_2} (Lex.{u_1} α) β (Lex.hasPow.{u_1, u_2} α β inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.1366)) a b)) (HPow.hPow.{u_1, u_2, u_1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : Lex.{u_1} α) => α) a) β ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : Lex.{u_1} α) => α) a) (instHPow.{u_1, u_2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : Lex.{u_1} α) => α) a) β inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.1366) (FunLike.coe.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (Lex.{u_1} α) α) (Lex.{u_1} α) (fun (a : Lex.{u_1} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : Lex.{u_1} α) => α) a) (EmbeddingLike.toFunLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (Lex.{u_1} α) α) (Lex.{u_1} α) α (EquivLike.toEmbeddingLike.{succ u_1, succ u_1, succ u_1} (Equiv.{succ u_1, succ u_1} (Lex.{u_1} α) α) (Lex.{u_1} α) α (Equiv.instEquivLikeEquiv.{succ u_1, succ u_1} (Lex.{u_1} α) α))) (ofLex.{u_1} α) a) b)
Case conversion may be inaccurate. Consider using '#align of_lex_pow ofLex_powₓ'. -/
@[simp, to_additive ofLex_smul, to_additive_reorder 1 4]
theorem ofLex_pow [Pow α β] (a : Lex α) (b : β) : ofLex (a ^ b) = ofLex a ^ b :=
  rfl
#align of_lex_pow ofLex_pow

/- warning: pow_to_lex -> pow_toLex is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Pow.{u_1, u_2} α β] (a : α) (b : β), Eq.{succ u_1} α (HPow.hPow.{u_1, u_2, u_1} α (Lex.{u_2} β) α (instHPow.{u_1, u_2} α (Lex.{u_2} β) (Lex.hasPow'.{u_1, u_2} α β _inst_1)) a (coeFn.{max 1 (succ u_2), succ u_2} (Equiv.{succ u_2, succ u_2} β (Lex.{u_2} β)) (fun (_x : Equiv.{succ u_2, succ u_2} β (Lex.{u_2} β)) => β -> (Lex.{u_2} β)) (Equiv.hasCoeToFun.{succ u_2, succ u_2} β (Lex.{u_2} β)) (toLex.{u_2} β) b)) (HPow.hPow.{u_1, u_2, u_1} α β α (instHPow.{u_1, u_2} α β _inst_1) a b)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.1393 : Pow.{u_1, u_2} α β] (a : α) (b : β), Eq.{succ u_1} α (HPow.hPow.{u_1, u_2, u_1} α ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : β) => Lex.{u_2} β) b) α (instHPow.{u_1, u_2} α ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : β) => Lex.{u_2} β) b) (Lex.hasPow'.{u_1, u_2} α β inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.1393)) a (FunLike.coe.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} β (Lex.{u_2} β)) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : β) => Lex.{u_2} β) a) (EmbeddingLike.toFunLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} β (Lex.{u_2} β)) β (Lex.{u_2} β) (EquivLike.toEmbeddingLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} β (Lex.{u_2} β)) β (Lex.{u_2} β) (Equiv.instEquivLikeEquiv.{succ u_2, succ u_2} β (Lex.{u_2} β)))) (toLex.{u_2} β) b)) (HPow.hPow.{u_1, u_2, u_1} α β α (instHPow.{u_1, u_2} α β inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.1393) a b)
Case conversion may be inaccurate. Consider using '#align pow_to_lex pow_toLexₓ'. -/
@[simp, to_additive toLex_smul, to_additive_reorder 1 4]
theorem pow_toLex [Pow α β] (a : α) (b : β) : a ^ toLex b = a ^ b :=
  rfl
#align pow_to_lex pow_toLex

/- warning: pow_of_lex -> pow_ofLex is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Pow.{u_1, u_2} α β] (a : α) (b : Lex.{u_2} β), Eq.{succ u_1} α (HPow.hPow.{u_1, u_2, u_1} α β α (instHPow.{u_1, u_2} α β _inst_1) a (coeFn.{max 1 (succ u_2), succ u_2} (Equiv.{succ u_2, succ u_2} (Lex.{u_2} β) β) (fun (_x : Equiv.{succ u_2, succ u_2} (Lex.{u_2} β) β) => (Lex.{u_2} β) -> β) (Equiv.hasCoeToFun.{succ u_2, succ u_2} (Lex.{u_2} β) β) (ofLex.{u_2} β) b)) (HPow.hPow.{u_1, u_2, u_1} α (Lex.{u_2} β) α (instHPow.{u_1, u_2} α (Lex.{u_2} β) (Lex.hasPow'.{u_1, u_2} α β _inst_1)) a b)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.1414 : Pow.{u_1, u_2} α β] (a : α) (b : Lex.{u_2} β), Eq.{succ u_1} α (HPow.hPow.{u_1, u_2, u_1} α ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : Lex.{u_2} β) => β) b) α (instHPow.{u_1, u_2} α ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : Lex.{u_2} β) => β) b) inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.1414) a (FunLike.coe.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (Lex.{u_2} β) β) (Lex.{u_2} β) (fun (a : Lex.{u_2} β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.21 : Lex.{u_2} β) => β) a) (EmbeddingLike.toFunLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (Lex.{u_2} β) β) (Lex.{u_2} β) β (EquivLike.toEmbeddingLike.{succ u_2, succ u_2, succ u_2} (Equiv.{succ u_2, succ u_2} (Lex.{u_2} β) β) (Lex.{u_2} β) β (Equiv.instEquivLikeEquiv.{succ u_2, succ u_2} (Lex.{u_2} β) β))) (ofLex.{u_2} β) b)) (HPow.hPow.{u_1, u_2, u_1} α (Lex.{u_2} β) α (instHPow.{u_1, u_2} α (Lex.{u_2} β) (Lex.hasPow'.{u_1, u_2} α β inst._@.Mathlib.Algebra.Group.OrderSynonym._hyg.1414)) a b)
Case conversion may be inaccurate. Consider using '#align pow_of_lex pow_ofLexₓ'. -/
@[simp, to_additive ofLex_smul, to_additive_reorder 1 4]
theorem pow_ofLex [Pow α β] (a : α) (b : Lex β) : a ^ ofLex b = a ^ b :=
  rfl
#align pow_of_lex pow_ofLex

