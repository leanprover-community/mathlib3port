/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies
-/
import Mathbin.Algebra.Group.Defs
import Mathbin.Order.Synonym

/-!
# Group structure on the order type synonyms

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

@[to_additive OrderDual.hasSmul]
instance OrderDual.hasPow [h : Pow α β] : Pow αᵒᵈ β :=
  h

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

@[simp, to_additive]
theorem to_dual_one [One α] : toDual (1 : α) = 1 :=
  rfl

@[simp, to_additive]
theorem of_dual_one [One α] : (ofDual 1 : α) = 1 :=
  rfl

@[simp, to_additive]
theorem to_dual_mul [Mul α] (a b : α) : toDual (a * b) = toDual a * toDual b :=
  rfl

@[simp, to_additive]
theorem of_dual_mul [Mul α] (a b : αᵒᵈ) : ofDual (a * b) = ofDual a * ofDual b :=
  rfl

@[simp, to_additive]
theorem to_dual_inv [Inv α] (a : α) : toDual a⁻¹ = (toDual a)⁻¹ :=
  rfl

@[simp, to_additive]
theorem of_dual_inv [Inv α] (a : αᵒᵈ) : ofDual a⁻¹ = (ofDual a)⁻¹ :=
  rfl

@[simp, to_additive]
theorem to_dual_div [Div α] (a b : α) : toDual (a / b) = toDual a / toDual b :=
  rfl

@[simp, to_additive]
theorem of_dual_div [Div α] (a b : αᵒᵈ) : ofDual (a / b) = ofDual a / ofDual b :=
  rfl

theorem to_dual_vadd [HasVadd α β] (a : α) (b : β) : toDual (a +ᵥ b) = a +ᵥ toDual b :=
  rfl

theorem of_dual_vadd [HasVadd α β] (a : α) (b : βᵒᵈ) : ofDual (a +ᵥ b) = a +ᵥ ofDual b :=
  rfl

@[simp, to_additive]
theorem to_dual_smul [HasSmul α β] (a : α) (b : β) : toDual (a • b) = a • toDual b :=
  rfl

@[simp, to_additive]
theorem of_dual_smul [HasSmul α β] (a : α) (b : βᵒᵈ) : ofDual (a • b) = a • ofDual b :=
  rfl

@[simp, to_additive to_dual_smul]
theorem to_dual_pow [Pow α β] (a : α) (b : β) : toDual (a ^ b) = toDual a ^ b :=
  rfl

@[simp, to_additive of_dual_smul]
theorem of_dual_pow [Pow α β] (a : αᵒᵈ) (b : β) : ofDual (a ^ b) = ofDual a ^ b :=
  rfl

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

@[to_additive Lex.hasSmul]
instance Lex.hasPow [h : Pow α β] : Pow (Lex α) β :=
  h

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

@[simp, to_additive]
theorem to_lex_one [One α] : toLex (1 : α) = 1 :=
  rfl

@[simp, to_additive]
theorem of_lex_one [One α] : (ofLex 1 : α) = 1 :=
  rfl

@[simp, to_additive]
theorem to_lex_mul [Mul α] (a b : α) : toLex (a * b) = toLex a * toLex b :=
  rfl

@[simp, to_additive]
theorem of_lex_mul [Mul α] (a b : αᵒᵈ) : ofLex (a * b) = ofLex a * ofLex b :=
  rfl

@[simp, to_additive]
theorem to_lex_inv [Inv α] (a : α) : toLex a⁻¹ = (toLex a)⁻¹ :=
  rfl

@[simp, to_additive]
theorem of_lex_inv [Inv α] (a : αᵒᵈ) : ofLex a⁻¹ = (ofLex a)⁻¹ :=
  rfl

@[simp, to_additive]
theorem to_lex_div [Div α] (a b : α) : toLex (a / b) = toLex a / toLex b :=
  rfl

@[simp, to_additive]
theorem of_lex_div [Div α] (a b : αᵒᵈ) : ofLex (a / b) = ofLex a / ofLex b :=
  rfl

theorem to_lex_vadd [HasVadd α β] (a : α) (b : β) : toLex (a +ᵥ b) = a +ᵥ toLex b :=
  rfl

theorem of_lex_vadd [HasVadd α β] (a : α) (b : βᵒᵈ) : ofLex (a +ᵥ b) = a +ᵥ ofLex b :=
  rfl

@[simp, to_additive]
theorem to_lex_smul [HasSmul α β] (a : α) (b : β) : toLex (a • b) = a • toLex b :=
  rfl

@[simp, to_additive]
theorem of_lex_smul [HasSmul α β] (a : α) (b : βᵒᵈ) : ofLex (a • b) = a • ofLex b :=
  rfl

@[simp, to_additive to_lex_smul, to_additive_reorder 1 4]
theorem to_lex_pow [Pow α β] (a : α) (b : β) : toLex (a ^ b) = toLex a ^ b :=
  rfl

@[simp, to_additive of_lex_smul, to_additive_reorder 1 4]
theorem of_lex_pow [Pow α β] (a : αᵒᵈ) (b : β) : ofLex (a ^ b) = ofLex a ^ b :=
  rfl

