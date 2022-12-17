/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

! This file was ported from Lean 3 source module algebra.opposites
! leanprover-community/mathlib commit 706d88f2b8fdfeb0b22796433d7a6c1a010af9f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.Defs
import Mathbin.Logic.Equiv.Defs
import Mathbin.Logic.Nontrivial

/-!
# Multiplicative opposite and algebraic operations on it

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/644
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define `mul_opposite α = αᵐᵒᵖ` to be the multiplicative opposite of `α`. It inherits
all additive algebraic structures on `α` (in other files), and reverses the order of multipliers in
multiplicative structures, i.e., `op (x * y) = op y * op x`, where `mul_opposite.op` is the
canonical map from `α` to `αᵐᵒᵖ`.

We also define `add_opposite α = αᵃᵒᵖ` to be the additive opposite of `α`. It inherits all
multiplicative algebraic structures on `α` (in other files), and reverses the order of summands in
additive structures, i.e. `op (x + y) = op y + op x`, where `add_opposite.op` is the canonical map
from `α` to `αᵃᵒᵖ`.

## Notation

* `αᵐᵒᵖ = mul_opposite α`
* `αᵃᵒᵖ = add_opposite α`

## Tags

multiplicative opposite, additive opposite
-/


universe u v

open Function

#print MulOpposite /-
/-- Multiplicative opposite of a type. This type inherits all additive structures on `α` and
reverses left and right in multiplication.-/
@[to_additive
      "Additive opposite of a type. This type inherits all multiplicative structures on\n`α` and reverses left and right in addition."]
def MulOpposite (α : Type u) : Type u :=
  α
#align mul_opposite MulOpposite
-/

-- mathport name: «expr ᵐᵒᵖ»
postfix:max "ᵐᵒᵖ" => MulOpposite

-- mathport name: «expr ᵃᵒᵖ»
postfix:max "ᵃᵒᵖ" => AddOpposite

variable {α : Type u}

namespace MulOpposite

#print MulOpposite.op /-
/-- The element of `mul_opposite α` that represents `x : α`. -/
@[pp_nodot, to_additive "The element of `αᵃᵒᵖ` that represents `x : α`."]
def op : α → αᵐᵒᵖ :=
  id
#align mul_opposite.op MulOpposite.op
-/

#print MulOpposite.unop /-
/-- The element of `α` represented by `x : αᵐᵒᵖ`. -/
@[pp_nodot, to_additive "The element of `α` represented by `x : αᵃᵒᵖ`."]
def unop : αᵐᵒᵖ → α :=
  id
#align mul_opposite.unop MulOpposite.unop
-/

attribute [pp_nodot] AddOpposite.op AddOpposite.unop

#print MulOpposite.unop_op /-
@[simp, to_additive]
theorem unop_op (x : α) : unop (op x) = x :=
  rfl
#align mul_opposite.unop_op MulOpposite.unop_op
-/

#print MulOpposite.op_unop /-
@[simp, to_additive]
theorem op_unop (x : αᵐᵒᵖ) : op (unop x) = x :=
  rfl
#align mul_opposite.op_unop MulOpposite.op_unop
-/

#print MulOpposite.op_comp_unop /-
@[simp, to_additive]
theorem op_comp_unop : (op : α → αᵐᵒᵖ) ∘ unop = id :=
  rfl
#align mul_opposite.op_comp_unop MulOpposite.op_comp_unop
-/

#print MulOpposite.unop_comp_op /-
@[simp, to_additive]
theorem unop_comp_op : (unop : αᵐᵒᵖ → α) ∘ op = id :=
  rfl
#align mul_opposite.unop_comp_op MulOpposite.unop_comp_op
-/

/- warning: mul_opposite.rec -> MulOpposite.rec is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {F : (MulOpposite.{u1} α) -> Sort.{u2}}, (forall (X : α), F (MulOpposite.op.{u1} α X)) -> (forall (X : MulOpposite.{u1} α), F X)
but is expected to have type
  forall {α : Type.{u2}} {F : (MulOpposite.{u2} α) -> Sort.{u1}}, (forall (X : α), F (MulOpposite.op.{u2} α X)) -> (forall (X : MulOpposite.{u2} α), F X)
Case conversion may be inaccurate. Consider using '#align mul_opposite.rec MulOpposite.recₓ'. -/
/-- A recursor for `mul_opposite`. Use as `induction x using mul_opposite.rec`. -/
@[simp, to_additive "A recursor for `add_opposite`. Use as `induction x using add_opposite.rec`."]
protected def rec {F : ∀ X : αᵐᵒᵖ, Sort v} (h : ∀ X, F (op X)) : ∀ X, F X := fun X => h (unop X)
#align mul_opposite.rec MulOpposite.rec

#print MulOpposite.opEquiv /-
/-- The canonical bijection between `α` and `αᵐᵒᵖ`. -/
@[to_additive "The canonical bijection between `α` and `αᵃᵒᵖ`.",
  simps (config := { fullyApplied := false }) apply symmApply]
def opEquiv : α ≃ αᵐᵒᵖ :=
  ⟨op, unop, unop_op, op_unop⟩
#align mul_opposite.op_equiv MulOpposite.opEquiv
-/

#print MulOpposite.op_bijective /-
@[to_additive]
theorem op_bijective : Bijective (op : α → αᵐᵒᵖ) :=
  opEquiv.Bijective
#align mul_opposite.op_bijective MulOpposite.op_bijective
-/

#print MulOpposite.unop_bijective /-
@[to_additive]
theorem unop_bijective : Bijective (unop : αᵐᵒᵖ → α) :=
  opEquiv.symm.Bijective
#align mul_opposite.unop_bijective MulOpposite.unop_bijective
-/

#print MulOpposite.op_injective /-
@[to_additive]
theorem op_injective : Injective (op : α → αᵐᵒᵖ) :=
  op_bijective.Injective
#align mul_opposite.op_injective MulOpposite.op_injective
-/

#print MulOpposite.op_surjective /-
@[to_additive]
theorem op_surjective : Surjective (op : α → αᵐᵒᵖ) :=
  op_bijective.Surjective
#align mul_opposite.op_surjective MulOpposite.op_surjective
-/

#print MulOpposite.unop_injective /-
@[to_additive]
theorem unop_injective : Injective (unop : αᵐᵒᵖ → α) :=
  unop_bijective.Injective
#align mul_opposite.unop_injective MulOpposite.unop_injective
-/

#print MulOpposite.unop_surjective /-
@[to_additive]
theorem unop_surjective : Surjective (unop : αᵐᵒᵖ → α) :=
  unop_bijective.Surjective
#align mul_opposite.unop_surjective MulOpposite.unop_surjective
-/

#print MulOpposite.op_inj /-
@[simp, to_additive]
theorem op_inj {x y : α} : op x = op y ↔ x = y :=
  op_injective.eq_iff
#align mul_opposite.op_inj MulOpposite.op_inj
-/

#print MulOpposite.unop_inj /-
@[simp, to_additive]
theorem unop_inj {x y : αᵐᵒᵖ} : unop x = unop y ↔ x = y :=
  unop_injective.eq_iff
#align mul_opposite.unop_inj MulOpposite.unop_inj
-/

variable (α)

@[to_additive]
instance [Nontrivial α] : Nontrivial αᵐᵒᵖ :=
  op_injective.Nontrivial

@[to_additive]
instance [Inhabited α] : Inhabited αᵐᵒᵖ :=
  ⟨op default⟩

@[to_additive]
instance [Subsingleton α] : Subsingleton αᵐᵒᵖ :=
  unop_injective.Subsingleton

@[to_additive]
instance [Unique α] : Unique αᵐᵒᵖ :=
  Unique.mk' _

@[to_additive]
instance [IsEmpty α] : IsEmpty αᵐᵒᵖ :=
  Function.isEmpty unop

instance [Zero α] : Zero αᵐᵒᵖ where zero := op 0

@[to_additive]
instance [One α] : One αᵐᵒᵖ where one := op 1

instance [Add α] : Add αᵐᵒᵖ where add x y := op (unop x + unop y)

instance [Sub α] : Sub αᵐᵒᵖ where sub x y := op (unop x - unop y)

instance [Neg α] : Neg αᵐᵒᵖ where neg x := op <| -unop x

instance [InvolutiveNeg α] : InvolutiveNeg αᵐᵒᵖ :=
  { MulOpposite.hasNeg α with neg_neg := fun a => unop_injective <| neg_neg _ }

@[to_additive]
instance [Mul α] : Mul αᵐᵒᵖ where mul x y := op (unop y * unop x)

@[to_additive]
instance [Inv α] : Inv αᵐᵒᵖ where inv x := op <| (unop x)⁻¹

@[to_additive]
instance [InvolutiveInv α] : InvolutiveInv αᵐᵒᵖ :=
  { MulOpposite.hasInv α with inv_inv := fun a => unop_injective <| inv_inv _ }

@[to_additive]
instance (R : Type _) [HasSmul R α] : HasSmul R αᵐᵒᵖ where smul c x := op (c • unop x)

section

variable (α)

#print MulOpposite.op_zero /-
@[simp]
theorem op_zero [Zero α] : op (0 : α) = 0 :=
  rfl
#align mul_opposite.op_zero MulOpposite.op_zero
-/

#print MulOpposite.unop_zero /-
@[simp]
theorem unop_zero [Zero α] : unop (0 : αᵐᵒᵖ) = 0 :=
  rfl
#align mul_opposite.unop_zero MulOpposite.unop_zero
-/

#print MulOpposite.op_one /-
@[simp, to_additive]
theorem op_one [One α] : op (1 : α) = 1 :=
  rfl
#align mul_opposite.op_one MulOpposite.op_one
-/

#print MulOpposite.unop_one /-
@[simp, to_additive]
theorem unop_one [One α] : unop (1 : αᵐᵒᵖ) = 1 :=
  rfl
#align mul_opposite.unop_one MulOpposite.unop_one
-/

variable {α}

#print MulOpposite.op_add /-
@[simp]
theorem op_add [Add α] (x y : α) : op (x + y) = op x + op y :=
  rfl
#align mul_opposite.op_add MulOpposite.op_add
-/

#print MulOpposite.unop_add /-
@[simp]
theorem unop_add [Add α] (x y : αᵐᵒᵖ) : unop (x + y) = unop x + unop y :=
  rfl
#align mul_opposite.unop_add MulOpposite.unop_add
-/

#print MulOpposite.op_neg /-
@[simp]
theorem op_neg [Neg α] (x : α) : op (-x) = -op x :=
  rfl
#align mul_opposite.op_neg MulOpposite.op_neg
-/

#print MulOpposite.unop_neg /-
@[simp]
theorem unop_neg [Neg α] (x : αᵐᵒᵖ) : unop (-x) = -unop x :=
  rfl
#align mul_opposite.unop_neg MulOpposite.unop_neg
-/

#print MulOpposite.op_mul /-
@[simp, to_additive]
theorem op_mul [Mul α] (x y : α) : op (x * y) = op y * op x :=
  rfl
#align mul_opposite.op_mul MulOpposite.op_mul
-/

#print MulOpposite.unop_mul /-
@[simp, to_additive]
theorem unop_mul [Mul α] (x y : αᵐᵒᵖ) : unop (x * y) = unop y * unop x :=
  rfl
#align mul_opposite.unop_mul MulOpposite.unop_mul
-/

#print MulOpposite.op_inv /-
@[simp, to_additive]
theorem op_inv [Inv α] (x : α) : op x⁻¹ = (op x)⁻¹ :=
  rfl
#align mul_opposite.op_inv MulOpposite.op_inv
-/

#print MulOpposite.unop_inv /-
@[simp, to_additive]
theorem unop_inv [Inv α] (x : αᵐᵒᵖ) : unop x⁻¹ = (unop x)⁻¹ :=
  rfl
#align mul_opposite.unop_inv MulOpposite.unop_inv
-/

#print MulOpposite.op_sub /-
@[simp]
theorem op_sub [Sub α] (x y : α) : op (x - y) = op x - op y :=
  rfl
#align mul_opposite.op_sub MulOpposite.op_sub
-/

#print MulOpposite.unop_sub /-
@[simp]
theorem unop_sub [Sub α] (x y : αᵐᵒᵖ) : unop (x - y) = unop x - unop y :=
  rfl
#align mul_opposite.unop_sub MulOpposite.unop_sub
-/

/- warning: mul_opposite.op_smul -> MulOpposite.op_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : HasSmul.{u2, u1} R α] (c : R) (a : α), Eq.{succ u1} (MulOpposite.{u1} α) (MulOpposite.op.{u1} α (HasSmul.smul.{u2, u1} R α _inst_1 c a)) (HasSmul.smul.{u2, u1} R (MulOpposite.{u1} α) (MulOpposite.hasSmul.{u1, u2} α R _inst_1) c (MulOpposite.op.{u1} α a))
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : SMul.{u2, u1} R α] (c : R) (a : α), Eq.{succ u1} (MulOpposite.{u1} α) (MulOpposite.op.{u1} α (HSMul.hSMul.{u2, u1, u1} R α α (instHSMul.{u2, u1} R α _inst_1) c a)) (HSMul.hSMul.{u2, u1, u1} R (MulOpposite.{u1} α) (MulOpposite.{u1} α) (instHSMul.{u2, u1} R (MulOpposite.{u1} α) (MulOpposite.instSMulMulOpposite.{u1, u2} α R _inst_1)) c (MulOpposite.op.{u1} α a))
Case conversion may be inaccurate. Consider using '#align mul_opposite.op_smul MulOpposite.op_smulₓ'. -/
@[simp, to_additive]
theorem op_smul {R : Type _} [HasSmul R α] (c : R) (a : α) : op (c • a) = c • op a :=
  rfl
#align mul_opposite.op_smul MulOpposite.op_smul

/- warning: mul_opposite.unop_smul -> MulOpposite.unop_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : HasSmul.{u2, u1} R α] (c : R) (a : MulOpposite.{u1} α), Eq.{succ u1} α (MulOpposite.unop.{u1} α (HasSmul.smul.{u2, u1} R (MulOpposite.{u1} α) (MulOpposite.hasSmul.{u1, u2} α R _inst_1) c a)) (HasSmul.smul.{u2, u1} R α _inst_1 c (MulOpposite.unop.{u1} α a))
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : SMul.{u2, u1} R α] (c : R) (a : MulOpposite.{u1} α), Eq.{succ u1} α (MulOpposite.unop.{u1} α (HSMul.hSMul.{u2, u1, u1} R (MulOpposite.{u1} α) (MulOpposite.{u1} α) (instHSMul.{u2, u1} R (MulOpposite.{u1} α) (MulOpposite.instSMulMulOpposite.{u1, u2} α R _inst_1)) c a)) (HSMul.hSMul.{u2, u1, u1} R α α (instHSMul.{u2, u1} R α _inst_1) c (MulOpposite.unop.{u1} α a))
Case conversion may be inaccurate. Consider using '#align mul_opposite.unop_smul MulOpposite.unop_smulₓ'. -/
@[simp, to_additive]
theorem unop_smul {R : Type _} [HasSmul R α] (c : R) (a : αᵐᵒᵖ) : unop (c • a) = c • unop a :=
  rfl
#align mul_opposite.unop_smul MulOpposite.unop_smul

end

variable {α}

#print MulOpposite.unop_eq_zero_iff /-
@[simp]
theorem unop_eq_zero_iff [Zero α] (a : αᵐᵒᵖ) : a.unop = (0 : α) ↔ a = (0 : αᵐᵒᵖ) :=
  unop_injective.eq_iff' rfl
#align mul_opposite.unop_eq_zero_iff MulOpposite.unop_eq_zero_iff
-/

#print MulOpposite.op_eq_zero_iff /-
@[simp]
theorem op_eq_zero_iff [Zero α] (a : α) : op a = (0 : αᵐᵒᵖ) ↔ a = (0 : α) :=
  op_injective.eq_iff' rfl
#align mul_opposite.op_eq_zero_iff MulOpposite.op_eq_zero_iff
-/

#print MulOpposite.unop_ne_zero_iff /-
theorem unop_ne_zero_iff [Zero α] (a : αᵐᵒᵖ) : a.unop ≠ (0 : α) ↔ a ≠ (0 : αᵐᵒᵖ) :=
  not_congr <| unop_eq_zero_iff a
#align mul_opposite.unop_ne_zero_iff MulOpposite.unop_ne_zero_iff
-/

#print MulOpposite.op_ne_zero_iff /-
theorem op_ne_zero_iff [Zero α] (a : α) : op a ≠ (0 : αᵐᵒᵖ) ↔ a ≠ (0 : α) :=
  not_congr <| op_eq_zero_iff a
#align mul_opposite.op_ne_zero_iff MulOpposite.op_ne_zero_iff
-/

#print MulOpposite.unop_eq_one_iff /-
@[simp, to_additive]
theorem unop_eq_one_iff [One α] (a : αᵐᵒᵖ) : a.unop = 1 ↔ a = 1 :=
  unop_injective.eq_iff' rfl
#align mul_opposite.unop_eq_one_iff MulOpposite.unop_eq_one_iff
-/

#print MulOpposite.op_eq_one_iff /-
@[simp, to_additive]
theorem op_eq_one_iff [One α] (a : α) : op a = 1 ↔ a = 1 :=
  op_injective.eq_iff' rfl
#align mul_opposite.op_eq_one_iff MulOpposite.op_eq_one_iff
-/

end MulOpposite

namespace AddOpposite

instance [One α] : One αᵃᵒᵖ where one := op 1

#print AddOpposite.op_one /-
@[simp]
theorem op_one [One α] : op (1 : α) = 1 :=
  rfl
#align add_opposite.op_one AddOpposite.op_one
-/

#print AddOpposite.unop_one /-
@[simp]
theorem unop_one [One α] : unop 1 = (1 : α) :=
  rfl
#align add_opposite.unop_one AddOpposite.unop_one
-/

#print AddOpposite.op_eq_one_iff /-
@[simp]
theorem op_eq_one_iff [One α] {a : α} : op a = 1 ↔ a = 1 :=
  op_injective.eq_iff' op_one
#align add_opposite.op_eq_one_iff AddOpposite.op_eq_one_iff
-/

#print AddOpposite.unop_eq_one_iff /-
@[simp]
theorem unop_eq_one_iff [One α] {a : αᵃᵒᵖ} : unop a = 1 ↔ a = 1 :=
  unop_injective.eq_iff' unop_one
#align add_opposite.unop_eq_one_iff AddOpposite.unop_eq_one_iff
-/

instance [Mul α] : Mul αᵃᵒᵖ where mul a b := op (unop a * unop b)

#print AddOpposite.op_mul /-
@[simp]
theorem op_mul [Mul α] (a b : α) : op (a * b) = op a * op b :=
  rfl
#align add_opposite.op_mul AddOpposite.op_mul
-/

#print AddOpposite.unop_mul /-
@[simp]
theorem unop_mul [Mul α] (a b : αᵃᵒᵖ) : unop (a * b) = unop a * unop b :=
  rfl
#align add_opposite.unop_mul AddOpposite.unop_mul
-/

instance [Inv α] : Inv αᵃᵒᵖ where inv a := op (unop a)⁻¹

instance [InvolutiveInv α] : InvolutiveInv αᵃᵒᵖ :=
  { AddOpposite.hasInv with inv_inv := fun a => unop_injective <| inv_inv _ }

#print AddOpposite.op_inv /-
@[simp]
theorem op_inv [Inv α] (a : α) : op a⁻¹ = (op a)⁻¹ :=
  rfl
#align add_opposite.op_inv AddOpposite.op_inv
-/

#print AddOpposite.unop_inv /-
@[simp]
theorem unop_inv [Inv α] (a : αᵃᵒᵖ) : unop a⁻¹ = (unop a)⁻¹ :=
  rfl
#align add_opposite.unop_inv AddOpposite.unop_inv
-/

instance [Div α] : Div αᵃᵒᵖ where div a b := op (unop a / unop b)

#print AddOpposite.op_div /-
@[simp]
theorem op_div [Div α] (a b : α) : op (a / b) = op a / op b :=
  rfl
#align add_opposite.op_div AddOpposite.op_div
-/

#print AddOpposite.unop_div /-
@[simp]
theorem unop_div [Div α] (a b : αᵃᵒᵖ) : unop (a / b) = unop a / unop b :=
  rfl
#align add_opposite.unop_div AddOpposite.unop_div
-/

end AddOpposite

