/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland

! This file was ported from Lean 3 source module algebra.ring.defs
! leanprover-community/mathlib commit 861a26926586cd46ff80264d121cdb6fa0e35cc1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.Basic
import Mathbin.Algebra.GroupWithZero.Defs
import Mathbin.Data.Int.Cast.Defs

/-!
# Semirings and rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines semirings, rings and domains. This is analogous to `algebra.group.defs` and
`algebra.group.basic`, the difference being that the former is about `+` and `*` separately, while
the present file is about their interaction.

## Main definitions

* `distrib`: Typeclass for distributivity of multiplication over addition.
* `has_distrib_neg`: Typeclass for commutativity of negation and multiplication. This is useful when
  dealing with multiplicative submonoids which are closed under negation without being closed under
  addition, for example `units`.
* `(non_unital_)(non_assoc_)(semi)ring`: Typeclasses for possibly non-unital or non-associative
  rings and semirings. Some combinations are not defined yet because they haven't found use.

## Tags

`semiring`, `comm_semiring`, `ring`, `comm_ring`, `domain`, `is_domain`, `nonzero`, `units`
-/


universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {R : Type x}

open Function

/-!
### `distrib` class
-/


#print Distrib /-
/-- A typeclass stating that multiplication is left and right distributive
over addition. -/
@[protect_proj]
class Distrib (R : Type _) extends Mul R, Add R where
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c
#align distrib Distrib
-/

#print LeftDistribClass /-
/-- A typeclass stating that multiplication is left distributive over addition. -/
@[protect_proj]
class LeftDistribClass (R : Type _) [Mul R] [Add R] where
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
#align left_distrib_class LeftDistribClass
-/

#print RightDistribClass /-
/-- A typeclass stating that multiplication is right distributive over addition. -/
@[protect_proj]
class RightDistribClass (R : Type _) [Mul R] [Add R] where
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c
#align right_distrib_class RightDistribClass
-/

/- warning: distrib.left_distrib_class -> Distrib.leftDistribClass is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : Distrib.{u1} R], LeftDistribClass.{u1} R (Distrib.toHasMul.{u1} R _inst_1) (Distrib.toHasAdd.{u1} R _inst_1)
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : Distrib.{u1} R], LeftDistribClass.{u1} R (Distrib.toMul.{u1} R _inst_1) (Distrib.toAdd.{u1} R _inst_1)
Case conversion may be inaccurate. Consider using '#align distrib.left_distrib_class Distrib.leftDistribClassₓ'. -/
-- see Note [lower instance priority]
instance (priority := 100) Distrib.leftDistribClass (R : Type _) [Distrib R] : LeftDistribClass R :=
  ⟨Distrib.left_distrib⟩
#align distrib.left_distrib_class Distrib.leftDistribClass

/- warning: distrib.right_distrib_class -> Distrib.rightDistribClass is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : Distrib.{u1} R], RightDistribClass.{u1} R (Distrib.toHasMul.{u1} R _inst_1) (Distrib.toHasAdd.{u1} R _inst_1)
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : Distrib.{u1} R], RightDistribClass.{u1} R (Distrib.toMul.{u1} R _inst_1) (Distrib.toAdd.{u1} R _inst_1)
Case conversion may be inaccurate. Consider using '#align distrib.right_distrib_class Distrib.rightDistribClassₓ'. -/
-- see Note [lower instance priority]
instance (priority := 100) Distrib.rightDistribClass (R : Type _) [Distrib R] :
    RightDistribClass R :=
  ⟨Distrib.right_distrib⟩
#align distrib.right_distrib_class Distrib.rightDistribClass

#print left_distrib /-
theorem left_distrib [Mul R] [Add R] [LeftDistribClass R] (a b c : R) :
    a * (b + c) = a * b + a * c :=
  LeftDistribClass.left_distrib a b c
#align left_distrib left_distrib
-/

alias left_distrib ← mul_add
#align mul_add mul_add

#print right_distrib /-
theorem right_distrib [Mul R] [Add R] [RightDistribClass R] (a b c : R) :
    (a + b) * c = a * c + b * c :=
  RightDistribClass.right_distrib a b c
#align right_distrib right_distrib
-/

alias right_distrib ← add_mul
#align add_mul add_mul

#print distrib_three_right /-
theorem distrib_three_right [Mul R] [Add R] [RightDistribClass R] (a b c d : R) :
    (a + b + c) * d = a * d + b * d + c * d := by simp [right_distrib]
#align distrib_three_right distrib_three_right
-/

/-!
### Semirings
-/


#print NonUnitalNonAssocSemiring /-
/-- A not-necessarily-unital, not-necessarily-associative semiring. -/
@[protect_proj]
class NonUnitalNonAssocSemiring (α : Type u) extends AddCommMonoid α, Distrib α, MulZeroClass α
#align non_unital_non_assoc_semiring NonUnitalNonAssocSemiring
-/

#print NonUnitalSemiring /-
/-- An associative but not-necessarily unital semiring. -/
@[protect_proj]
class NonUnitalSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, SemigroupWithZero α
#align non_unital_semiring NonUnitalSemiring
-/

#print NonAssocSemiring /-
/-- A unital but not-necessarily-associative semiring. -/
@[protect_proj]
class NonAssocSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, MulZeroOneClass α,
  AddCommMonoidWithOne α
#align non_assoc_semiring NonAssocSemiring
-/

#print Semiring /-
/-- A semiring is a type with the following structures: additive commutative monoid
(`add_comm_monoid`), multiplicative monoid (`monoid`), distributive laws (`distrib`), and
multiplication by zero law (`mul_zero_class`). The actual definition extends `monoid_with_zero`
instead of `monoid` and `mul_zero_class`. -/
@[protect_proj]
class Semiring (α : Type u) extends NonUnitalSemiring α, NonAssocSemiring α, MonoidWithZero α
#align semiring Semiring
-/

section HasOneHasAdd

variable [One α] [Add α]

/- warning: one_add_one_eq_two -> one_add_one_eq_two is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : One.{u1} α] [_inst_2 : Add.{u1} α], Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 2 (OfNat.mk.{u1} α 2 (bit0.{u1} α _inst_2 (One.one.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} α], Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (AddMonoidWithOne.toOne.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (AddMonoidWithOne.toOne.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 2 (instOfNat.{u1} α 2 (AddMonoidWithOne.toNatCast.{u1} α _inst_1) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))
Case conversion may be inaccurate. Consider using '#align one_add_one_eq_two one_add_one_eq_twoₓ'. -/
theorem one_add_one_eq_two : 1 + 1 = (2 : α) :=
  rfl
#align one_add_one_eq_two one_add_one_eq_two

end HasOneHasAdd

section DistribMulOneClass

variable [Add α] [MulOneClass α]

/- warning: add_one_mul -> add_one_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] [_inst_2 : MulOneClass.{u1} α] [_inst_3 : RightDistribClass.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2) _inst_1] (a : α) (b : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_2))))) b) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2)) a b) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] [_inst_2 : MulOneClass.{u1} α] [_inst_3 : RightDistribClass.{u1} α (MulOneClass.toMul.{u1} α _inst_2) _inst_1] (a : α) (b : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_2)))) b) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) a b) b)
Case conversion may be inaccurate. Consider using '#align add_one_mul add_one_mulₓ'. -/
theorem add_one_mul [RightDistribClass α] (a b : α) : (a + 1) * b = a * b + b := by
  rw [add_mul, one_mul]
#align add_one_mul add_one_mul

/- warning: mul_add_one -> mul_add_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] [_inst_2 : MulOneClass.{u1} α] [_inst_3 : LeftDistribClass.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2) _inst_1] (a : α) (b : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2)) a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_2)))))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2)) a b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] [_inst_2 : MulOneClass.{u1} α] [_inst_3 : LeftDistribClass.{u1} α (MulOneClass.toMul.{u1} α _inst_2) _inst_1] (a : α) (b : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_2))))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) a b) a)
Case conversion may be inaccurate. Consider using '#align mul_add_one mul_add_oneₓ'. -/
theorem mul_add_one [LeftDistribClass α] (a b : α) : a * (b + 1) = a * b + a := by
  rw [mul_add, mul_one]
#align mul_add_one mul_add_one

/- warning: one_add_mul -> one_add_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] [_inst_2 : MulOneClass.{u1} α] [_inst_3 : RightDistribClass.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2) _inst_1] (a : α) (b : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_2)))) a) b) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] [_inst_2 : MulOneClass.{u1} α] [_inst_3 : RightDistribClass.{u1} α (MulOneClass.toMul.{u1} α _inst_2) _inst_1] (a : α) (b : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_2))) a) b) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) a b))
Case conversion may be inaccurate. Consider using '#align one_add_mul one_add_mulₓ'. -/
theorem one_add_mul [RightDistribClass α] (a b : α) : (1 + a) * b = b + a * b := by
  rw [add_mul, one_mul]
#align one_add_mul one_add_mul

/- warning: mul_one_add -> mul_one_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] [_inst_2 : MulOneClass.{u1} α] [_inst_3 : LeftDistribClass.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2) _inst_1] (a : α) (b : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2)) a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_2)))) b)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] [_inst_2 : MulOneClass.{u1} α] [_inst_3 : LeftDistribClass.{u1} α (MulOneClass.toMul.{u1} α _inst_2) _inst_1] (a : α) (b : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_2))) b)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) a b))
Case conversion may be inaccurate. Consider using '#align mul_one_add mul_one_addₓ'. -/
theorem mul_one_add [LeftDistribClass α] (a b : α) : a * (1 + b) = a + a * b := by
  rw [mul_add, mul_one]
#align mul_one_add mul_one_add

/- warning: two_mul -> two_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] [_inst_2 : MulOneClass.{u1} α] [_inst_3 : RightDistribClass.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2) _inst_1] (n : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 2 (OfNat.mk.{u1} α 2 (bit0.{u1} α _inst_1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_2))))) n) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) n n)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonAssocSemiring.{u1} α] (_inst_2 : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 2 (instOfNat.{u1} α 2 (NonAssocSemiring.toNatCast.{u1} α _inst_1) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) _inst_2) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) _inst_2 _inst_2)
Case conversion may be inaccurate. Consider using '#align two_mul two_mulₓ'. -/
theorem two_mul [RightDistribClass α] (n : α) : 2 * n = n + n :=
  Eq.trans (right_distrib 1 1 n) (by simp)
#align two_mul two_mul

/- warning: bit0_eq_two_mul -> bit0_eq_two_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] [_inst_2 : MulOneClass.{u1} α] [_inst_3 : RightDistribClass.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2) _inst_1] (n : α), Eq.{succ u1} α (bit0.{u1} α _inst_1 n) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 2 (OfNat.mk.{u1} α 2 (bit0.{u1} α _inst_1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_2))))) n)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonAssocSemiring.{u1} α] (_inst_2 : α), Eq.{succ u1} α (bit0.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 2 (instOfNat.{u1} α 2 (NonAssocSemiring.toNatCast.{u1} α _inst_1) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) _inst_2)
Case conversion may be inaccurate. Consider using '#align bit0_eq_two_mul bit0_eq_two_mulₓ'. -/
theorem bit0_eq_two_mul [RightDistribClass α] (n : α) : bit0 n = 2 * n :=
  (two_mul _).symm
#align bit0_eq_two_mul bit0_eq_two_mul

/- warning: mul_two -> mul_two is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] [_inst_2 : MulOneClass.{u1} α] [_inst_3 : LeftDistribClass.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2) _inst_1] (n : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2)) n (OfNat.ofNat.{u1} α 2 (OfNat.mk.{u1} α 2 (bit0.{u1} α _inst_1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_2)))))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) n n)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonAssocSemiring.{u1} α] (_inst_2 : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) _inst_2 (OfNat.ofNat.{u1} α 2 (instOfNat.{u1} α 2 (NonAssocSemiring.toNatCast.{u1} α _inst_1) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) _inst_2 _inst_2)
Case conversion may be inaccurate. Consider using '#align mul_two mul_twoₓ'. -/
theorem mul_two [LeftDistribClass α] (n : α) : n * 2 = n + n :=
  (left_distrib n 1 1).trans (by simp)
#align mul_two mul_two

end DistribMulOneClass

section Semiring

variable [Semiring α]

#print mul_ite /-
@[to_additive]
theorem mul_ite {α} [Mul α] (P : Prop) [Decidable P] (a b c : α) :
    (a * if P then b else c) = if P then a * b else a * c := by split_ifs <;> rfl
#align mul_ite mul_ite
#align add_ite add_ite
-/

#print ite_mul /-
@[to_additive]
theorem ite_mul {α} [Mul α] (P : Prop) [Decidable P] (a b c : α) :
    (if P then a else b) * c = if P then a * c else b * c := by split_ifs <;> rfl
#align ite_mul ite_mul
#align ite_add ite_add
-/

-- We make `mul_ite` and `ite_mul` simp lemmas,
-- but not `add_ite` or `ite_add`.
-- The problem we're trying to avoid is dealing with
-- summations of the form `∑ x in s, (f x + ite P 1 0)`,
-- in which `add_ite` followed by `sum_ite` would needlessly slice up
-- the `f x` terms according to whether `P` holds at `x`.
-- There doesn't appear to be a corresponding difficulty so far with
-- `mul_ite` and `ite_mul`.
attribute [simp] mul_ite ite_mul

/- warning: mul_boole -> mul_boole is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : MulZeroOneClass.{u1} α] (P : Prop) [_inst_3 : Decidable P] (a : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α _inst_2))) a (ite.{succ u1} α P _inst_3 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α _inst_2))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α _inst_2))))))) (ite.{succ u1} α P _inst_3 a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α _inst_2))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_2 : MulZeroOneClass.{u1} α] (P : Prop) [_inst_3 : Decidable P] (a : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α _inst_2))) a (ite.{succ u1} α P _inst_3 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α _inst_2)))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MulZeroOneClass.toZero.{u1} α _inst_2))))) (ite.{succ u1} α P _inst_3 a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MulZeroOneClass.toZero.{u1} α _inst_2))))
Case conversion may be inaccurate. Consider using '#align mul_boole mul_booleₓ'. -/
@[simp]
theorem mul_boole {α} [MulZeroOneClass α] (P : Prop) [Decidable P] (a : α) :
    (a * if P then 1 else 0) = if P then a else 0 := by simp
#align mul_boole mul_boole

/- warning: boole_mul -> boole_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : MulZeroOneClass.{u1} α] (P : Prop) [_inst_3 : Decidable P] (a : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α _inst_2))) (ite.{succ u1} α P _inst_3 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α _inst_2))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α _inst_2)))))) a) (ite.{succ u1} α P _inst_3 a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α _inst_2))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_2 : MulZeroOneClass.{u1} α] (P : Prop) [_inst_3 : Decidable P] (a : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α _inst_2))) (ite.{succ u1} α P _inst_3 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α _inst_2)))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MulZeroOneClass.toZero.{u1} α _inst_2)))) a) (ite.{succ u1} α P _inst_3 a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MulZeroOneClass.toZero.{u1} α _inst_2))))
Case conversion may be inaccurate. Consider using '#align boole_mul boole_mulₓ'. -/
@[simp]
theorem boole_mul {α} [MulZeroOneClass α] (P : Prop) [Decidable P] (a : α) :
    (if P then 1 else 0) * a = if P then a else 0 := by simp
#align boole_mul boole_mul

/- warning: ite_mul_zero_left -> ite_mul_zero_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : MulZeroClass.{u1} α] (P : Prop) [_inst_3 : Decidable P] (a : α) (b : α), Eq.{succ u1} α (ite.{succ u1} α P _inst_3 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α _inst_2)) a b) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α _inst_2))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α _inst_2)) (ite.{succ u1} α P _inst_3 a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α _inst_2))))) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_2 : MulZeroClass.{u1} α] (P : Prop) [_inst_3 : Decidable P] (a : α) (b : α), Eq.{succ u1} α (ite.{succ u1} α P _inst_3 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α _inst_2)) a b) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MulZeroClass.toZero.{u1} α _inst_2)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α _inst_2)) (ite.{succ u1} α P _inst_3 a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MulZeroClass.toZero.{u1} α _inst_2)))) b)
Case conversion may be inaccurate. Consider using '#align ite_mul_zero_left ite_mul_zero_leftₓ'. -/
theorem ite_mul_zero_left {α : Type _} [MulZeroClass α] (P : Prop) [Decidable P] (a b : α) :
    ite P (a * b) 0 = ite P a 0 * b := by by_cases h : P <;> simp [h]
#align ite_mul_zero_left ite_mul_zero_left

/- warning: ite_mul_zero_right -> ite_mul_zero_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : MulZeroClass.{u1} α] (P : Prop) [_inst_3 : Decidable P] (a : α) (b : α), Eq.{succ u1} α (ite.{succ u1} α P _inst_3 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α _inst_2)) a b) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α _inst_2))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α _inst_2)) a (ite.{succ u1} α P _inst_3 b (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α _inst_2))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_2 : MulZeroClass.{u1} α] (P : Prop) [_inst_3 : Decidable P] (a : α) (b : α), Eq.{succ u1} α (ite.{succ u1} α P _inst_3 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α _inst_2)) a b) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MulZeroClass.toZero.{u1} α _inst_2)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α _inst_2)) a (ite.{succ u1} α P _inst_3 b (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MulZeroClass.toZero.{u1} α _inst_2)))))
Case conversion may be inaccurate. Consider using '#align ite_mul_zero_right ite_mul_zero_rightₓ'. -/
theorem ite_mul_zero_right {α : Type _} [MulZeroClass α] (P : Prop) [Decidable P] (a b : α) :
    ite P (a * b) 0 = a * ite P b 0 := by by_cases h : P <;> simp [h]
#align ite_mul_zero_right ite_mul_zero_right

/- warning: ite_and_mul_zero -> ite_and_mul_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : MulZeroClass.{u1} α] (P : Prop) (Q : Prop) [_inst_3 : Decidable P] [_inst_4 : Decidable Q] (a : α) (b : α), Eq.{succ u1} α (ite.{succ u1} α (And P Q) (And.decidable P Q _inst_3 _inst_4) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α _inst_2)) a b) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α _inst_2))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α _inst_2)) (ite.{succ u1} α P _inst_3 a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α _inst_2))))) (ite.{succ u1} α Q _inst_4 b (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α _inst_2))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_2 : MulZeroClass.{u1} α] (P : Prop) (Q : Prop) [_inst_3 : Decidable P] [_inst_4 : Decidable Q] (a : α) (b : α), Eq.{succ u1} α (ite.{succ u1} α (And P Q) (instDecidableAnd P Q _inst_3 _inst_4) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α _inst_2)) a b) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MulZeroClass.toZero.{u1} α _inst_2)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α _inst_2)) (ite.{succ u1} α P _inst_3 a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MulZeroClass.toZero.{u1} α _inst_2)))) (ite.{succ u1} α Q _inst_4 b (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MulZeroClass.toZero.{u1} α _inst_2)))))
Case conversion may be inaccurate. Consider using '#align ite_and_mul_zero ite_and_mul_zeroₓ'. -/
theorem ite_and_mul_zero {α : Type _} [MulZeroClass α] (P Q : Prop) [Decidable P] [Decidable Q]
    (a b : α) : ite (P ∧ Q) (a * b) 0 = ite P a 0 * ite Q b 0 := by
  simp only [← ite_and, ite_mul, mul_ite, mul_zero, zero_mul, and_comm']
#align ite_and_mul_zero ite_and_mul_zero

end Semiring

#print NonUnitalCommSemiring /-
/-- A non-unital commutative semiring is a `non_unital_semiring` with commutative multiplication.
In other words, it is a type with the following structures: additive commutative monoid
(`add_comm_monoid`), commutative semigroup (`comm_semigroup`), distributive laws (`distrib`), and
multiplication by zero law (`mul_zero_class`). -/
@[protect_proj]
class NonUnitalCommSemiring (α : Type u) extends NonUnitalSemiring α, CommSemigroup α
#align non_unital_comm_semiring NonUnitalCommSemiring
-/

#print CommSemiring /-
/-- A commutative semiring is a `semiring` with commutative multiplication. In other words, it is a
type with the following structures: additive commutative monoid (`add_comm_monoid`), multiplicative
commutative monoid (`comm_monoid`), distributive laws (`distrib`), and multiplication by zero law
(`mul_zero_class`). -/
@[protect_proj]
class CommSemiring (α : Type u) extends Semiring α, CommMonoid α
#align comm_semiring CommSemiring
-/

#print CommSemiring.toNonUnitalCommSemiring /-
-- see Note [lower instance priority]
instance (priority := 100) CommSemiring.toNonUnitalCommSemiring [CommSemiring α] :
    NonUnitalCommSemiring α :=
  { CommSemiring.toCommMonoid α, CommSemiring.toSemiring α with }
#align comm_semiring.to_non_unital_comm_semiring CommSemiring.toNonUnitalCommSemiring
-/

#print CommSemiring.toCommMonoidWithZero /-
-- see Note [lower instance priority]
instance (priority := 100) CommSemiring.toCommMonoidWithZero [CommSemiring α] :
    CommMonoidWithZero α :=
  { CommSemiring.toCommMonoid α, CommSemiring.toSemiring α with }
#align comm_semiring.to_comm_monoid_with_zero CommSemiring.toCommMonoidWithZero
-/

section CommSemiring

variable [CommSemiring α] {a b c : α}

/- warning: add_mul_self_eq -> add_mul_self_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommSemiring.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))))) a b) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))))) a b)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))))) a a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 2 (OfNat.mk.{u1} α 2 (bit0.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))) (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))))))) a) b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))))) b b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommSemiring.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))))) a b) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))))) a b)) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))) a a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))) (OfNat.ofNat.{u1} α 2 (instOfNat.{u1} α 2 (Semiring.toNatCast.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) a) b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))) b b))
Case conversion may be inaccurate. Consider using '#align add_mul_self_eq add_mul_self_eqₓ'. -/
theorem add_mul_self_eq (a b : α) : (a + b) * (a + b) = a * a + 2 * a * b + b * b := by
  simp only [two_mul, add_mul, mul_add, add_assoc, mul_comm b]
#align add_mul_self_eq add_mul_self_eq

end CommSemiring

section HasDistribNeg

#print HasDistribNeg /-
/-- Typeclass for a negation operator that distributes across multiplication.

This is useful for dealing with submonoids of a ring that contain `-1` without having to duplicate
lemmas. -/
class HasDistribNeg (α : Type _) [Mul α] extends InvolutiveNeg α where
  neg_mul : ∀ x y : α, -x * y = -(x * y)
  mul_neg : ∀ x y : α, x * -y = -(x * y)
#align has_distrib_neg HasDistribNeg
-/

section Mul

variable [Mul α] [HasDistribNeg α]

/- warning: neg_mul -> neg_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : HasDistribNeg.{u1} α _inst_1] (a : α) (b : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α _inst_1 _inst_2)) a) b) (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α _inst_1 _inst_2)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : HasDistribNeg.{u1} α _inst_1] (a : α) (b : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α _inst_1 _inst_2)) a) b) (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α _inst_1 _inst_2)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a b))
Case conversion may be inaccurate. Consider using '#align neg_mul neg_mulₓ'. -/
@[simp]
theorem neg_mul (a b : α) : -a * b = -(a * b) :=
  HasDistribNeg.neg_mul _ _
#align neg_mul neg_mul

/- warning: mul_neg -> mul_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : HasDistribNeg.{u1} α _inst_1] (a : α) (b : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α _inst_1 _inst_2)) b)) (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α _inst_1 _inst_2)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : HasDistribNeg.{u1} α _inst_1] (a : α) (b : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α _inst_1 _inst_2)) b)) (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α _inst_1 _inst_2)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a b))
Case conversion may be inaccurate. Consider using '#align mul_neg mul_negₓ'. -/
@[simp]
theorem mul_neg (a b : α) : a * -b = -(a * b) :=
  HasDistribNeg.mul_neg _ _
#align mul_neg mul_neg

/- warning: neg_mul_neg -> neg_mul_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : HasDistribNeg.{u1} α _inst_1] (a : α) (b : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α _inst_1 _inst_2)) a) (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α _inst_1 _inst_2)) b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : HasDistribNeg.{u1} α _inst_1] (a : α) (b : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α _inst_1 _inst_2)) a) (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α _inst_1 _inst_2)) b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align neg_mul_neg neg_mul_negₓ'. -/
theorem neg_mul_neg (a b : α) : -a * -b = a * b := by simp
#align neg_mul_neg neg_mul_neg

/- warning: neg_mul_eq_neg_mul -> neg_mul_eq_neg_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : HasDistribNeg.{u1} α _inst_1] (a : α) (b : α), Eq.{succ u1} α (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α _inst_1 _inst_2)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α _inst_1 _inst_2)) a) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : HasDistribNeg.{u1} α _inst_1] (a : α) (b : α), Eq.{succ u1} α (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α _inst_1 _inst_2)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α _inst_1 _inst_2)) a) b)
Case conversion may be inaccurate. Consider using '#align neg_mul_eq_neg_mul neg_mul_eq_neg_mulₓ'. -/
theorem neg_mul_eq_neg_mul (a b : α) : -(a * b) = -a * b :=
  (neg_mul _ _).symm
#align neg_mul_eq_neg_mul neg_mul_eq_neg_mul

/- warning: neg_mul_eq_mul_neg -> neg_mul_eq_mul_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : HasDistribNeg.{u1} α _inst_1] (a : α) (b : α), Eq.{succ u1} α (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α _inst_1 _inst_2)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α _inst_1 _inst_2)) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : HasDistribNeg.{u1} α _inst_1] (a : α) (b : α), Eq.{succ u1} α (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α _inst_1 _inst_2)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α _inst_1 _inst_2)) b))
Case conversion may be inaccurate. Consider using '#align neg_mul_eq_mul_neg neg_mul_eq_mul_negₓ'. -/
theorem neg_mul_eq_mul_neg (a b : α) : -(a * b) = a * -b :=
  (mul_neg _ _).symm
#align neg_mul_eq_mul_neg neg_mul_eq_mul_neg

/- warning: neg_mul_comm -> neg_mul_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : HasDistribNeg.{u1} α _inst_1] (a : α) (b : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α _inst_1 _inst_2)) a) b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α _inst_1 _inst_2)) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : HasDistribNeg.{u1} α _inst_1] (a : α) (b : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α _inst_1 _inst_2)) a) b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α _inst_1 _inst_2)) b))
Case conversion may be inaccurate. Consider using '#align neg_mul_comm neg_mul_commₓ'. -/
theorem neg_mul_comm (a b : α) : -a * b = a * -b := by simp
#align neg_mul_comm neg_mul_comm

end Mul

section MulOneClass

variable [MulOneClass α] [HasDistribNeg α]

/- warning: neg_eq_neg_one_mul -> neg_eq_neg_one_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)] (a : α), Eq.{succ u1} α (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1) _inst_2)) a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1) _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (MulOneClass.toMul.{u1} α _inst_1)] (a : α), Eq.{succ u1} α (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α (MulOneClass.toMul.{u1} α _inst_1) _inst_2)) a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α (MulOneClass.toMul.{u1} α _inst_1) _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) a)
Case conversion may be inaccurate. Consider using '#align neg_eq_neg_one_mul neg_eq_neg_one_mulₓ'. -/
theorem neg_eq_neg_one_mul (a : α) : -a = -1 * a := by simp
#align neg_eq_neg_one_mul neg_eq_neg_one_mul

/- warning: mul_neg_one -> mul_neg_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)] (a : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1) _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))) (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1) _inst_2)) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (MulOneClass.toMul.{u1} α _inst_1)] (a : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α (MulOneClass.toMul.{u1} α _inst_1) _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))) (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α (MulOneClass.toMul.{u1} α _inst_1) _inst_2)) a)
Case conversion may be inaccurate. Consider using '#align mul_neg_one mul_neg_oneₓ'. -/
/-- An element of a ring multiplied by the additive inverse of one is the element's additive
  inverse. -/
theorem mul_neg_one (a : α) : a * -1 = -a := by simp
#align mul_neg_one mul_neg_one

/- warning: neg_one_mul -> neg_one_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)] (a : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1) _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) a) (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1) _inst_2)) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (MulOneClass.toMul.{u1} α _inst_1)] (a : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α (MulOneClass.toMul.{u1} α _inst_1) _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) a) (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α (MulOneClass.toMul.{u1} α _inst_1) _inst_2)) a)
Case conversion may be inaccurate. Consider using '#align neg_one_mul neg_one_mulₓ'. -/
/-- The additive inverse of one multiplied by an element of a ring is the element's additive
  inverse. -/
theorem neg_one_mul (a : α) : -1 * a = -a := by simp
#align neg_one_mul neg_one_mul

end MulOneClass

section MulZeroClass

variable [MulZeroClass α] [HasDistribNeg α]

/- warning: mul_zero_class.neg_zero_class -> MulZeroClass.negZeroClass is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulZeroClass.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (MulZeroClass.toHasMul.{u1} α _inst_1)], NegZeroClass.{u1} α
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulZeroClass.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (MulZeroClass.toMul.{u1} α _inst_1)], NegZeroClass.{u1} α
Case conversion may be inaccurate. Consider using '#align mul_zero_class.neg_zero_class MulZeroClass.negZeroClassₓ'. -/
instance (priority := 100) MulZeroClass.negZeroClass : NegZeroClass α :=
  { MulZeroClass.toHasZero α, HasDistribNeg.toHasInvolutiveNeg α with
    neg_zero := by rw [← zero_mul (0 : α), ← neg_mul, mul_zero, mul_zero] }
#align mul_zero_class.neg_zero_class MulZeroClass.negZeroClass

end MulZeroClass

end HasDistribNeg

/-!
### Rings
-/


#print NonUnitalNonAssocRing /-
/-- A not-necessarily-unital, not-necessarily-associative ring. -/
@[protect_proj]
class NonUnitalNonAssocRing (α : Type u) extends AddCommGroup α, NonUnitalNonAssocSemiring α
#align non_unital_non_assoc_ring NonUnitalNonAssocRing
-/

#print NonUnitalRing /-
-- We defer the instance `non_unital_non_assoc_ring.to_has_distrib_neg` to `algebra.ring.basic`
-- as it relies on the lemma `eq_neg_of_add_eq_zero_left`.
/-- An associative but not-necessarily unital ring. -/
@[protect_proj]
class NonUnitalRing (α : Type _) extends NonUnitalNonAssocRing α, NonUnitalSemiring α
#align non_unital_ring NonUnitalRing
-/

#print NonAssocRing /-
/-- A unital but not-necessarily-associative ring. -/
@[protect_proj]
class NonAssocRing (α : Type _) extends NonUnitalNonAssocRing α, NonAssocSemiring α,
  AddGroupWithOne α
#align non_assoc_ring NonAssocRing
-/

#print Ring /-
/-- A ring is a type with the following structures: additive commutative group (`add_comm_group`),
multiplicative monoid (`monoid`), and distributive laws (`distrib`).  Equivalently, a ring is a
`semiring` with a negation operation making it an additive group.  -/
@[protect_proj]
class Ring (α : Type u) extends AddCommGroupWithOne α, Monoid α, Distrib α
#align ring Ring
-/

section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing α]

/- warning: non_unital_non_assoc_ring.to_has_distrib_neg -> NonUnitalNonAssocRing.toHasDistribNeg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} α], HasDistribNeg.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} α], HasDistribNeg.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align non_unital_non_assoc_ring.to_has_distrib_neg NonUnitalNonAssocRing.toHasDistribNegₓ'. -/
instance (priority := 100) NonUnitalNonAssocRing.toHasDistribNeg : HasDistribNeg α
    where
  neg := Neg.neg
  neg_neg := neg_neg
  neg_mul a b := eq_neg_of_add_eq_zero_left <| by rw [← right_distrib, add_left_neg, zero_mul]
  mul_neg a b := eq_neg_of_add_eq_zero_left <| by rw [← left_distrib, add_left_neg, mul_zero]
#align non_unital_non_assoc_ring.to_has_distrib_neg NonUnitalNonAssocRing.toHasDistribNeg

/- warning: mul_sub_left_distrib -> mul_sub_left_distrib is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1))))) b c)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α _inst_1)) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1))))) b c)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α _inst_1)) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α _inst_1)) a c))
Case conversion may be inaccurate. Consider using '#align mul_sub_left_distrib mul_sub_left_distribₓ'. -/
theorem mul_sub_left_distrib (a b c : α) : a * (b - c) = a * b - a * c := by
  simpa only [sub_eq_add_neg, neg_mul_eq_mul_neg] using mul_add a b (-c)
#align mul_sub_left_distrib mul_sub_left_distrib

/- warning: mul_sub -> mul_sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1))))) b c)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α _inst_1)) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1))))) b c)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α _inst_1)) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α _inst_1)) a c))
Case conversion may be inaccurate. Consider using '#align mul_sub mul_subₓ'. -/
alias mul_sub_left_distrib ← mul_sub
#align mul_sub mul_sub

/- warning: mul_sub_right_distrib -> mul_sub_right_distrib is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1))))) a b) c) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1))))) a b) c) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α _inst_1)) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α _inst_1)) b c))
Case conversion may be inaccurate. Consider using '#align mul_sub_right_distrib mul_sub_right_distribₓ'. -/
theorem mul_sub_right_distrib (a b c : α) : (a - b) * c = a * c - b * c := by
  simpa only [sub_eq_add_neg, neg_mul_eq_neg_mul] using add_mul a (-b) c
#align mul_sub_right_distrib mul_sub_right_distrib

/- warning: sub_mul -> sub_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1))))) a b) c) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1))))) a b) c) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α _inst_1)) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α _inst_1)) b c))
Case conversion may be inaccurate. Consider using '#align sub_mul sub_mulₓ'. -/
alias mul_sub_right_distrib ← sub_mul
#align sub_mul sub_mul

variable {a b c d e : α}

/- warning: mul_add_eq_mul_add_iff_sub_mul_add_eq -> mul_add_eq_mul_add_iff_sub_mul_add_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} α] {a : α} {b : α} {c : α} {d : α} {e : α}, Iff (Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) a e) c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) b e) d)) (Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1))))) a b) e) c) d)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} α] {a : α} {b : α} {c : α} {d : α} {e : α}, Iff (Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α _inst_1)) a e) c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α _inst_1)) b e) d)) (Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1))))) a b) e) c) d)
Case conversion may be inaccurate. Consider using '#align mul_add_eq_mul_add_iff_sub_mul_add_eq mul_add_eq_mul_add_iff_sub_mul_add_eqₓ'. -/
/-- An iff statement following from right distributivity in rings and the definition
  of subtraction. -/
theorem mul_add_eq_mul_add_iff_sub_mul_add_eq : a * e + c = b * e + d ↔ (a - b) * e + c = d :=
  calc
    a * e + c = b * e + d ↔ a * e + c = d + b * e := by simp [add_comm]
    _ ↔ a * e + c - b * e = d := Iff.intro (fun h => by rw [h]; simp) fun h => by rw [← h]; simp
    _ ↔ (a - b) * e + c = d := by simp [sub_mul, sub_add_eq_add_sub]
    
#align mul_add_eq_mul_add_iff_sub_mul_add_eq mul_add_eq_mul_add_iff_sub_mul_add_eq

/- warning: sub_mul_add_eq_of_mul_add_eq_mul_add -> sub_mul_add_eq_of_mul_add_eq_mul_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} α] {a : α} {b : α} {c : α} {d : α} {e : α}, (Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) a e) c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) b e) d)) -> (Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1))))) a b) e) c) d)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} α] {a : α} {b : α} {c : α} {d : α} {e : α}, (Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α _inst_1)) a e) c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α _inst_1)) b e) d)) -> (Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α _inst_1))))) a b) e) c) d)
Case conversion may be inaccurate. Consider using '#align sub_mul_add_eq_of_mul_add_eq_mul_add sub_mul_add_eq_of_mul_add_eq_mul_addₓ'. -/
/-- A simplification of one side of an equation exploiting right distributivity in rings
  and the definition of subtraction. -/
theorem sub_mul_add_eq_of_mul_add_eq_mul_add : a * e + c = b * e + d → (a - b) * e + c = d :=
  fun h =>
  calc
    (a - b) * e + c = a * e + c - b * e := by simp [sub_mul, sub_add_eq_add_sub]
    _ = d := by rw [h]; simp [@add_sub_cancel α]
    
#align sub_mul_add_eq_of_mul_add_eq_mul_add sub_mul_add_eq_of_mul_add_eq_mul_add

end NonUnitalNonAssocRing

section NonAssocRing

variable [NonAssocRing α]

/- warning: sub_one_mul -> sub_one_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonAssocRing.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α _inst_1))))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α _inst_1))))) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α _inst_1))))))) b) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α _inst_1))))) a b) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonAssocRing.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α _inst_1))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (AddGroupWithOne.toSub.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α _inst_1))) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (NonAssocRing.toOne.{u1} α _inst_1)))) b) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (AddGroupWithOne.toSub.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α _inst_1))) a b) b)
Case conversion may be inaccurate. Consider using '#align sub_one_mul sub_one_mulₓ'. -/
theorem sub_one_mul (a b : α) : (a - 1) * b = a * b - b := by rw [sub_mul, one_mul]
#align sub_one_mul sub_one_mul

/- warning: mul_sub_one -> mul_sub_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonAssocRing.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α _inst_1))))) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α _inst_1))))) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α _inst_1)))))))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α _inst_1))))) a b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonAssocRing.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α _inst_1))) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (AddGroupWithOne.toSub.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α _inst_1))) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (NonAssocRing.toOne.{u1} α _inst_1))))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (AddGroupWithOne.toSub.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α _inst_1))) a b) a)
Case conversion may be inaccurate. Consider using '#align mul_sub_one mul_sub_oneₓ'. -/
theorem mul_sub_one (a b : α) : a * (b - 1) = a * b - a := by rw [mul_sub, mul_one]
#align mul_sub_one mul_sub_one

/- warning: one_sub_mul -> one_sub_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonAssocRing.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α _inst_1))))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α _inst_1))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α _inst_1)))))) a) b) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α _inst_1))))) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α _inst_1))))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonAssocRing.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α _inst_1))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (AddGroupWithOne.toSub.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (NonAssocRing.toOne.{u1} α _inst_1))) a) b) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (AddGroupWithOne.toSub.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α _inst_1))) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α _inst_1))) a b))
Case conversion may be inaccurate. Consider using '#align one_sub_mul one_sub_mulₓ'. -/
theorem one_sub_mul (a b : α) : (1 - a) * b = b - a * b := by rw [sub_mul, one_mul]
#align one_sub_mul one_sub_mul

/- warning: mul_one_sub -> mul_one_sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonAssocRing.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α _inst_1))))) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α _inst_1))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α _inst_1)))))) b)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α _inst_1))))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α _inst_1))))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonAssocRing.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α _inst_1))) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (AddGroupWithOne.toSub.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (NonAssocRing.toOne.{u1} α _inst_1))) b)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (AddGroupWithOne.toSub.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α _inst_1))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α _inst_1))) a b))
Case conversion may be inaccurate. Consider using '#align mul_one_sub mul_one_subₓ'. -/
theorem mul_one_sub (a b : α) : a * (1 - b) = a - a * b := by rw [mul_sub, mul_one]
#align mul_one_sub mul_one_sub

end NonAssocRing

section Ring

variable [Ring α] {a b c d e : α}

#print Ring.toNonUnitalRing /-
-- A (unital, associative) ring is a not-necessarily-unital ring 
-- see Note [lower instance priority]
instance (priority := 100) Ring.toNonUnitalRing : NonUnitalRing α :=
  {
    ‹Ring
        α› with
    zero_mul := fun a =>
      add_left_cancel <| show 0 * a + 0 * a = 0 * a + 0 by rw [← add_mul, zero_add, add_zero]
    mul_zero := fun a =>
      add_left_cancel <| show a * 0 + a * 0 = a * 0 + 0 by rw [← mul_add, add_zero, add_zero] }
#align ring.to_non_unital_ring Ring.toNonUnitalRing
-/

#print Ring.toNonAssocRing /-
-- A (unital, associative) ring is a not-necessarily-associative ring 
-- see Note [lower instance priority]
instance (priority := 100) Ring.toNonAssocRing : NonAssocRing α :=
  {
    ‹Ring
        α› with
    zero_mul := fun a =>
      add_left_cancel <| show 0 * a + 0 * a = 0 * a + 0 by rw [← add_mul, zero_add, add_zero]
    mul_zero := fun a =>
      add_left_cancel <| show a * 0 + a * 0 = a * 0 + 0 by rw [← mul_add, add_zero, add_zero] }
#align ring.to_non_assoc_ring Ring.toNonAssocRing
-/

#print Ring.toSemiring /-
/- The instance from `ring` to `semiring` happens often in linear algebra, for which all the basic
definitions are given in terms of semirings, but many applications use rings or fields. We increase
a little bit its priority above 100 to try it quickly, but remaining below the default 1000 so that
more specific instances are tried first. -/
instance (priority := 200) Ring.toSemiring : Semiring α :=
  { ‹Ring α›, Ring.toNonUnitalRing with }
#align ring.to_semiring Ring.toSemiring
-/

end Ring

#print NonUnitalCommRing /-
/-- A non-unital commutative ring is a `non_unital_ring` with commutative multiplication. -/
@[protect_proj]
class NonUnitalCommRing (α : Type u) extends NonUnitalRing α, CommSemigroup α
#align non_unital_comm_ring NonUnitalCommRing
-/

#print NonUnitalCommRing.toNonUnitalCommSemiring /-
-- see Note [lower instance priority]
instance (priority := 100) NonUnitalCommRing.toNonUnitalCommSemiring [s : NonUnitalCommRing α] :
    NonUnitalCommSemiring α :=
  { s with }
#align non_unital_comm_ring.to_non_unital_comm_semiring NonUnitalCommRing.toNonUnitalCommSemiring
-/

#print CommRing /-
/-- A commutative ring is a `ring` with commutative multiplication. -/
@[protect_proj]
class CommRing (α : Type u) extends Ring α, CommMonoid α
#align comm_ring CommRing
-/

#print CommRing.toCommSemiring /-
-- see Note [lower instance priority]
instance (priority := 100) CommRing.toCommSemiring [s : CommRing α] : CommSemiring α :=
  { s with
    mul_zero := mul_zero
    zero_mul := zero_mul }
#align comm_ring.to_comm_semiring CommRing.toCommSemiring
-/

#print CommRing.toNonUnitalCommRing /-
-- see Note [lower instance priority]
instance (priority := 100) CommRing.toNonUnitalCommRing [s : CommRing α] : NonUnitalCommRing α :=
  { s with
    mul_zero := mul_zero
    zero_mul := zero_mul }
#align comm_ring.to_non_unital_comm_ring CommRing.toNonUnitalCommRing
-/

#print IsDomain /-
/-- A domain is a nontrivial semiring such multiplication by a non zero element is cancellative,
  on both sides. In other words, a nontrivial semiring `R` satisfying
  `∀ {a b c : R}, a ≠ 0 → a * b = a * c → b = c` and
  `∀ {a b c : R}, b ≠ 0 → a * b = c * b → a = c`.

  This is implemented as a mixin for `semiring α`.
  To obtain an integral domain use `[comm_ring α] [is_domain α]`. -/
@[protect_proj]
class IsDomain (α : Type u) [Semiring α] extends IsCancelMulZero α, Nontrivial α : Prop
#align is_domain IsDomain
-/

