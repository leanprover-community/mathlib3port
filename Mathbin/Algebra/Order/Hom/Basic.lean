/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module algebra.order.hom.basic
! leanprover-community/mathlib commit 44b58b42794e5abe2bf86397c38e26b587e07e59
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Hom.Group

/-!
# Algebraic order homomorphism classes

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines hom classes for common properties at the intersection of order theory and algebra.

## Typeclasses

* `nonneg_hom_class`: Homs are nonnegative: `∀ f a, 0 ≤ f a`
* `subadditive_hom_class`: Homs are subadditive: `∀ f a b, f (a + b) ≤ f a + f b`
* `submultiplicative_hom_class`: Homs are submultiplicative: `∀ f a b, f (a * b) ≤ f a * f b`
* `mul_le_add_hom_class`: `∀ f a b, f (a * b) ≤ f a + f b`
* `nonarchimedean_hom_class`: `∀ a b, f (a + b) ≤ max (f a) (f b)`

## TODO

Finitary versions of the current lemmas.
-/


open Function

variable {ι F α β γ δ : Type _}

#print NonnegHomClass /-
/-- `nonneg_hom_class F α β` states that `F` is a type of nonnegative morphisms. -/
class NonnegHomClass (F : Type _) (α β : outParam <| Type _) [Zero β] [LE β] extends
  FunLike F α fun _ => β where
  map_nonneg (f : F) : ∀ a, 0 ≤ f a
#align nonneg_hom_class NonnegHomClass
-/

#print SubadditiveHomClass /-
/-- `subadditive_hom_class F α β` states that `F` is a type of subadditive morphisms. -/
class SubadditiveHomClass (F : Type _) (α β : outParam <| Type _) [Add α] [Add β] [LE β] extends
  FunLike F α fun _ => β where
  map_add_le_add (f : F) : ∀ a b, f (a + b) ≤ f a + f b
#align subadditive_hom_class SubadditiveHomClass
-/

#print SubmultiplicativeHomClass /-
/-- `submultiplicative_hom_class F α β` states that `F` is a type of submultiplicative morphisms. -/
@[to_additive SubadditiveHomClass]
class SubmultiplicativeHomClass (F : Type _) (α β : outParam <| Type _) [Mul α] [Mul β]
  [LE β] extends FunLike F α fun _ => β where
  map_mul_le_mul (f : F) : ∀ a b, f (a * b) ≤ f a * f b
#align submultiplicative_hom_class SubmultiplicativeHomClass
-/

#print MulLEAddHomClass /-
/-- `mul_le_add_hom_class F α β` states that `F` is a type of subadditive morphisms. -/
@[to_additive SubadditiveHomClass]
class MulLEAddHomClass (F : Type _) (α β : outParam <| Type _) [Mul α] [Add β] [LE β] extends
  FunLike F α fun _ => β where
  map_mul_le_add (f : F) : ∀ a b, f (a * b) ≤ f a + f b
#align mul_le_add_hom_class MulLEAddHomClass
-/

#print NonarchimedeanHomClass /-
/-- `nonarchimedean_hom_class F α β` states that `F` is a type of non-archimedean morphisms. -/
class NonarchimedeanHomClass (F : Type _) (α β : outParam <| Type _) [Add α] [LinearOrder β] extends
  FunLike F α fun _ => β where
  map_add_le_max (f : F) : ∀ a b, f (a + b) ≤ max (f a) (f b)
#align nonarchimedean_hom_class NonarchimedeanHomClass
-/

export NonnegHomClass (map_nonneg)

export SubadditiveHomClass (map_add_le_add)

export SubmultiplicativeHomClass (map_mul_le_mul)

export MulLEAddHomClass (map_mul_le_add)

export NonarchimedeanHomClass (map_add_le_max)

attribute [simp] map_nonneg

/- warning: le_map_mul_map_div -> le_map_mul_map_div is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Group.{u2} α] [_inst_2 : CommSemigroup.{u3} β] [_inst_3 : LE.{u3} β] [_inst_4 : SubmultiplicativeHomClass.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (Semigroup.toHasMul.{u3} β (CommSemigroup.toSemigroup.{u3} β _inst_2)) _inst_3] (f : F) (a : α) (b : α), LE.le.{u3} β _inst_3 (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (SubmultiplicativeHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (Semigroup.toHasMul.{u3} β (CommSemigroup.toSemigroup.{u3} β _inst_2)) _inst_3 _inst_4)) f a) (HMul.hMul.{u3, u3, u3} β β β (instHMul.{u3} β (Semigroup.toHasMul.{u3} β (CommSemigroup.toSemigroup.{u3} β _inst_2))) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (SubmultiplicativeHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (Semigroup.toHasMul.{u3} β (CommSemigroup.toSemigroup.{u3} β _inst_2)) _inst_3 _inst_4)) f b) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (SubmultiplicativeHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (Semigroup.toHasMul.{u3} β (CommSemigroup.toSemigroup.{u3} β _inst_2)) _inst_3 _inst_4)) f (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toHasDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) a b)))
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : Group.{u3} α] [_inst_2 : CommSemigroup.{u2} β] [_inst_3 : LE.{u2} β] [_inst_4 : SubmultiplicativeHomClass.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1)))) (Semigroup.toMul.{u2} β (CommSemigroup.toSemigroup.{u2} β _inst_2)) _inst_3] (f : F) (a : α) (b : α), LE.le.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.158 : α) => β) a) _inst_3 (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.158 : α) => β) _x) (SubmultiplicativeHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1)))) (Semigroup.toMul.{u2} β (CommSemigroup.toSemigroup.{u2} β _inst_2)) _inst_3 _inst_4) f a) (HMul.hMul.{u2, u2, u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.158 : α) => β) b) ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.158 : α) => β) (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a b)) ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.158 : α) => β) b) (instHMul.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.158 : α) => β) b) (Semigroup.toMul.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.158 : α) => β) b) (CommSemigroup.toSemigroup.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.158 : α) => β) b) _inst_2))) (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.158 : α) => β) _x) (SubmultiplicativeHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1)))) (Semigroup.toMul.{u2} β (CommSemigroup.toSemigroup.{u2} β _inst_2)) _inst_3 _inst_4) f b) (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.158 : α) => β) _x) (SubmultiplicativeHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1)))) (Semigroup.toMul.{u2} β (CommSemigroup.toSemigroup.{u2} β _inst_2)) _inst_3 _inst_4) f (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a b)))
Case conversion may be inaccurate. Consider using '#align le_map_mul_map_div le_map_mul_map_divₓ'. -/
@[to_additive]
theorem le_map_mul_map_div [Group α] [CommSemigroup β] [LE β] [SubmultiplicativeHomClass F α β]
    (f : F) (a b : α) : f a ≤ f b * f (a / b) := by
  simpa only [mul_comm, div_mul_cancel'] using map_mul_le_mul f (a / b) b
#align le_map_mul_map_div le_map_mul_map_div

/- warning: le_map_add_map_div -> le_map_add_map_div is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Group.{u2} α] [_inst_2 : AddCommSemigroup.{u3} β] [_inst_3 : LE.{u3} β] [_inst_4 : MulLEAddHomClass.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (AddSemigroup.toHasAdd.{u3} β (AddCommSemigroup.toAddSemigroup.{u3} β _inst_2)) _inst_3] (f : F) (a : α) (b : α), LE.le.{u3} β _inst_3 (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulLEAddHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (AddSemigroup.toHasAdd.{u3} β (AddCommSemigroup.toAddSemigroup.{u3} β _inst_2)) _inst_3 _inst_4)) f a) (HAdd.hAdd.{u3, u3, u3} β β β (instHAdd.{u3} β (AddSemigroup.toHasAdd.{u3} β (AddCommSemigroup.toAddSemigroup.{u3} β _inst_2))) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulLEAddHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (AddSemigroup.toHasAdd.{u3} β (AddCommSemigroup.toAddSemigroup.{u3} β _inst_2)) _inst_3 _inst_4)) f b) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulLEAddHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (AddSemigroup.toHasAdd.{u3} β (AddCommSemigroup.toAddSemigroup.{u3} β _inst_2)) _inst_3 _inst_4)) f (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toHasDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) a b)))
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : Group.{u3} α] [_inst_2 : AddCommSemigroup.{u2} β] [_inst_3 : LE.{u2} β] [_inst_4 : MulLEAddHomClass.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1)))) (AddSemigroup.toAdd.{u2} β (AddCommSemigroup.toAddSemigroup.{u2} β _inst_2)) _inst_3] (f : F) (a : α) (b : α), LE.le.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.220 : α) => β) a) _inst_3 (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.220 : α) => β) _x) (MulLEAddHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1)))) (AddSemigroup.toAdd.{u2} β (AddCommSemigroup.toAddSemigroup.{u2} β _inst_2)) _inst_3 _inst_4) f a) (HAdd.hAdd.{u2, u2, u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.220 : α) => β) b) ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.220 : α) => β) (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a b)) ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.220 : α) => β) b) (instHAdd.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.220 : α) => β) b) (AddSemigroup.toAdd.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.220 : α) => β) b) (AddCommSemigroup.toAddSemigroup.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.220 : α) => β) b) _inst_2))) (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.220 : α) => β) _x) (MulLEAddHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1)))) (AddSemigroup.toAdd.{u2} β (AddCommSemigroup.toAddSemigroup.{u2} β _inst_2)) _inst_3 _inst_4) f b) (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.220 : α) => β) _x) (MulLEAddHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1)))) (AddSemigroup.toAdd.{u2} β (AddCommSemigroup.toAddSemigroup.{u2} β _inst_2)) _inst_3 _inst_4) f (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a b)))
Case conversion may be inaccurate. Consider using '#align le_map_add_map_div le_map_add_map_divₓ'. -/
@[to_additive]
theorem le_map_add_map_div [Group α] [AddCommSemigroup β] [LE β] [MulLEAddHomClass F α β] (f : F)
    (a b : α) : f a ≤ f b + f (a / b) := by
  simpa only [add_comm, div_mul_cancel'] using map_mul_le_add f (a / b) b
#align le_map_add_map_div le_map_add_map_div

/- warning: le_map_div_mul_map_div -> le_map_div_mul_map_div is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Group.{u2} α] [_inst_2 : CommSemigroup.{u3} β] [_inst_3 : LE.{u3} β] [_inst_4 : SubmultiplicativeHomClass.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (Semigroup.toHasMul.{u3} β (CommSemigroup.toSemigroup.{u3} β _inst_2)) _inst_3] (f : F) (a : α) (b : α) (c : α), LE.le.{u3} β _inst_3 (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (SubmultiplicativeHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (Semigroup.toHasMul.{u3} β (CommSemigroup.toSemigroup.{u3} β _inst_2)) _inst_3 _inst_4)) f (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toHasDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) a c)) (HMul.hMul.{u3, u3, u3} β β β (instHMul.{u3} β (Semigroup.toHasMul.{u3} β (CommSemigroup.toSemigroup.{u3} β _inst_2))) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (SubmultiplicativeHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (Semigroup.toHasMul.{u3} β (CommSemigroup.toSemigroup.{u3} β _inst_2)) _inst_3 _inst_4)) f (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toHasDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) a b)) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (SubmultiplicativeHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (Semigroup.toHasMul.{u3} β (CommSemigroup.toSemigroup.{u3} β _inst_2)) _inst_3 _inst_4)) f (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toHasDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) b c)))
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : Group.{u3} α] [_inst_2 : CommSemigroup.{u2} β] [_inst_3 : LE.{u2} β] [_inst_4 : SubmultiplicativeHomClass.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1)))) (Semigroup.toMul.{u2} β (CommSemigroup.toSemigroup.{u2} β _inst_2)) _inst_3] (f : F) (a : α) (b : α) (c : α), LE.le.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.158 : α) => β) (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a c)) _inst_3 (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.158 : α) => β) _x) (SubmultiplicativeHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1)))) (Semigroup.toMul.{u2} β (CommSemigroup.toSemigroup.{u2} β _inst_2)) _inst_3 _inst_4) f (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a c)) (HMul.hMul.{u2, u2, u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.158 : α) => β) (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a b)) ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.158 : α) => β) (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) b c)) ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.158 : α) => β) (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a b)) (instHMul.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.158 : α) => β) (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a b)) (Semigroup.toMul.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.158 : α) => β) (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a b)) (CommSemigroup.toSemigroup.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.158 : α) => β) (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a b)) _inst_2))) (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.158 : α) => β) _x) (SubmultiplicativeHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1)))) (Semigroup.toMul.{u2} β (CommSemigroup.toSemigroup.{u2} β _inst_2)) _inst_3 _inst_4) f (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a b)) (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.158 : α) => β) _x) (SubmultiplicativeHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1)))) (Semigroup.toMul.{u2} β (CommSemigroup.toSemigroup.{u2} β _inst_2)) _inst_3 _inst_4) f (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) b c)))
Case conversion may be inaccurate. Consider using '#align le_map_div_mul_map_div le_map_div_mul_map_divₓ'. -/
@[to_additive]
theorem le_map_div_mul_map_div [Group α] [CommSemigroup β] [LE β] [SubmultiplicativeHomClass F α β]
    (f : F) (a b c : α) : f (a / c) ≤ f (a / b) * f (b / c) := by
  simpa only [div_mul_div_cancel'] using map_mul_le_mul f (a / b) (b / c)
#align le_map_div_mul_map_div le_map_div_mul_map_div

/- warning: le_map_div_add_map_div -> le_map_div_add_map_div is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Group.{u2} α] [_inst_2 : AddCommSemigroup.{u3} β] [_inst_3 : LE.{u3} β] [_inst_4 : MulLEAddHomClass.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (AddSemigroup.toHasAdd.{u3} β (AddCommSemigroup.toAddSemigroup.{u3} β _inst_2)) _inst_3] (f : F) (a : α) (b : α) (c : α), LE.le.{u3} β _inst_3 (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulLEAddHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (AddSemigroup.toHasAdd.{u3} β (AddCommSemigroup.toAddSemigroup.{u3} β _inst_2)) _inst_3 _inst_4)) f (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toHasDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) a c)) (HAdd.hAdd.{u3, u3, u3} β β β (instHAdd.{u3} β (AddSemigroup.toHasAdd.{u3} β (AddCommSemigroup.toAddSemigroup.{u3} β _inst_2))) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulLEAddHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (AddSemigroup.toHasAdd.{u3} β (AddCommSemigroup.toAddSemigroup.{u3} β _inst_2)) _inst_3 _inst_4)) f (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toHasDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) a b)) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulLEAddHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (AddSemigroup.toHasAdd.{u3} β (AddCommSemigroup.toAddSemigroup.{u3} β _inst_2)) _inst_3 _inst_4)) f (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toHasDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) b c)))
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : Group.{u3} α] [_inst_2 : AddCommSemigroup.{u2} β] [_inst_3 : LE.{u2} β] [_inst_4 : MulLEAddHomClass.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1)))) (AddSemigroup.toAdd.{u2} β (AddCommSemigroup.toAddSemigroup.{u2} β _inst_2)) _inst_3] (f : F) (a : α) (b : α) (c : α), LE.le.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.220 : α) => β) (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a c)) _inst_3 (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.220 : α) => β) _x) (MulLEAddHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1)))) (AddSemigroup.toAdd.{u2} β (AddCommSemigroup.toAddSemigroup.{u2} β _inst_2)) _inst_3 _inst_4) f (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a c)) (HAdd.hAdd.{u2, u2, u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.220 : α) => β) (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a b)) ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.220 : α) => β) (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) b c)) ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.220 : α) => β) (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a b)) (instHAdd.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.220 : α) => β) (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a b)) (AddSemigroup.toAdd.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.220 : α) => β) (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a b)) (AddCommSemigroup.toAddSemigroup.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.220 : α) => β) (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a b)) _inst_2))) (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.220 : α) => β) _x) (MulLEAddHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1)))) (AddSemigroup.toAdd.{u2} β (AddCommSemigroup.toAddSemigroup.{u2} β _inst_2)) _inst_3 _inst_4) f (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a b)) (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.220 : α) => β) _x) (MulLEAddHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1)))) (AddSemigroup.toAdd.{u2} β (AddCommSemigroup.toAddSemigroup.{u2} β _inst_2)) _inst_3 _inst_4) f (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) b c)))
Case conversion may be inaccurate. Consider using '#align le_map_div_add_map_div le_map_div_add_map_divₓ'. -/
@[to_additive]
theorem le_map_div_add_map_div [Group α] [AddCommSemigroup β] [LE β] [MulLEAddHomClass F α β]
    (f : F) (a b c : α) : f (a / c) ≤ f (a / b) + f (b / c) := by
  simpa only [div_mul_div_cancel'] using map_mul_le_add f (a / b) (b / c)
#align le_map_div_add_map_div le_map_div_add_map_div

