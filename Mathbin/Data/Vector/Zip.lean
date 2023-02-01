/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module data.vector.zip
! leanprover-community/mathlib commit 59694bd07f0a39c5beccba34bd9f413a160782bf
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Vector.Basic
import Mathbin.Data.List.Zip

/-!
# The `zip_with` operation on vectors.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


namespace Vector

section ZipWith

variable {α β γ : Type _} {n : ℕ} (f : α → β → γ)

#print Vector.zipWith /-
/-- Apply the function `f : α → β → γ` to each corresponding pair of elements from two vectors. -/
def zipWith : Vector α n → Vector β n → Vector γ n := fun x y => ⟨List.zipWith f x.1 y.1, by simp⟩
#align vector.zip_with Vector.zipWith
-/

/- warning: vector.zip_with_to_list -> Vector.zipWith_toList is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {n : Nat} (f : α -> β -> γ) (x : Vector.{u1} α n) (y : Vector.{u2} β n), Eq.{succ u3} (List.{u3} γ) (Vector.toList.{u3} γ n (Vector.zipWith.{u1, u2, u3} α β γ n f x y)) (List.zipWith.{u1, u2, u3} α β γ f (Vector.toList.{u1} α n x) (Vector.toList.{u2} β n y))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {n : Nat} (f : α -> β -> γ) (x : Vector.{u3} α n) (y : Vector.{u2} β n), Eq.{succ u1} (List.{u1} γ) (Vector.toList.{u1} γ n (Vector.zipWith.{u3, u2, u1} α β γ n f x y)) (List.zipWith.{u3, u2, u1} α β γ f (Vector.toList.{u3} α n x) (Vector.toList.{u2} β n y))
Case conversion may be inaccurate. Consider using '#align vector.zip_with_to_list Vector.zipWith_toListₓ'. -/
@[simp]
theorem zipWith_toList (x : Vector α n) (y : Vector β n) :
    (Vector.zipWith f x y).toList = List.zipWith f x.toList y.toList :=
  rfl
#align vector.zip_with_to_list Vector.zipWith_toList

/- warning: vector.zip_with_nth -> Vector.zipWith_get is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {n : Nat} (f : α -> β -> γ) (x : Vector.{u1} α n) (y : Vector.{u2} β n) (i : Fin n), Eq.{succ u3} γ (Vector.get.{u3} γ n (Vector.zipWith.{u1, u2, u3} α β γ n f x y) i) (f (Vector.get.{u1} α n x i) (Vector.get.{u2} β n y i))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {n : Nat} (f : α -> β -> γ) (x : Vector.{u3} α n) (y : Vector.{u2} β n) (i : Fin n), Eq.{succ u1} γ (Vector.get.{u1} γ n (Vector.zipWith.{u3, u2, u1} α β γ n f x y) i) (f (Vector.get.{u3} α n x i) (Vector.get.{u2} β n y i))
Case conversion may be inaccurate. Consider using '#align vector.zip_with_nth Vector.zipWith_getₓ'. -/
@[simp]
theorem zipWith_get (x : Vector α n) (y : Vector β n) (i) :
    (Vector.zipWith f x y).get? i = f (x.get? i) (y.get? i) :=
  by
  dsimp only [Vector.zipWith, Vector.get]
  cases x; cases y
  simp only [List.nthLe_zipWith, Subtype.coe_mk]
  congr
#align vector.zip_with_nth Vector.zipWith_get

/- warning: vector.zip_with_tail -> Vector.zipWith_tail is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {n : Nat} (f : α -> β -> γ) (x : Vector.{u1} α n) (y : Vector.{u2} β n), Eq.{succ u3} (Vector.{u3} γ (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Vector.tail.{u3} γ n (Vector.zipWith.{u1, u2, u3} α β γ n f x y)) (Vector.zipWith.{u1, u2, u3} α β γ (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) f (Vector.tail.{u1} α n x) (Vector.tail.{u2} β n y))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {n : Nat} (f : α -> β -> γ) (x : Vector.{u3} α n) (y : Vector.{u2} β n), Eq.{succ u1} (Vector.{u1} γ (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Vector.tail.{u1} γ n (Vector.zipWith.{u3, u2, u1} α β γ n f x y)) (Vector.zipWith.{u3, u2, u1} α β γ (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) f (Vector.tail.{u3} α n x) (Vector.tail.{u2} β n y))
Case conversion may be inaccurate. Consider using '#align vector.zip_with_tail Vector.zipWith_tailₓ'. -/
@[simp]
theorem zipWith_tail (x : Vector α n) (y : Vector β n) :
    (Vector.zipWith f x y).tail = Vector.zipWith f x.tail y.tail :=
  by
  ext
  simp [nth_tail]
#align vector.zip_with_tail Vector.zipWith_tail

/- warning: vector.prod_mul_prod_eq_prod_zip_with -> Vector.prod_mul_prod_eq_prod_zipWith is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Nat} [_inst_1 : CommMonoid.{u1} α] (x : Vector.{u1} α n) (y : Vector.{u1} α n), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Vector.toList.{u1} α n x)) (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Vector.toList.{u1} α n y))) (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Vector.toList.{u1} α n (Vector.zipWith.{u1, u1, u1} α α α n (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))) x y)))
but is expected to have type
  forall {α : Type.{u1}} {n : Nat} [_inst_1 : CommMonoid.{u1} α] (x : Vector.{u1} α n) (y : Vector.{u1} α n), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Vector.toList.{u1} α n x)) (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Vector.toList.{u1} α n y))) (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Vector.toList.{u1} α n (Vector.zipWith.{u1, u1, u1} α α α n (fun (x._@.Mathlib.Data.Vector.Zip._hyg.241 : α) (x._@.Mathlib.Data.Vector.Zip._hyg.243 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x._@.Mathlib.Data.Vector.Zip._hyg.241 x._@.Mathlib.Data.Vector.Zip._hyg.243) x y)))
Case conversion may be inaccurate. Consider using '#align vector.prod_mul_prod_eq_prod_zip_with Vector.prod_mul_prod_eq_prod_zipWithₓ'. -/
@[to_additive]
theorem prod_mul_prod_eq_prod_zipWith [CommMonoid α] (x y : Vector α n) :
    x.toList.Prod * y.toList.Prod = (Vector.zipWith (· * ·) x y).toList.Prod :=
  List.prod_mul_prod_eq_prod_zipWith_of_length_eq x.toList y.toList
    ((toList_length x).trans (toList_length y).symm)
#align vector.prod_mul_prod_eq_prod_zip_with Vector.prod_mul_prod_eq_prod_zipWith
#align vector.sum_add_sum_eq_sum_zip_with Vector.sum_add_sum_eq_sum_zipWith

end ZipWith

end Vector

