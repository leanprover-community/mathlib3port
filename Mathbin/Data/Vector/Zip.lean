/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Data.Vector.Basic
import Data.List.Zip

#align_import data.vector.zip from "leanprover-community/mathlib"@"63f84d91dd847f50bae04a01071f3a5491934e36"

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

#print Vector.zipWith_toList /-
@[simp]
theorem zipWith_toList (x : Vector α n) (y : Vector β n) :
    (Vector.zipWith f x y).toList = List.zipWith f x.toList y.toList :=
  rfl
#align vector.zip_with_to_list Vector.zipWith_toList
-/

#print Vector.zipWith_get /-
@[simp]
theorem zipWith_get (x : Vector α n) (y : Vector β n) (i) :
    (Vector.zipWith f x y).get? i = f (x.get? i) (y.get? i) :=
  by
  dsimp only [Vector.zipWith, Vector.get]
  cases x; cases y
  simp only [List.nthLe_zipWith, Subtype.coe_mk]
  congr
#align vector.zip_with_nth Vector.zipWith_get
-/

#print Vector.zipWith_tail /-
@[simp]
theorem zipWith_tail (x : Vector α n) (y : Vector β n) :
    (Vector.zipWith f x y).tail = Vector.zipWith f x.tail y.tail := by ext; simp [nth_tail]
#align vector.zip_with_tail Vector.zipWith_tail
-/

#print Vector.prod_mul_prod_eq_prod_zipWith /-
@[to_additive]
theorem prod_mul_prod_eq_prod_zipWith [CommMonoid α] (x y : Vector α n) :
    x.toList.Prod * y.toList.Prod = (Vector.zipWith (· * ·) x y).toList.Prod :=
  List.prod_mul_prod_eq_prod_zipWith_of_length_eq x.toList y.toList
    ((toList_length x).trans (toList_length y).symm)
#align vector.prod_mul_prod_eq_prod_zip_with Vector.prod_mul_prod_eq_prod_zipWith
#align vector.sum_add_sum_eq_sum_zip_with Vector.sum_add_sum_eq_sum_zipWith
-/

end ZipWith

end Vector

