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


namespace Mathlib.Vector

section ZipWith

variable {α β γ : Type _} {n : ℕ} (f : α → β → γ)

#print Mathlib.Vector.zipWith /-
/-- Apply the function `f : α → β → γ` to each corresponding pair of elements from two vectors. -/
def Mathlib.Vector.zipWith : Mathlib.Vector α n → Mathlib.Vector β n → Mathlib.Vector γ n :=
  fun x y => ⟨List.zipWith f x.1 y.1, by simp⟩
#align vector.zip_with Mathlib.Vector.zipWith
-/

#print Mathlib.Vector.zipWith_toList /-
@[simp]
theorem Mathlib.Vector.zipWith_toList (x : Mathlib.Vector α n) (y : Mathlib.Vector β n) :
    (Mathlib.Vector.zipWith f x y).toList = List.zipWith f x.toList y.toList :=
  rfl
#align vector.zip_with_to_list Mathlib.Vector.zipWith_toList
-/

#print Mathlib.Vector.zipWith_get /-
@[simp]
theorem Mathlib.Vector.zipWith_get (x : Mathlib.Vector α n) (y : Mathlib.Vector β n) (i) :
    (Mathlib.Vector.zipWith f x y).get? i = f (x.get? i) (y.get? i) :=
  by
  dsimp only [Mathlib.Vector.zipWith, Mathlib.Vector.get]
  cases x; cases y
  simp only [List.nthLe_zipWith, Subtype.coe_mk]
  congr
#align vector.zip_with_nth Mathlib.Vector.zipWith_get
-/

#print Mathlib.Vector.zipWith_tail /-
@[simp]
theorem Mathlib.Vector.zipWith_tail (x : Mathlib.Vector α n) (y : Mathlib.Vector β n) :
    (Mathlib.Vector.zipWith f x y).tail = Mathlib.Vector.zipWith f x.tail y.tail := by ext;
  simp [nth_tail]
#align vector.zip_with_tail Mathlib.Vector.zipWith_tail
-/

#print Mathlib.Vector.prod_mul_prod_eq_prod_zipWith /-
@[to_additive]
theorem Mathlib.Vector.prod_mul_prod_eq_prod_zipWith [CommMonoid α] (x y : Mathlib.Vector α n) :
    x.toList.Prod * y.toList.Prod = (Mathlib.Vector.zipWith (· * ·) x y).toList.Prod :=
  List.prod_mul_prod_eq_prod_zipWith_of_length_eq x.toList y.toList
    ((Mathlib.Vector.toList_length x).trans (Mathlib.Vector.toList_length y).symm)
#align vector.prod_mul_prod_eq_prod_zip_with Mathlib.Vector.prod_mul_prod_eq_prod_zipWith
#align vector.sum_add_sum_eq_sum_zip_with Mathlib.Vector.sum_add_sum_eq_sum_zipWith
-/

end ZipWith

end Mathlib.Vector

