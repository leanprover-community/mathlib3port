/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathbin.Data.Rat.Cast
import Mathbin.Algebra.BigOperators.Basic

#align_import data.rat.big_operators from "leanprover-community/mathlib"@"327c3c0d9232d80e250dc8f65e7835b82b266ea5"

/-! # Casting lemmas for rational numbers involving sums and products

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open scoped BigOperators

variable {ι α : Type _}

namespace Rat

section WithDivRing

variable [DivisionRing α] [CharZero α]

#print Rat.cast_list_sum /-
@[simp, norm_cast]
theorem cast_list_sum (s : List ℚ) : (↑s.Sum : α) = (s.map coe).Sum :=
  map_list_sum (Rat.castHom α) _
#align rat.cast_list_sum Rat.cast_list_sum
-/

#print Rat.cast_multiset_sum /-
@[simp, norm_cast]
theorem cast_multiset_sum (s : Multiset ℚ) : (↑s.Sum : α) = (s.map coe).Sum :=
  map_multiset_sum (Rat.castHom α) _
#align rat.cast_multiset_sum Rat.cast_multiset_sum
-/

#print Rat.cast_sum /-
@[simp, norm_cast]
theorem cast_sum (s : Finset ι) (f : ι → ℚ) : (↑(∑ i in s, f i) : α) = ∑ i in s, f i :=
  map_sum (Rat.castHom α) _ _
#align rat.cast_sum Rat.cast_sum
-/

#print Rat.cast_list_prod /-
@[simp, norm_cast]
theorem cast_list_prod (s : List ℚ) : (↑s.Prod : α) = (s.map coe).Prod :=
  map_list_prod (Rat.castHom α) _
#align rat.cast_list_prod Rat.cast_list_prod
-/

end WithDivRing

section Field

variable [Field α] [CharZero α]

#print Rat.cast_multiset_prod /-
@[simp, norm_cast]
theorem cast_multiset_prod (s : Multiset ℚ) : (↑s.Prod : α) = (s.map coe).Prod :=
  map_multiset_prod (Rat.castHom α) _
#align rat.cast_multiset_prod Rat.cast_multiset_prod
-/

#print Rat.cast_prod /-
@[simp, norm_cast]
theorem cast_prod (s : Finset ι) (f : ι → ℚ) : (↑(∏ i in s, f i) : α) = ∏ i in s, f i :=
  map_prod (Rat.castHom α) _ _
#align rat.cast_prod Rat.cast_prod
-/

end Field

end Rat

