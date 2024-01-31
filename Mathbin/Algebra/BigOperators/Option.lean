/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Algebra.BigOperators.Basic
import Data.Finset.Option

#align_import algebra.big_operators.option from "leanprover-community/mathlib"@"327c3c0d9232d80e250dc8f65e7835b82b266ea5"

/-!
# Lemmas about products and sums over finite sets in `option α`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove formulas for products and sums over `finset.insert_none s` and
`finset.erase_none s`.
-/


open scoped BigOperators

open Function

namespace Finset

variable {α M : Type _} [CommMonoid M]

#print Finset.prod_insertNone /-
@[simp, to_additive]
theorem prod_insertNone (f : Option α → M) (s : Finset α) :
    ∏ x in s.insertNone, f x = f none * ∏ x in s, f (some x) := by simp [insert_none]
#align finset.prod_insert_none Finset.prod_insertNone
#align finset.sum_insert_none Finset.sum_insertNone
-/

#print Finset.prod_eraseNone /-
@[to_additive]
theorem prod_eraseNone (f : α → M) (s : Finset (Option α)) :
    ∏ x in s.eraseNone, f x = ∏ x in s, Option.elim' 1 f x := by classical
#align finset.prod_erase_none Finset.prod_eraseNone
#align finset.sum_erase_none Finset.sum_eraseNone
-/

end Finset

