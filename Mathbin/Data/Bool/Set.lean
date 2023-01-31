/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module data.bool.set
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Bool.Basic
import Mathbin.Data.Set.Image

/-!
# Booleans and set operations

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains two trivial lemmas about `bool`, `set.univ`, and `set.range`.
-/


open Set

namespace Bool

#print Bool.univ_eq /-
@[simp]
theorem univ_eq : (univ : Set Bool) = {false, true} :=
  (eq_univ_of_forall Bool.dichotomy).symm
#align bool.univ_eq Bool.univ_eq
-/

#print Bool.range_eq /-
@[simp]
theorem range_eq {α : Type _} (f : Bool → α) : range f = {f false, f true} := by
  rw [← image_univ, univ_eq, image_pair]
#align bool.range_eq Bool.range_eq
-/

end Bool

