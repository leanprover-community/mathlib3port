/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Data.Bool.Basic
import Data.Set.Image

#align_import data.bool.set from "leanprover-community/mathlib"@"ed60ee25ed00d7a62a0d1e5808092e1324cee451"

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

#print Bool.compl_singleton /-
@[simp]
theorem compl_singleton (b : Bool) : ({b}ᶜ : Set Bool) = {!b} :=
  ext fun _ => eq_not_iff.symm
#align bool.compl_singleton Bool.compl_singleton
-/

end Bool

