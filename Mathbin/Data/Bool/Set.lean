/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module data.bool.set
! leanprover-community/mathlib commit 0a0ec35061ed9960bf0e7ffb0335f44447b58977
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

/- warning: bool.compl_singleton -> Bool.compl_singleton is a dubious translation:
lean 3 declaration is
  forall (b : Bool), Eq.{1} (Set.{0} Bool) (HasCompl.compl.{0} (Set.{0} Bool) (BooleanAlgebra.toHasCompl.{0} (Set.{0} Bool) (Set.booleanAlgebra.{0} Bool)) (Singleton.singleton.{0, 0} Bool (Set.{0} Bool) (Set.hasSingleton.{0} Bool) b)) (Singleton.singleton.{0, 0} Bool (Set.{0} Bool) (Set.hasSingleton.{0} Bool) (not b))
but is expected to have type
  forall (b : Bool), Eq.{1} (Set.{0} Bool) (HasCompl.compl.{0} (Set.{0} Bool) (BooleanAlgebra.toHasCompl.{0} (Set.{0} Bool) (Set.instBooleanAlgebraSet.{0} Bool)) (Singleton.singleton.{0, 0} Bool (Set.{0} Bool) (Set.instSingletonSet.{0} Bool) b)) (Singleton.singleton.{0, 0} Bool (Set.{0} Bool) (Set.instSingletonSet.{0} Bool) (not b))
Case conversion may be inaccurate. Consider using '#align bool.compl_singleton Bool.compl_singletonₓ'. -/
@[simp]
theorem compl_singleton (b : Bool) : ({b}ᶜ : Set Bool) = {!b} :=
  ext fun _ => eq_not_iff.symm
#align bool.compl_singleton Bool.compl_singleton

end Bool

