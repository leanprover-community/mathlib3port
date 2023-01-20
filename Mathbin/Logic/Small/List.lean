/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module logic.small.list
! leanprover-community/mathlib commit 1126441d6bccf98c81214a0780c73d499f6721fe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Small.Basic
import Mathbin.Data.Vector.Basic

/-!
# Instances for `small (list α)` and `small (vector α)`.

These must not be in `logic.small.basic` as this is very low in the import hierarchy,
and is used by category theory files which do not need everything imported by `data.vector.basic`.
-/


universe u v

#print smallVector /-
instance smallVector {α : Type v} {n : ℕ} [Small.{u} α] : Small.{u} (Vector α n) :=
  small_of_injective (Equiv.vectorEquivFin α n).Injective
#align small_vector smallVector
-/

#print smallList /-
instance smallList {α : Type v} [Small.{u} α] : Small.{u} (List α) :=
  by
  let e : (Σn, Vector α n) ≃ List α := Equiv.sigmaFiberEquiv List.length
  exact small_of_surjective e.surjective
#align small_list smallList
-/

