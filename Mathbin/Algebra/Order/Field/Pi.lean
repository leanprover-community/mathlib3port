/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module algebra.order.field.pi
! leanprover-community/mathlib commit 327c3c0d9232d80e250dc8f65e7835b82b266ea5
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Field.Basic
import Mathbin.Data.Fintype.Lattice

/-!
# Lemmas about (finite domain) functions into fields.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We split this from `algebra.order.field.basic` to avoid importing the finiteness hierarchy there.
-/


variable {α ι : Type _} [LinearOrderedSemifield α]

#print Pi.exists_forall_pos_add_lt /-
theorem Pi.exists_forall_pos_add_lt [ExistsAddOfLE α] [Finite ι] {x y : ι → α}
    (h : ∀ i, x i < y i) : ∃ ε, 0 < ε ∧ ∀ i, x i + ε < y i :=
  by
  cases nonempty_fintype ι
  cases isEmpty_or_nonempty ι
  · exact ⟨1, zero_lt_one, isEmptyElim⟩
  choose ε hε hxε using fun i => exists_pos_add_of_lt' (h i)
  obtain rfl : x + ε = y := funext hxε
  have hε : 0 < finset.univ.inf' Finset.univ_nonempty ε := (Finset.lt_inf'_iff _).2 fun i _ => hε _
  exact
    ⟨_, half_pos hε, fun i =>
      add_lt_add_left ((half_lt_self hε).trans_le <| Finset.inf'_le _ <| Finset.mem_univ _) _⟩
#align pi.exists_forall_pos_add_lt Pi.exists_forall_pos_add_lt
-/

