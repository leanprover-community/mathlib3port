/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov

! This file was ported from Lean 3 source module algebra.order.group.bounds
! leanprover-community/mathlib commit 198161d833f2c01498c39c266b0b3dbe2c7a8c07
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Bounds.Basic
import Mathbin.Algebra.Order.Group.Defs

/-!
# Least upper bound and the greatest lower bound in linear ordered additive commutative groups
-/


variable {α : Type _}

section LinearOrderedAddCommGroup

variable [LinearOrderedAddCommGroup α] {s : Set α} {a ε : α}

theorem IsGlb.exists_between_self_add (h : IsGlb s a) (hε : 0 < ε) : ∃ b ∈ s, a ≤ b ∧ b < a + ε :=
  h.exists_between <| lt_add_of_pos_right _ hε
#align is_glb.exists_between_self_add IsGlb.exists_between_self_add

theorem IsGlb.exists_between_self_add' (h : IsGlb s a) (h₂ : a ∉ s) (hε : 0 < ε) :
    ∃ b ∈ s, a < b ∧ b < a + ε :=
  h.exists_between' h₂ <| lt_add_of_pos_right _ hε
#align is_glb.exists_between_self_add' IsGlb.exists_between_self_add'

theorem IsLub.exists_between_sub_self (h : IsLub s a) (hε : 0 < ε) : ∃ b ∈ s, a - ε < b ∧ b ≤ a :=
  h.exists_between <| sub_lt_self _ hε
#align is_lub.exists_between_sub_self IsLub.exists_between_sub_self

theorem IsLub.exists_between_sub_self' (h : IsLub s a) (h₂ : a ∉ s) (hε : 0 < ε) :
    ∃ b ∈ s, a - ε < b ∧ b < a :=
  h.exists_between' h₂ <| sub_lt_self _ hε
#align is_lub.exists_between_sub_self' IsLub.exists_between_sub_self'

end LinearOrderedAddCommGroup

