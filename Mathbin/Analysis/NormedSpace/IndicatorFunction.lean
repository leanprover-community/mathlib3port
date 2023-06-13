/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov

! This file was ported from Lean 3 source module analysis.normed_space.indicator_function
! leanprover-community/mathlib commit 69c6a5a12d8a2b159f20933e60115a4f2de62b58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Normed.Group.Basic
import Mathbin.Algebra.IndicatorFunction

/-!
# Indicator function and norm

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains a few simple lemmas about `set.indicator` and `norm`.

## Tags
indicator, norm
-/


variable {α E : Type _} [SeminormedAddCommGroup E] {s t : Set α} (f : α → E) (a : α)

open Set

#print norm_indicator_eq_indicator_norm /-
theorem norm_indicator_eq_indicator_norm : ‖indicator s f a‖ = indicator s (fun a => ‖f a‖) a :=
  flip congr_fun a (indicator_comp_of_zero norm_zero).symm
#align norm_indicator_eq_indicator_norm norm_indicator_eq_indicator_norm
-/

#print nnnorm_indicator_eq_indicator_nnnorm /-
theorem nnnorm_indicator_eq_indicator_nnnorm :
    ‖indicator s f a‖₊ = indicator s (fun a => ‖f a‖₊) a :=
  flip congr_fun a (indicator_comp_of_zero nnnorm_zero).symm
#align nnnorm_indicator_eq_indicator_nnnorm nnnorm_indicator_eq_indicator_nnnorm
-/

#print norm_indicator_le_of_subset /-
theorem norm_indicator_le_of_subset (h : s ⊆ t) (f : α → E) (a : α) :
    ‖indicator s f a‖ ≤ ‖indicator t f a‖ :=
  by
  simp only [norm_indicator_eq_indicator_norm]
  exact indicator_le_indicator_of_subset ‹_› (fun _ => norm_nonneg _) _
#align norm_indicator_le_of_subset norm_indicator_le_of_subset
-/

#print indicator_norm_le_norm_self /-
theorem indicator_norm_le_norm_self : indicator s (fun a => ‖f a‖) a ≤ ‖f a‖ :=
  indicator_le_self' (fun _ _ => norm_nonneg _) a
#align indicator_norm_le_norm_self indicator_norm_le_norm_self
-/

#print norm_indicator_le_norm_self /-
theorem norm_indicator_le_norm_self : ‖indicator s f a‖ ≤ ‖f a‖ := by
  rw [norm_indicator_eq_indicator_norm]; apply indicator_norm_le_norm_self
#align norm_indicator_le_norm_self norm_indicator_le_norm_self
-/

