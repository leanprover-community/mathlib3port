/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module category_theory.concrete_category.elementwise
! leanprover-community/mathlib commit 369525b73f229ccd76a6ec0e0e0bf2be57599768
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Elementwise
import Mathbin.CategoryTheory.Limits.HasLimits
import Mathbin.CategoryTheory.Limits.Shapes.Kernels
import Mathbin.CategoryTheory.ConcreteCategory.Basic
import Mathbin.Tactic.FreshNames

/-!
In this file we provide various simp lemmas in its elementwise form via `tactic.elementwise`.
-/


open CategoryTheory CategoryTheory.Limits

attribute [elementwise]
  cone.w limit.lift_π limit.w cocone.w colimit.ι_desc colimit.w kernel.lift_ι cokernel.π_desc kernel.condition cokernel.condition

