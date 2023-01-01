/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

! This file was ported from Lean 3 source module tactic.project_dir
! leanprover-community/mathlib commit ffc3730d545623aedf5d5bd46a3153cbf41f6c2c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/

/-!

# Project directory locator

We use the dummy declaration in this file to locate the project directory of mathlib.

-/


/-- This is a dummy declaration that is used to determine the project folder of mathlib, using the
  tactic `tactic.decl_olean`. This is used in `tactic.get_mathlib_dir`. -/
theorem mathlib_dir_locator : True :=
  trivial
#align mathlib_dir_locator mathlib_dir_locator

