/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

#align_import tactic.project_dir from "leanprover-community/mathlib"@"29079ba8bc53a8465448a577eb2fc41932b02301"

/-!

# Project directory locator

We use the dummy declaration in this file to locate the project directory of mathlib.

-/


/-- This is a dummy declaration that is used to determine the project folder of mathlib, using the
  tactic `tactic.decl_olean`. This is used in `tactic.get_mathlib_dir`. -/
theorem mathlib_dir_locator : True :=
  trivial
#align mathlib_dir_locator mathlib_dir_locator

