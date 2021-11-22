
/-!

# Project directory locator

We use the dummy declaration in this file to locate the project directory of mathlib.

-/


/-- This is a dummy declaration that is used to determine the project folder of mathlib, using the
  tactic `tactic.decl_olean`. This is used in `tactic.get_mathlib_dir`. -/
theorem mathlib_dir_locator : True :=
  trivialₓ

