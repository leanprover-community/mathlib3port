/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison

! This file was ported from Lean 3 source module tactic.assert_exists
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Core
import Mathbin.Tactic.Lint.Basic

/-!
# User commands for assert the (non-)existence of declaration or instances.

These commands are used to enforce the independence of different parts of mathlib.

## Implementation notes

This file provides two linters that verify that things we assert do not _yet_ exist do _eventually_
exist. This works by creating declarations of the form:

* ``assert_not_exists._checked.<uniq> : name := `foo`` for `assert_not_exists foo`
* `assert_no_instance._checked.<uniq> := t` for `assert_instance t`

These declarations are then picked up by the linter and analyzed accordingly.
The `_` in the `_checked` prefix should hide them from doc-gen.
-/


section

/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:38:34: unsupported: setup_tactic_parser -/
open Tactic

/-- `assert_exists n` is a user command that asserts that a declaration named `n` exists
in the current import scope.

Be careful to use names (e.g. `rat`) rather than notations (e.g. `ℚ`).
-/
@[user_command]
unsafe def assert_exists (_ : parse <| tk "assert_exists") : lean.parser Unit := do
  let decl ← ident
  let d ← get_decl decl
  return ()
#align assert_exists assert_exists

/--
`assert_not_exists n` is a user command that asserts that a declaration named `n` *does not exist*
in the current import scope.

Be careful to use names (e.g. `rat`) rather than notations (e.g. `ℚ`).

It may be used (sparingly!) in mathlib to enforce plans that certain files
are independent of each other.

If you encounter an error on an `assert_not_exists` command while developing mathlib,
it is probably because you have introduced new import dependencies to a file.

In this case, you should refactor your work
(for example by creating new files rather than adding imports to existing files).
You should *not* delete the `assert_not_exists` statement without careful discussion ahead of time.
-/
@[user_command]
unsafe def assert_not_exists (_ : parse <| tk "assert_not_exists") : lean.parser Unit := do
  let decl ← ident
  let ff ← succeeds (get_decl decl) |
    fail f! "Declaration {decl} is not allowed to exist in this file."
  let n ← tactic.mk_fresh_name
  let marker := `assert_not_exists._checked.append (decl.append n)
  add_decl (declaration.defn marker [] q(Name) q(decl) default tt)
  pure ()
#align assert_not_exists assert_not_exists

/-- A linter for checking that the declarations marked `assert_not_exists` eventually exist. -/
unsafe def assert_not_exists.linter : linter
    where
  test d := do
    let n := d.to_name
    let tt ← pure (`assert_not_exists._checked.isPrefixOf n) |
      pure none
    let declaration.defn _ _ q(Name) val _ _ ← pure d
    let n ← tactic.eval_expr Name val
    let tt ← succeeds (get_decl n) |
      pure (some (f! "`{n}` does not ever exist").toString)
    pure none
  auto_decls := true
  no_errors_found := "All `assert_not_exists` declarations eventually exist."
  errors_found :=
    "The following declarations used in `assert_not_exists` never exist; perhaps there is a typo."
  is_fast := true
#align assert_not_exists.linter assert_not_exists.linter

/-- `assert_instance e` is a user command that asserts that an instance `e` is available
in the current import scope.

Example usage:
```
assert_instance semiring ℕ
```
-/
@[user_command]
unsafe def assert_instance (_ : parse <| tk "assert_instance") : lean.parser Unit := do
  let q ← texpr
  let e ← i_to_expr q
  mk_instance e
  return ()
#align assert_instance assert_instance

/-- `assert_no_instance e` is a user command that asserts that an instance `e` *is not available*
in the current import scope.

It may be used (sparingly!) in mathlib to enforce plans that certain files
are independent of each other.

If you encounter an error on an `assert_no_instance` command while developing mathlib,
it is probably because you have introduced new import dependencies to a file.

In this case, you should refactor your work
(for example by creating new files rather than adding imports to existing files).
You should *not* delete the `assert_no_instance` statement without careful discussion ahead of time.

Example usage:
```
assert_no_instance linear_ordered_field ℚ
```
-/
@[user_command]
unsafe def assert_no_instance (_ : parse <| tk "assert_no_instance") : lean.parser Unit := do
  let q ← texpr
  let e ← i_to_expr q
  let i ← try_core (mk_instance e)
  match i with
    | none => do
      let n ← tactic.mk_fresh_name
      let e_str ← toString <$> pp e
      let marker := (`assert_no_instance._checked.mk_string e_str).append n
      let et ← infer_type e
      let tt ← succeeds (get_decl marker) |
        add_decl (declaration.defn marker [] et e default tt)
      pure ()
    | some i =>
      (throwError "Instance `{(← i)} : {← e}` is not allowed to be found in this file." :
        tactic Unit)
#align assert_no_instance assert_no_instance

/-- A linter for checking that the declarations marked `assert_no_instance` eventually exist. -/
unsafe def assert_no_instance.linter : linter
    where
  test d := do
    let n := d.to_name
    let tt ← pure (`assert_no_instance._checked.isPrefixOf n) |
      pure none
    let declaration.defn _ _ _ val _ _ ← pure d
    let tt ← succeeds (tactic.mk_instance val) |
      (some ∘ format.to_string) <$> f!"No instance of `{← val}`"
    pure none
  auto_decls := true
  no_errors_found := "All `assert_no_instance` instances eventually exist."
  errors_found :=
    "The following typeclass instances used in `assert_no_instance` never exist; perhaps they " ++
      "are missing?"
  is_fast := false
#align assert_no_instance.linter assert_no_instance.linter

end

