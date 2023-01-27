/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Robert Y. Lewis, Gabriel Ebner

! This file was ported from Lean 3 source module tactic.lint.basic
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Core

/-!
# Basic linter types and attributes

This file defines the basic types and attributes used by the linting
framework.  A linter essentially consists of a function
`declaration → tactic (option string)`, this function together with some
metadata is stored in the `linter` structure. We define two attributes:

 * `@[linter]` applies to a declaration of type `linter` and adds it to the default linter set.

 * `@[nolint linter_name]` omits the tagged declaration from being checked by
   the linter with name `linter_name`.
-/


open Tactic

/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:38:34: unsupported: setup_tactic_parser -/
section

attribute [local semireducible] reflected

/-- We store the list of nolint names as `@id (list name) (Prop simp_nf doc_blame has_coe_t)`

See Note [user attribute parameters]
-/
private unsafe def reflect_name_list : has_reflect (List Name)
  | ns => q((id $(expr.mk_app q(Prop) <| ns.map flip expr.const []) : List Name))
#align reflect_name_list reflect_name_list

private unsafe def parse_name_list (e : expr) : List Name :=
  e.app_arg.get_app_args.map expr.const_name
#align parse_name_list parse_name_list

attribute [local instance] reflect_name_list

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `parser.many -/
/-- Defines the user attribute `nolint` for skipping `#lint` -/
@[user_attribute]
unsafe def nolint_attr : user_attribute (name_map (List Name)) (List Name)
    where
  Name := "nolint"
  descr := "Do not report this declaration in any of the tests of `#lint`"
  after_set :=
    some fun n _ _ => do
      let ls@(_ :: _) ← parse_name_list <$> nolint_attr.get_param_untyped n |
        fail "you need to specify at least one linter to disable"
      skip
  cache_cfg :=
    { dependencies := []
      mk_cache :=
        List.foldlM
          (fun cache d =>
            native.rb_map.insert cache d <$> parse_name_list <$> nolint_attr.get_param_untyped d)
          mk_name_map }
  parser := parser.many ident
#align nolint_attr nolint_attr

end

add_tactic_doc
  { Name := "nolint"
    category := DocCategory.attr
    declNames := [`nolint_attr]
    tags := ["linting"] }

/-- `should_be_linted linter decl` returns true if `decl` should be checked
using `linter`, i.e., if there is no `nolint` attribute. -/
unsafe def should_be_linted (linter : Name) (decl : Name) : tactic Bool := do
  let c ← nolint_attr.get_cache
  pure <| linter ∉ (c decl).getOrElse []
#align should_be_linted should_be_linted

/-- A linting test for the `#lint` command.

`test` defines a test to perform on every declaration. It should never fail. Returning `none`
signifies a passing test. Returning `some msg` reports a failing test with error `msg`.

`no_errors_found` is the message printed when all tests are negative, and `errors_found` is printed
when at least one test is positive.

If `is_fast` is false, this test will be omitted from `#lint-`.

If `auto_decls` is true, this test will also be executed on automatically generated declarations.
-/
unsafe structure linter where
  test : declaration → tactic (Option String)
  no_errors_found : String
  errors_found : String
  is_fast : Bool := true
  auto_decls : Bool
#align linter linter

/-- Takes a list of names that resolve to declarations of type `linter`,
and produces a list of linters. -/
unsafe def get_linters (l : List Name) : tactic (List (Name × linter)) :=
  l.mmap fun n =>
    Prod.mk n.last <$> (mk_const n >>= eval_expr linter) <|> fail f! "invalid linter: {n}"
#align get_linters get_linters

/-- Defines the user attribute `linter` for adding a linter to the default set.
Linters should be defined in the `linter` namespace.
A linter `linter.my_new_linter` is referred to as `my_new_linter` (without the `linter` namespace)
when used in `#lint`.
-/
@[user_attribute]
unsafe def linter_attr : user_attribute Unit Unit
    where
  Name := "linter"
  descr := "Use this declaration as a linting test in #lint"
  after_set := some fun nm _ _ => mk_const nm >>= infer_type >>= unify q(linter)
#align linter_attr linter_attr

add_tactic_doc
  { Name := "linter"
    category := DocCategory.attr
    declNames := [`linter_attr]
    tags := ["linting"] }

