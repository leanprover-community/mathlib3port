/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

! This file was ported from Lean 3 source module tactic.localized
! leanprover-community/mathlib commit 48085f140e684306f9e7da907cd5932056d1aded
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Meta.RbMap
import Mathbin.Tactic.Core

/-!
# Localized notation

This consists of two user-commands which allow you to declare notation and commands localized to a
locale.

See the tactic doc entry below for more information.

The code is inspired by code from Gabriel Ebner from the
[hott3 repository](https://github.com/gebner/hott3).
-/


open Lean Lean.Parser Interactive Tactic Native

@[user_attribute]
unsafe def localized_attr : user_attribute (rb_lmap Name String) Unit
    where
  Name := "_localized"
  descr := "(interal) attribute that flags localized commands"
  parser := failed
  cache_cfg :=
    ⟨fun ns => do
      let dcls ← ns.mapM fun n => mk_const n >>= eval_expr (Name × String)
      return <| rb_lmap.of_list dcls, []⟩
#align localized_attr localized_attr

/-- Get all commands in the given locale and return them as a list of strings -/
unsafe def get_localized (ns : List Name) : tactic (List String) := do
  let m ← localized_attr.get_cache
  ns
      (fun l nm =>
        match m nm with
        | [] => fail f! "locale {nm} does not exist"
        | new_l => return <| l new_l)
      []
#align get_localized get_localized

/-- Execute all commands in the given locale -/
@[user_command]
unsafe def open_locale_cmd (_ : parse <| tk "open_locale") : parser Unit := do
  let ns ← many ident
  let cmds ← get_localized ns
  cmds emit_code_here
#align open_locale_cmd open_locale_cmd

/-- Add a new command to a locale and execute it right now.
  The new command is added as a declaration to the environment with name `_localized_decl.<number>`.
  This declaration has attribute `_localized` and as value a name-string pair. -/
@[user_command]
unsafe def localized_cmd (_ : parse <| tk "localized") : parser Unit := do
  let cmd ← parser.pexpr
  let cmd ← i_to_expr cmd
  let cmd ← eval_expr String cmd
  let cmd := "local " ++ cmd
  emit_code_here cmd
  tk "in"
  let nm ← ident
  let env ← get_env
  let dummy_decl_name :=
    mkNumName `_localized_decl ((String.hash (cmd ++ nm.toString) + env.fingerprint) % unsignedSz)
  add_decl
      (declaration.defn dummy_decl_name [] q(Name × String) (reflect (⟨nm, cmd⟩ : Name × String))
        (ReducibilityHints.regular 1 tt) ff)
  localized_attr dummy_decl_name Unit.unit tt
#align localized_cmd localized_cmd

/--
This consists of two user-commands which allow you to declare notation and commands localized to a
locale.

* Declare notation which is localized to a locale using:
```lean
localized "infix (name := my_add) ` ⊹ `:60 := my_add" in my.add
```

* After this command it will be available in the same section/namespace/file, just as if you wrote
  `local infix (name := my_add) ` ⊹ `:60 := my_add`

* You can open it in other places. The following command will declare the notation again as local
  notation in that section/namespace/file:
```lean
open_locale my.add
```

* More generally, the following will declare all localized notation in the specified locales.
```lean
open_locale locale1 locale2 ...
```

* You can also declare other localized commands, like local attributes
```lean
localized "attribute [simp] le_refl" in le
```

* To see all localized commands in a given locale, run:
```lean
run_cmd print_localized_commands [`my.add].
```

* To see a list of all locales with localized commands, run:
```lean
run_cmd do
  m ← localized_attr.get_cache,
  tactic.trace m.keys -- change to `tactic.trace m.to_list` to list all the commands in each locale
```

* Warning: You have to give full names of all declarations used in localized notation,
  so that the localized notation also works when the appropriate namespaces are not opened.

* Note: In mathlib, you should always provide names for localized notations using the
  `(name := ...)` parameter. This prevents issues if the localized notation overrides
  an existing notation when it gets opened.

* Warning: Due to limitations in the implementation, you cannot use `_` in localized notations.
  (Otherwise `open_locale foo` will fail if `foo` is already opened or partially opened.)
  Instead, you should use the `hole!` notation as a drop-in replacement. For example:
```lean
-- BAD
-- localized "infix (name := my_add) ` ⊹[` R `] ` := my_add _ R" in foo
-- GOOD
localized "infix (name := my_add) ` ⊹[` R `] ` := my_add hole! R" in foo
```
-/
add_tactic_doc
  { Name := "localized notation"
    category := DocCategory.cmd
    declNames := [`localized_cmd, `open_locale_cmd]
    tags := ["notation", "type classes"] }

/-- Print all commands in a given locale -/
unsafe def print_localized_commands (ns : List Name) : tactic Unit := do
  let cmds ← get_localized ns
  cmds trace
#align print_localized_commands print_localized_commands

-- mathport name: exprhole!
notation
  "hole!" =>-- This should be used instead of `_` inside localized commands,
  -- because otherwise `open_locale` will fail if some of the notations are already available.
  _

scoped[-- you can run `open_locale classical` to get the decidability of all propositions, and downgrade
-- the priority of decidability instances that make Lean run through all the algebraic hierarchy
-- whenever it wants to solve a decidability question
Classical] attribute [instance] Classical.propDecidable

scoped[Classical] attribute [instance] Eq.decidable

-- mathport name: parser.optional
scoped[Parser] postfix:1024 "?" => optional

-- mathport name: parser.many
scoped[Parser] postfix:1024 "*" => lean.parser.many

