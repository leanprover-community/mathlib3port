/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky

! This file was ported from Lean 3 source module tactic.swap_var
! leanprover-community/mathlib commit 26f081a2fb920140ed5bc5cc5344e84bcc7cb2b2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Interactive

/-!
# Swap bound variable tactic

This files defines a tactic `swap_var` whose main purpose is to be a weaker
version of `wlog` that juggles bound names.

It is a helper around the core tactic `rename`.

* `swap_var old new` renames all names named `old` to `new` and vice versa in the goal
  and all hypotheses.

```lean
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q :=
begin
  split,
  work_on_goal 1 { swap_var [P Q] },
  all_goals { exact ‹P› }
end
```

# See also
* `tactic.interactive.rename`
* `tactic.interactive.rename_var`

-/


namespace Tactic.Interactive

/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:38:34: unsupported: setup_tactic_parser -/
private unsafe def swap_arg_parser : lean.parser (Name × Name) :=
  Prod.mk <$> ident <*> (optional (tk "<->" <|> tk "↔") *> ident)
#align tactic.interactive.swap_arg_parser tactic.interactive.swap_arg_parser

private unsafe def swap_args_parser : lean.parser (List (Name × Name)) :=
  Functor.map (fun x => [x]) swap_arg_parser <|> tk "[" *> sep_by (tk ",") swap_arg_parser <* tk "]"
#align tactic.interactive.swap_args_parser tactic.interactive.swap_args_parser

/-- `swap_var [x y, P ↔ Q]` swaps the names `x` and `y`, `P` and `Q`.
Such a swapping can be used as a weak `wlog` if the tactic proofs use the same names.

```lean
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q :=
begin
  split,
  work_on_goal 1 { swap_var [P Q] },
  all_goals { exact ‹P› }
end
```
-/
unsafe def swap_var (renames : parse swap_args_parser) : tactic Unit := do
  renames fun e => do
      let n ← tactic.get_unused_name
      -- how to call `interactive.tactic.rename` here?
          propagate_tags <|
          tactic.rename_many <| native.rb_map.of_list [(e.1, n), (e.2, e.1)]
      propagate_tags <| tactic.rename_many <| native.rb_map.of_list [(n, e.2)]
  pure ()
#align tactic.interactive.swap_var tactic.interactive.swap_var

end Tactic.Interactive

add_tactic_doc
  { Name := "swap_var"
    category := DocCategory.tactic
    declNames := [`tactic.interactive.swap_var]
    tags := ["renaming"] }

