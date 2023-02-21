/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module tactic.pretty_cases
! leanprover-community/mathlib commit bd9851ca476957ea4549eb19b40e7b5ade9428cc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Core

/-!
# `pretty_cases` tactic

When using `induction` and `cases`, `pretty_cases` prints a `"Try
this:"` advice that shows how to structure the proof with
`case { ... }` commands.  In the following example, we apply induction on a
permutation assumption about lists. `pretty_cases` gives us a proof
skeleton that explicit selects the branches and explicit names the
new local constants:

```lean
example {α} (xs ys : list α) (h : xs ~ ys) : true :=
begin
  induction h,
  pretty_cases,
    -- Try this:
    --   case list.perm.nil :
    --   { admit },
    --   case list.perm.cons : h_x h_l₁ h_l₂ h_a h_ih
    --   { admit },
    --   case list.perm.swap : h_x h_y h_l
    --   { admit },
    --   case list.perm.trans : h_l₁ h_l₂ h_l₃ h_a h_a_1 h_ih_a h_ih_a_1
    --   { admit },
end
```

## Main definitions

 * `pretty_cases_advice` return `pretty_cases` advice without printing it
 * `pretty_cases` main tactic
-/


namespace Tactic

/-- Query the proof goal and print the skeleton of a proof by cases. -/
unsafe def pretty_cases_advice : tactic String :=
  retrieve do
    let gs ← get_goals
    let cases ←
      gs.mapM fun g => do
          let t : List Name ← get_tag g
          let vs := t.tail
          let ⟨vs, ts⟩ := vs.spanₓ fun n => Name.lastString n = "_arg"
          set_goals [g]
          let ls ← local_context
          let m :=
            native.rb_map.of_list <| (ls.map expr.local_uniq_name).zip (ls.map expr.local_pp_name)
          let vs := vs.map fun v => (m.find v.getPrefix).getD `_
          let var_decls := String.intercalate " " <| vs.map toString
          let var_decls := if vs.Empty then "" else " : " ++ var_decls
          pure
              s! "  case {ts }{var_decls}
                  \{ admit }}"
    let cases := String.intercalate ",\n" cases
    pure
        s! "Try this:
          {cases}"
#align tactic.pretty_cases_advice tactic.pretty_cases_advice

namespace Interactive

/-- Query the proof goal and print the skeleton of a proof by
cases.

For example, let us consider the following proof:

```lean
example {α} (xs ys : list α) (h : xs ~ ys) : true :=
begin
  induction h,
  pretty_cases,
    -- Try this:
    --   case list.perm.nil :
    --   { admit },
    --   case list.perm.cons : h_x h_l₁ h_l₂ h_a h_ih
    --   { admit },
    --   case list.perm.swap : h_x h_y h_l
    --   { admit },
    --   case list.perm.trans : h_l₁ h_l₂ h_l₃ h_a h_a_1 h_ih_a h_ih_a_1
    --   { admit },
end
```

The output helps the user layout the cases and rename the
introduced variables.
-/
unsafe def pretty_cases : tactic Unit :=
  pretty_cases_advice >>= trace
#align tactic.interactive.pretty_cases tactic.interactive.pretty_cases

add_tactic_doc
  { Name := "pretty_cases"
    category := DocCategory.tactic
    declNames := [`` tactic.interactive.pretty_cases]
    tags := ["context management", "goal management"] }

end Interactive

end Tactic

