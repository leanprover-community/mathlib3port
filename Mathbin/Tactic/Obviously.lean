import Mathbin.Tactic.Tidy 
import Mathbin.Tactic.Replacer

/-!
# The `obviously` tactic

This file sets up a tactic called `obviously`,
which is subsequently used throughout the category theory library
as an `auto_param` to discharge easy proof obligations when building structures.

In this file, we set up `obviously` as a "replacer" tactic,
whose implementation can be modified after the fact.
Then we set the default implementation to be `tidy`.

## Implementation note
At present we don't actually take advantage of the replacer mechanism in mathlib.
In the past it had been used by an external category theory library which wanted to incorporate
`rewrite_search` as part of `obviously`.
-/


def_replacer obviously

/--
The default implementation of `obviously`
discharges any goals which contain `sorry` in their type using `sorry`,
and then calls `tidy`.
-/
@[obviously]
unsafe def obviously' :=
  tactic.sorry_if_contains_sorry <|>
    tactic.tidy <|>
      tactic.fail
        ("`obviously` failed to solve a subgoal.\n" ++
          "You may need to explicitly provide a proof of the corresponding structure field.")

