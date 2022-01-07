import Mathbin.Tactic.Interactive

/-!
# `dec_trivial` tactic

The `dec_trivial` tactic tries to use decidability to prove a goal.
It is basically a glorified wrapper around `exact dec_trivial`.

There is an extra option to make it a little bit smarter:
`dec_trivial!` will revert all hypotheses on which the target depends,
before it tries `exact dec_trivial`.
-/


open Tactic.Interactive

setup_tactic_parser

-- ././Mathport/Syntax/Translate/Basic.lean:705:4: warning: unsupported notation `«expr ?»
/-- `dec_trivial` tries to use decidability to prove a goal
(i.e., using `exact dec_trivial`).
The variant `dec_trivial!` will revert all hypotheses on which the target depends,
before it tries `exact dec_trivial`.

Example:
```lean
example (n : ℕ) (h : n < 2) : n = 0 ∨ n = 1 :=
by dec_trivial!
```
-/
unsafe def tactic.interactive.dec_trivial (revert_deps : parse («expr ?» (tk "!"))) : tactic Unit :=
  if revert_deps.is_some then revert_target_deps; tactic.exact_dec_trivial else tactic.exact_dec_trivial

add_tactic_doc
  { Name := "dec_trivial", category := DocCategory.tactic, declNames := [`tactic.interactive.dec_trivial],
    tags := ["basic", "finishing"] }

