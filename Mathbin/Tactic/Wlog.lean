/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Johan Commelin, Reid Barton

! This file was ported from Lean 3 source module tactic.wlog
! leanprover-community/mathlib commit e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Core
import Mathbin.Tactic.Dependencies

/-!

# Without loss of generality tactic

The tactic `wlog h : P` will add an assumption `h : P` to the main goal,
and add a new goal that requires showing that the case `h : ¬ P` can be reduced to the case
where `P` holds (typically by symmetry).
The new goal will be placed at the top of the goal stack.

-/


namespace Tactic

/-- A helper function to retrieve the names of the first `n` arguments to a Pi-expression. -/
unsafe def take_pi_args : Nat → expr → List Name
  | n + 1, expr.pi h _ _ e => h :: take_pi_args n e
  | _, _ => []
#align tactic.take_pi_args tactic.take_pi_args

namespace Interactive

/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:38:34: unsupported: setup_tactic_parser -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `parser.many -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `parser.optional -/
/-- `wlog h : P` will add an assumption `h : P` to the main goal,
and add a side goal that requires showing that the case `h : ¬ P` can be reduced to the case
where `P` holds (typically by symmetry).

The side goal will be at the top of the stack. In this side goal, there will be two assumptions:
- `h : ¬ P`: the assumption that `P` does not hold
- `this`: which is the statement that in the old context `P` suffices to prove the goal.
  By default, the name `this` is used, but the idiom `with H` can be added to specify the name:
  `wlog h : P with H`.

Typically, it is useful to use the variant `wlog h : P generalizing x y`,
to revert certain parts of the context before creating the new goal.
In this way, the wlog-claim `this` can be applied to `x` and `y` in different orders
(exploiting symmetry, which is the typical use case).

By default, the entire context is reverted. -/
unsafe def wlog (H : parse ident) (t : parse (tk ":" *> texpr))
    (revert :
      parse (tk "generalizing" *> (none <$ tk "*" <|> some <$> parser.many ident) <|> pure none))
    (h : parse (parser.optional (tk "with" *> ident))) : tactic Unit := do
  let-- if there is no `with` clause, use `this` as default name
  h := h.getD `this
  let t ← i_to_expr ``(($(t) : Sort _))
  let-- compute which constants must be reverted (by default: everything)
    (num_generalized, goal, rctx)
    ←
    retrieve do
        assert_core H t
        swap
        let num_generalized
          ←-- use `revert_lst'` to ensure that the order of local constants in the context is preserved
            match revert with
            | none => revert_all
            | some revert => Prod.fst <$> (revert.mapM tactic.get_local >>= revert_lst')
        let goal ← target
        let ctx ← local_context
        return (num_generalized, goal, ctx)
  let ctx ← local_context
  let e ← tactic.assert h goal
  let goal ← target
  (take_pi_args num_generalized goal).reverse.mapM' fun h =>
      try (tactic.get_local h >>= tactic.clear)
  intron (num_generalized + 1)
  -- prove the easy branch of the side goal
    swap
  tactic.by_cases t H
  let H ← tactic.get_local H
  let L := ctx.filterₓ fun n => n ∉ rctx
  tactic.exact <| (e L).app H
#align tactic.interactive.wlog tactic.interactive.wlog

add_tactic_doc
  { Name := "wlog"
    category := DocCategory.tactic
    declNames := [`tactic.interactive.wlog]
    tags := ["logic"] }

end Interactive

end Tactic

