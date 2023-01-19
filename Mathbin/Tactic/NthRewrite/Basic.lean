/-
Copyright (c) 2018 Keeley Hoek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Keeley Hoek, Scott Morrison

! This file was ported from Lean 3 source module tactic.nth_rewrite.basic
! leanprover-community/mathlib commit 509de852e1de55e1efa8eacfa11df0823f26f226
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Meta.ExprLens

namespace Tactic

open Expr

namespace NthRewrite

/-- Configuration options for nth_rewrite. -/
unsafe structure cfg extends RewriteCfg where
  try_simp : Bool := false
  discharger : tactic Unit := skip
  -- Warning: rewrite_search can't produce tactic scripts when the simplifier is used.
  simplifier : expr → tactic (expr × expr) := fun e => failed
#align tactic.nth_rewrite.cfg tactic.nth_rewrite.cfg

/-- A data structure to track rewrites of subexpressions.
The field `exp` contains the new expression,
while `proof` contains a proof that `exp` is equivalent to the expression that was rewritten. -/
unsafe structure tracked_rewrite where
  exp : expr
  proof : tactic expr
  -- If `addr` is not provided by the underlying implementation of `nth_rewrite` (i.e. kabstract)
  -- `rewrite_search` will not be able to produce tactic scripts.
  addr : Option (List ExprLens.Dir)
#align tactic.nth_rewrite.tracked_rewrite tactic.nth_rewrite.tracked_rewrite

namespace TrackedRewrite

/-- Postprocess a tracked rewrite into a pair
of a rewritten expression and a proof witness of the rewrite. -/
unsafe def eval (rw : tracked_rewrite) : tactic (expr × expr) := do
  let prf ← rw.proof
  return (rw, prf)
#align tactic.nth_rewrite.tracked_rewrite.eval tactic.nth_rewrite.tracked_rewrite.eval

end TrackedRewrite

end NthRewrite

end Tactic

