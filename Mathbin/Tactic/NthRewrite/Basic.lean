import Mathbin.Meta.ExprLens

namespace Tactic

open Expr

namespace NthRewrite

/--  Configuration options for nth_rewrite. -/
unsafe structure cfg extends rewrite_cfg where
  try_simp : Bool := ff
  discharger : tactic Unit := skip
  simplifier : expr → tactic (expr × expr) := fun e => failed

/--  A data structure to track rewrites of subexpressions.
The field `exp` contains the new expression,
while `proof` contains a proof that `exp` is equivalent to the expression that was rewritten. -/
unsafe structure tracked_rewrite where
  exp : expr
  proof : tactic expr
  addr : Option (List ExprLens.Dir)

namespace TrackedRewrite

/--  Postprocess a tracked rewrite into a pair
of a rewritten expression and a proof witness of the rewrite. -/
unsafe def eval (rw : tracked_rewrite) : tactic (expr × expr) := do
  let prf ← rw.proof
  return (rw.exp, prf)

end TrackedRewrite

end NthRewrite

end Tactic

