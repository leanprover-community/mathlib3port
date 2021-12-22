import Mathbin.Tactic.Core

open Tactic

-- ././Mathport/Syntax/Translate/Basic.lean:833:9: unsupported derive handler decidable_eq
-- ././Mathport/Syntax/Translate/Basic.lean:833:9: unsupported derive handler inhabited
inductive Side
  | L
  | R
  deriving [anonymous], [anonymous]

def Side.other : Side → Side
  | Side.L => Side.R
  | Side.R => Side.L

def Side.toString : Side → Stringₓ
  | Side.L => "L"
  | Side.R => "R"

instance : HasToString Side :=
  ⟨Side.toString⟩

namespace Tactic.RewriteAll

unsafe structure cfg extends rewrite_cfg where
  try_simp : Bool := ff
  discharger : tactic Unit := skip
  simplifier : expr → tactic (expr × expr) := fun e => failed

unsafe structure tracked_rewrite where
  exp : expr
  proof : tactic expr
  addr : Option (List Side)

namespace TrackedRewrite

unsafe def eval (rw : tracked_rewrite) : tactic (expr × expr) := do
  let prf ← rw.proof
  return (rw.exp, prf)

unsafe def replace_target (rw : tracked_rewrite) : tactic Unit := do
  let (exp, prf) ← rw.eval
  tactic.replace_target exp prf

private unsafe def replace_target_side (new_target lam : pexpr) (prf : expr) : tactic Unit := do
  let new_target ← to_expr new_target tt ff
  let prf' ← to_expr (pquote.1 (congr_argₓ (%%ₓlam) (%%ₓprf))) tt ff
  tactic.replace_target new_target prf'

unsafe def replace_target_lhs (rw : tracked_rewrite) : tactic Unit := do
  let (new_lhs, prf) ← rw.eval
  let quote.1 ((%%ₓ_) = %%ₓrhs) ← target
  replace_target_side (pquote.1 ((%%ₓnew_lhs) = %%ₓrhs)) (pquote.1 fun L => L = %%ₓrhs) prf

unsafe def replace_target_rhs (rw : tracked_rewrite) : tactic Unit := do
  let (new_rhs, prf) ← rw.eval
  let quote.1 ((%%ₓlhs) = %%ₓ_) ← target
  replace_target_side (pquote.1 ((%%ₓlhs) = %%ₓnew_rhs)) (pquote.1 fun R => (%%ₓlhs) = R) prf

end TrackedRewrite

end Tactic.RewriteAll

