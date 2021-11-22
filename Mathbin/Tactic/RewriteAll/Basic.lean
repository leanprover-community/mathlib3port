import Mathbin.Data.Mllist 
import Mathbin.Tactic.Core

open Tactic

-- error in Tactic.RewriteAll.Basic: ././Mathport/Syntax/Translate/Basic.lean:702:9: unsupported derive handler decidable_eq
@[derive #[expr decidable_eq], derive #[expr inhabited]] inductive side
| L
| R

def Side.other : Side → Side
| Side.L => Side.R
| Side.R => Side.L

def Side.toString : Side → Stringₓ
| Side.L => "L"
| Side.R => "R"

instance  : HasToString Side :=
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

unsafe def eval (rw : tracked_rewrite) : tactic (expr × expr) :=
  do 
    let prf ← rw.proof 
    return (rw.exp, prf)

unsafe def replace_target (rw : tracked_rewrite) : tactic Unit :=
  do 
    let (exp, prf) ← rw.eval 
    tactic.replace_target exp prf

private unsafe def replace_target_side (new_target lam : pexpr) (prf : expr) : tactic Unit :=
  do 
    let new_target ← to_expr new_target tt ff 
    let prf' ← to_expr (pquote congr_argₓ (%%lam) (%%prf)) tt ff 
    tactic.replace_target new_target prf'

unsafe def replace_target_lhs (rw : tracked_rewrite) : tactic Unit :=
  do 
    let (new_lhs, prf) ← rw.eval 
    let quote (%%_) = %%rhs ← target 
    replace_target_side (pquote (%%new_lhs) = %%rhs) (pquote fun L => L = %%rhs) prf

unsafe def replace_target_rhs (rw : tracked_rewrite) : tactic Unit :=
  do 
    let (new_rhs, prf) ← rw.eval 
    let quote (%%lhs) = %%_ ← target 
    replace_target_side (pquote (%%lhs) = %%new_rhs) (pquote fun R => (%%lhs) = R) prf

end TrackedRewrite

end Tactic.RewriteAll

