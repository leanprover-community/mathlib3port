/-
Copyright (c) 2018 Keeley Hoek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek, Scott Morrison
-/
import Mathbin.Tactic.Core

open Tactic

inductive Side
  | L
  | R
  deriving DecidableEq, Inhabited
#align side Side

def Side.other : Side → Side
  | Side.L => Side.R
  | Side.R => Side.L
#align side.other Side.other

def Side.toString : Side → String
  | Side.L => "L"
  | Side.R => "R"
#align side.to_string Side.toString

instance : ToString Side :=
  ⟨Side.toString⟩

namespace Tactic.RewriteAll

unsafe structure cfg extends RewriteCfg where
  try_simp : Bool := false
  discharger : tactic Unit := skip
  -- Warning: rewrite_search can't produce tactic scripts when the simplifier is used.
  simplifier : expr → tactic (expr × expr) := fun e => failed
#align tactic.rewrite_all.cfg tactic.rewrite_all.cfg

unsafe structure tracked_rewrite where
  exp : expr
  proof : tactic expr
  -- If `addr` is not provided by the underlying implementation of `rewrite_all` (i.e. kabstract)
  -- `rewrite_search` will not be able to produce tactic scripts.
  addr : Option (List Side)
#align tactic.rewrite_all.tracked_rewrite tactic.rewrite_all.tracked_rewrite

namespace TrackedRewrite

unsafe def eval (rw : tracked_rewrite) : tactic (expr × expr) := do
  let prf ← rw.proof
  return (rw, prf)
#align tactic.rewrite_all.tracked_rewrite.eval tactic.rewrite_all.tracked_rewrite.eval

unsafe def replace_target (rw : tracked_rewrite) : tactic Unit := do
  let (exp, prf) ← rw.eval
  tactic.replace_target exp prf
#align tactic.rewrite_all.tracked_rewrite.replace_target tactic.rewrite_all.tracked_rewrite.replace_target

private unsafe def replace_target_side (new_target lam : pexpr) (prf : expr) : tactic Unit := do
  let new_target ← to_expr new_target true false
  let prf' ← to_expr (pquote.1 (congr_arg (%%ₓlam) (%%ₓprf))) true false
  tactic.replace_target new_target prf'
#align tactic.rewrite_all.tracked_rewrite.replace_target_side tactic.rewrite_all.tracked_rewrite.replace_target_side

unsafe def replace_target_lhs (rw : tracked_rewrite) : tactic Unit := do
  let (new_lhs, prf) ← rw.eval
  let quote.1 ((%%ₓ_) = %%ₓrhs) ← target
  replace_target_side (pquote.1 ((%%ₓnew_lhs) = %%ₓrhs)) (pquote.1 fun L => L = %%ₓrhs) prf
#align tactic.rewrite_all.tracked_rewrite.replace_target_lhs tactic.rewrite_all.tracked_rewrite.replace_target_lhs

unsafe def replace_target_rhs (rw : tracked_rewrite) : tactic Unit := do
  let (new_rhs, prf) ← rw.eval
  let quote.1 ((%%ₓlhs) = %%ₓ_) ← target
  replace_target_side (pquote.1 ((%%ₓlhs) = %%ₓnew_rhs)) (pquote.1 fun R => (%%ₓlhs) = R) prf
#align tactic.rewrite_all.tracked_rewrite.replace_target_rhs tactic.rewrite_all.tracked_rewrite.replace_target_rhs

end TrackedRewrite

end Tactic.RewriteAll

