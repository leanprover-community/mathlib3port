/-
Copyright (c) 2017 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich

! This file was ported from Lean 3 source module tactic.find
! leanprover-community/mathlib commit 740acc0e6f9adf4423f92a485d0456fc271482da
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Core

open Expr

open Interactive

open Lean.Parser

open Tactic

private unsafe def match_subexpr (p : pattern) : expr → tactic (List expr)
  | e =>
    Prod.snd <$> match_pattern p e <|>
      match e with
      | app e₁ e₂ => match_subexpr e₁ <|> match_subexpr e₂
      | pi _ _ _ b => mk_fresh_name >>= match_subexpr ∘ b.instantiate_var ∘ mk_local
      | lam _ _ _ b => mk_fresh_name >>= match_subexpr ∘ b.instantiate_var ∘ mk_local
      | _ => failed
#align match_subexpr match_subexpr

private unsafe def match_exact : pexpr → expr → tactic (List expr)
  | p, e => do
    let app p₁ p₂ ← pure p |
      match_expr p e
    if pexpr.is_placeholder p₁ then -- `_ p` pattern ~> match `p` recursively
      do
        let p ← pexpr_to_pattern p₂
        match_subexpr p e
      else match_expr p e
#align match_exact match_exact

unsafe def expr.get_pis : expr → tactic (List expr × expr)
  | pi n bi d b => do
    let l ← mk_local' n bi d
    let (pis, b) ← expr.get_pis (b.instantiate_var l)
    pure (d :: pis, b)
  | e => pure ([], e)
#align expr.get_pis expr.get_pis

unsafe def pexpr.get_uninst_pis : pexpr → tactic (List pexpr × pexpr)
  | pi n bi d b => do
    let (pis, b) ← pexpr.get_uninst_pis b
    pure (d :: pis, b)
  | e => pure ([], e)
#align pexpr.get_uninst_pis pexpr.get_uninst_pis

private unsafe def match_hyps : List pexpr → List expr → List expr → tactic Unit
  | p :: ps, old_hyps, h :: new_hyps => do
    let some _ ← try_core (match_exact p h) |
      match_hyps (p :: ps) (h :: old_hyps) new_hyps
    match_hyps ps [] (old_hyps ++ new_hyps)
  | [], _, _ => skip
  | _ :: _, _, [] => failed
#align match_hyps match_hyps

private unsafe def match_sig (p : pexpr) (e : expr) : tactic Unit := do
  let (p_pis, p) ← p.get_uninst_pis
  let (pis, e) ← e.get_pis
  match_exact p e
  match_hyps p_pis [] pis
#align match_sig match_sig

private unsafe def trace_match (pat : pexpr) (ty : expr) (n : Name) : tactic Unit :=
  try do
    guard ¬n
    match_sig pat ty
    let ty ← pp ty
    trace f! "{n }: {ty}"
#align trace_match trace_match

/-- The `find` command from `tactic.find` allows to find definitions lemmas using
pattern matching on the type. For instance:

```lean
import tactic.find

run_cmd tactic.skip

#find _ + _ = _ + _
#find (_ : ℕ) + _ = _ + _
#find ℕ → ℕ
```

The tactic `library_search` is an alternate way to find lemmas in the library.
-/
@[user_command]
unsafe def find_cmd (_ : parse <| tk "#find") : lean.parser Unit := do
  let pat ← lean.parser.pexpr 0
  let env ← get_env
  env () fun d _ =>
      match d with
      | declaration.thm n _ ty _ => trace_match pat ty n
      | declaration.defn n _ ty _ _ _ => trace_match pat ty n
      | _ => skip
#align find_cmd find_cmd

add_tactic_doc
  { Name := "#find"
    category := DocCategory.cmd
    declNames := [`find_cmd]
    tags := ["search"] }

-- #find (_ : nat) + _ = _ + _
-- #find _ + _ = _ + _
-- #find _ (_ + _) → _ + _ = _ + _   -- TODO(Mario): no results
-- #find add_group _ → _ + _ = _ + _ -- TODO(Mario): no results
