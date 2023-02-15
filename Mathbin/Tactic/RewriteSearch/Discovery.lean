/-
Copyright (c) 2020 Kevin Lacker, Keeley Hoek, Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Keeley Hoek, Scott Morrison

! This file was ported from Lean 3 source module tactic.rewrite_search.discovery
! leanprover-community/mathlib commit 369525b73f229ccd76a6ec0e0e0bf2be57599768
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.NthRewrite.Default
import Mathbin.Tactic.RewriteSearch.Types

/-!
# Generating a list of rewrites to use as steps in rewrite search.
-/


namespace Tactic.RewriteSearch

open Tactic Tactic.Interactive Tactic.RewriteSearch

/-- Convert a list of expressions into a list of rules. The difference is that a rule
includes a flag for direction, so this simply includes each expression twice,
once in each direction.
-/
private unsafe def rules_from_exprs (l : List expr) : List (expr × Bool) :=
  (l.map fun e => (e, false)) ++ l.map fun e => (e, true)
#align tactic.rewrite_search.rules_from_exprs tactic.rewrite_search.rules_from_exprs

-- failed to format: unknown constant 'term.pseudo.antiquot'
/-- Returns true if expression is an equation or iff. -/ private unsafe
  def
    is_acceptable_rewrite
    : expr → Bool
    | expr.pi n bi d b => is_acceptable_rewrite b
      | q( $ ( a ) = $ ( b ) ) => true
      | q( $ ( a ) ↔ $ ( b ) ) => true
      | _ => false
#align tactic.rewrite_search.is_acceptable_rewrite tactic.rewrite_search.is_acceptable_rewrite

/-- Returns true if the expression is an equation or iff and has no metavariables. -/
private unsafe def is_acceptable_hyp (r : expr) : tactic Bool := do
  let t ← infer_type r >>= whnf
  return <| is_acceptable_rewrite t ∧ ¬t
#align tactic.rewrite_search.is_acceptable_hyp tactic.rewrite_search.is_acceptable_hyp

/-- Collect all hypotheses in the local context that are usable as rewrite rules. -/
private unsafe def rules_from_hyps : tactic (List (expr × Bool)) := do
  let hyps ← local_context
  rules_from_exprs <$> hyps is_acceptable_hyp
#align tactic.rewrite_search.rules_from_hyps tactic.rewrite_search.rules_from_hyps

/-- Use this attribute to make `rewrite_search` use this definition during search. -/
@[user_attribute]
unsafe def rewrite_search_attr : user_attribute
    where
  Name := `rewrite
  descr := "declare that this definition should be considered by `rewrite_search`"
#align tactic.rewrite_search.rewrite_search_attr tactic.rewrite_search.rewrite_search_attr

/-- Gather rewrite rules from lemmas explicitly tagged with `rewrite. -/
private unsafe def rules_from_rewrite_attr : tactic (List (expr × Bool)) := do
  let names ← attribute.get_instances `rewrite
  rules_from_exprs <$> names mk_const
#align tactic.rewrite_search.rules_from_rewrite_attr tactic.rewrite_search.rules_from_rewrite_attr

/-- Collect rewrite rules to use from the environment.
-/
unsafe def collect_rules : tactic (List (expr × Bool)) := do
  let from_attr ← rules_from_rewrite_attr
  let from_hyps ← rules_from_hyps
  return <| from_attr ++ from_hyps
#align tactic.rewrite_search.collect_rules tactic.rewrite_search.collect_rules

open Tactic.NthRewrite Tactic.NthRewrite.Congr

/-- Constructing our rewrite structure from the `tracked_rewrite` provided by `nth_rewrite`.
rule_index is the index of the rule used from the rules provided.
tracked is an (index, tracked_rewrite) pair for the element of `all_rewrites exp rule` we used.
-/
private unsafe def from_tracked (rule_index : ℕ) (tracked : ℕ × tracked_rewrite) : rewrite := do
  let (rw_index, rw) := tracked
  let h : how := ⟨rule_index, rw_index, rw.addr⟩
  ⟨rw, rw, h⟩
#align tactic.rewrite_search.from_tracked tactic.rewrite_search.from_tracked

/-- Get all rewrites that start at the given expression and use the given rewrite rule.
-/
private unsafe def rewrites_for_rule (exp : expr) (cfg : config) (numbered_rule : ℕ × expr × Bool) :
    tactic (List rewrite) := do
  let (rule_index, rule) := numbered_rule
  let tracked ← all_rewrites exp rule cfg.to_cfg
  return (List.map (from_tracked rule_index) tracked)
#align tactic.rewrite_search.rewrites_for_rule tactic.rewrite_search.rewrites_for_rule

/-- Get all rewrites that start at the given expression and use one of the given rewrite rules.
-/
unsafe def get_rewrites (rules : List (expr × Bool)) (exp : expr) (cfg : config) :
    tactic (Buffer rewrite) := do
  let lists ← List.mapM (rewrites_for_rule exp cfg) rules.enum
  return (List.foldl Buffer.appendList Buffer.nil Lists)
#align tactic.rewrite_search.get_rewrites tactic.rewrite_search.get_rewrites

end Tactic.RewriteSearch

