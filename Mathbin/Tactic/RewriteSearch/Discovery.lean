import Mathbin.Tactic.NthRewrite.Default 
import Mathbin.Tactic.RewriteSearch.Types

/-!
# Generating a list of rewrites to use as steps in rewrite search.
-/


namespace Tactic.RewriteSearch

open Tactic Tactic.Interactive Tactic.RewriteSearch

/--
Convert a list of expressions into a list of rules. The difference is that a rule
includes a flag for direction, so this simply includes each expression twice,
once in each direction.
-/
private unsafe def rules_from_exprs (l : List expr) : List (expr × Bool) :=
  (l.map fun e => (e, ff)) ++ l.map fun e => (e, tt)

/-- Returns true if expression is an equation or iff. -/
private unsafe def is_acceptable_rewrite : expr → Bool
| expr.pi n bi d b => is_acceptable_rewrite b
| quote.1 ((%%ₓa) = %%ₓb) => tt
| quote.1 ((%%ₓa) ↔ %%ₓb) => tt
| _ => ff

/-- Returns true if the expression is an equation or iff and has no metavariables. -/
private unsafe def is_acceptable_hyp (r : expr) : tactic Bool :=
  do 
    let t ← infer_type r >>= whnf 
    return$ is_acceptable_rewrite t ∧ ¬t.has_meta_var

/-- Collect all hypotheses in the local context that are usable as rewrite rules. -/
private unsafe def rules_from_hyps : tactic (List (expr × Bool)) :=
  do 
    let hyps ← local_context 
    rules_from_exprs <$> hyps.mfilter is_acceptable_hyp

/-- Use this attribute to make `rewrite_search` use this definition during search. -/
@[user_attribute]
unsafe def rewrite_search_attr : user_attribute :=
  { Name := `rewrite, descr := "declare that this definition should be considered by `rewrite_search`" }

/-- Gather rewrite rules from lemmas explicitly tagged with `rewrite. -/
private unsafe def rules_from_rewrite_attr : tactic (List (expr × Bool)) :=
  do 
    let names ← attribute.get_instances `rewrite 
    rules_from_exprs <$> names.mmap mk_const

/--
Collect rewrite rules to use from the environment.
-/
unsafe def collect_rules : tactic (List (expr × Bool)) :=
  do 
    let from_attr ← rules_from_rewrite_attr 
    let from_hyps ← rules_from_hyps 
    return$ from_attr ++ from_hyps

open Tactic.NthRewrite Tactic.NthRewrite.Congr

/--
Constructing our rewrite structure from the `tracked_rewrite` provided by `nth_rewrite`.
rule_index is the index of the rule used from the rules provided.
tracked is an (index, tracked_rewrite) pair for the element of `all_rewrites exp rule` we used.
-/
private unsafe def from_tracked (rule_index : ℕ) (tracked : ℕ × tracked_rewrite) : rewrite :=
  do 
    let (rw_index, rw) := tracked 
    let h : how := ⟨rule_index, rw_index, rw.addr⟩
    ⟨rw.exp, rw.proof, h⟩

/--
Get all rewrites that start at the given expression and use the given rewrite rule.
-/
private unsafe def rewrites_for_rule (exp : expr) (cfg : config) (numbered_rule : ℕ × expr × Bool) :
  tactic (List rewrite) :=
  do 
    let (rule_index, rule) := numbered_rule 
    let tracked ← all_rewrites exp rule cfg.to_cfg 
    return (List.map (from_tracked rule_index) tracked.enum)

/--
Get all rewrites that start at the given expression and use one of the given rewrite rules.
-/
unsafe def get_rewrites (rules : List (expr × Bool)) (exp : expr) (cfg : config) : tactic (Buffer rewrite) :=
  do 
    let lists ← List.mmap (rewrites_for_rule exp cfg) rules.enum 
    return (List.foldlₓ Buffer.appendList Buffer.nil lists)

end Tactic.RewriteSearch

