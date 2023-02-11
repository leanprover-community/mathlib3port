/-
Copyright (c) 2020 Kevin Lacker, Keeley Hoek, Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Keeley Hoek, Scott Morrison

! This file was ported from Lean 3 source module tactic.rewrite_search.types
! leanprover-community/mathlib commit dc6c365e751e34d100e80fe6e314c3c3e0fd2988
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.NthRewrite.Default

/-!
# Types used in rewrite search.
-/


initialize
  registerTraceClass.1 `rewrite_search

namespace Tactic.RewriteSearch

/-- `side` represents the side of an equation, either the left or the right.
-/
inductive Side
  | L
  | R
  deriving DecidableEq, Inhabited
#align tactic.rewrite_search.side Tactic.RewriteSearch.Side

/-- Convert a side to a human-readable string. -/
unsafe def side.to_string : Side → format
  | side.L => "L"
  | side.R => "R"
#align tactic.rewrite_search.side.to_string tactic.rewrite_search.side.to_string

/-- Convert a side to the string "lhs" or "rhs", for use in tactic name generation. -/
def Side.toXhs : Side → String
  | side.L => "lhs"
  | side.R => "rhs"
#align tactic.rewrite_search.side.to_xhs Tactic.RewriteSearch.Side.toXhs

unsafe instance side.has_to_format : has_to_format Side :=
  ⟨side.to_string⟩
#align tactic.rewrite_search.side.has_to_format tactic.rewrite_search.side.has_to_format

/-- A `how` contains information needed by the explainer to generate code for a rewrite.
`rule_index` denotes which rule in the static list of rules is used.
`location` describes which match of that rule was used, to work with `nth_rewrite`.
`addr` is a list of "left" and "right" describing which subexpression is rewritten.
-/
unsafe structure how where
  rule_index : ℕ
  location : ℕ
  addr : Option (List ExprLens.Dir)
#align tactic.rewrite_search.how tactic.rewrite_search.how

/-- Convert a `how` to a human-readable string. -/
unsafe def how.to_string : how → format
  | h => f! "rewrite {h.rule_index } {h.location } {h.addr.iget.toString}"
#align tactic.rewrite_search.how.to_string tactic.rewrite_search.how.to_string

unsafe instance how.has_to_format : has_to_format how :=
  ⟨how.to_string⟩
#align tactic.rewrite_search.how.has_to_format tactic.rewrite_search.how.has_to_format

/-- `rewrite` represents a single step of rewriting, that proves `exp` using `proof`. -/
unsafe structure rewrite where
  exp : expr
  proof : tactic expr
  -- we defer constructing the proofs until they are needed
  how : how
#align tactic.rewrite_search.rewrite tactic.rewrite_search.rewrite

/-- `proof_unit` represents a sequence of steps that can be applied to one side of the
equation to prove a particular expression.
-/
unsafe structure proof_unit where
  proof : expr
  Side : Side
  steps : List how
#align tactic.rewrite_search.proof_unit tactic.rewrite_search.proof_unit

/-- Configuration options for a rewrite search.
`max_iterations` controls how many vertices are expanded in the graph search.
`explain` generates Lean code to replace the call to `rewrite_search`.
`explain_using_conv` changes the nature of the explanation.
-/
unsafe structure config extends tactic.nth_rewrite.cfg where
  max_iterations : ℕ := 5000
  explain_using_conv : Bool := true
#align tactic.rewrite_search.config tactic.rewrite_search.config

end Tactic.RewriteSearch

