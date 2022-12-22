/-
Copyright (c) 2022 Ian Wood. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Wood

! This file was ported from Lean 3 source module tactic.expand_exists
! leanprover-community/mathlib commit 207cfac9fcd06138865b5d04f7091e46d9320432
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Meta.Expr

/-!
# `expand_exists`

`expand_exists` is an attribute which takes a proof that something exists with some property, and
outputs a value using `classical.some`, and a proof that it has that property using
`classical.some_spec`. For example:

```lean
@[expand_exists it it_spec]
lemma it_exists (n : ℕ) : ∃ m : ℕ, n < m := sorry
```

produces

```
def it (n : ℕ) : ℕ := classical.some (it_exists n)

lemma it_spec (n : ℕ) : n < it n := classical.some_spec (it_exists n)
```
-/


namespace Tactic

open Expr

namespace ExpandExists

/-- Data known when parsing pi expressions.

`decl`'s arguments are: is_theorem, name, type, value.
-/
unsafe structure parse_ctx where
  original_decl : declaration
  decl : Bool → Name → expr → pexpr → tactic Unit
  names : List Name
  pis_depth : ℕ := 0
#align tactic.expand_exists.parse_ctx tactic.expand_exists.parse_ctx

/-- Data known when parsing exists expressions (after parsing pi expressions).

* `with_args` applies pi arguments to a term (eg `id` -> `id #2 #1 #0`).
* `spec_chain` takes the form of `classical.some_spec^n (it_exists ...)`,
with `n` the depth of `∃` parsed.
* `exists_decls` is a list of declarations containing the value(s) of witnesses.
-/
unsafe structure parse_ctx_exists extends parse_ctx where
  with_args : expr → expr
  spec_chain : pexpr
  exists_decls : List Name := []
#align tactic.expand_exists.parse_ctx_exists tactic.expand_exists.parse_ctx_exists

/-- Data known when parsing the proposition (after parsing exists and pi expressions).

`project_proof` projects a proof of the full proposition (eg `A ∧ B ∧ C`) to a specific proof (eg
`B`).
-/
unsafe structure parse_ctx_props extends parse_ctx_exists where
  project_proof : pexpr → pexpr := id
#align tactic.expand_exists.parse_ctx_props tactic.expand_exists.parse_ctx_props

/-- Replaces free variables with their exists declaration. For example, if:

```lean
def n_value : ℕ := ... -- generated by `expand_exists`
```

then this function converts `#0` in `#0 = #0` from `∃ n : ℕ, n = n` to `n_value = n_value`.
-/
unsafe def instantiate_exists_decls (ctx : parse_ctx_exists) (p : expr) : expr :=
  p.instantiate_vars <|
    ctx.exists_decls.reverse.map fun name =>
      ctx.with_args (const Name ctx.original_decl.univ_levels)
#align tactic.expand_exists.instantiate_exists_decls tactic.expand_exists.instantiate_exists_decls

/-- Parses a proposition and creates the associated specification proof. Does not break down the
proposition further.
-/
unsafe def parse_one_prop (ctx : parse_ctx_props) (p : expr) : tactic Unit := do
  let p : expr := instantiate_exists_decls { ctx with } p
  let val : pexpr := ctx.project_proof ctx.spec_chain
  let n ←
    match ctx.names with
      | [n] => return n
      | [] => fail "missing name for proposition"
      | _ => fail "too many names for propositions (are you missing an and?)"
  ctx True n p val
#align tactic.expand_exists.parse_one_prop tactic.expand_exists.parse_one_prop

/--
Parses a proposition and decides if it should be broken down (eg `P ∧ Q` -> `P` and `Q`) depending
on how many `names` are left. Then creates the associated specification proof(s).
-/
unsafe def parse_props : parse_ctx_props → expr → tactic Unit
  | ctx, app (app (const "and" []) p) q => do
    match ctx with
      | [n] => parse_one_prop ctx (app (app (const `and []) p) q)
      | n :: tail =>
        parse_one_prop
            { ctx with 
              names := [n]
              project_proof := (fun p => (const `and.left []) p) ∘ ctx }
            p >>
          parse_props
            { ctx with 
              names := tail
              project_proof := (fun p => (const `and.right []) p) ∘ ctx }
            q
      | [] => fail "missing name for proposition"
  | ctx, p => parse_one_prop ctx p
#align tactic.expand_exists.parse_props tactic.expand_exists.parse_props

/--
Parses an `∃ a : α, p a`, and creates an associated definition with a value of `α`. When `p α` is
not an exists statement, it will call `parse_props`.
-/
unsafe def parse_exists : parse_ctx_exists → expr → tactic Unit
  | ctx, app (app (const "Exists" [lvl]) type) (lam var_name bi var_type body) => do
    -- TODO: Is this needed, and/or does this create issues?
        if type = var_type then tactic.skip
      else tactic.fail "exists types should be equal"
    let ⟨n, names⟩ ←
      match ctx.names with
        | n :: tail => return (n, tail)
        | [] => fail "missing name for exists"
    let-- Type may be dependant on earlier arguments.
    type := instantiate_exists_decls ctx type
    let value : pexpr := (const `classical.some [lvl]) ctx.spec_chain
    ctx False n type value
    let exists_decls := ctx.exists_decls.concat n
    let some_spec : pexpr := (const `classical.some_spec [lvl]) ctx.spec_chain
    let ctx : parse_ctx_exists :=
      { ctx with 
        names
        spec_chain := some_spec
        exists_decls }
    parse_exists ctx body
  | ctx, e => parse_props { ctx with } e
#align tactic.expand_exists.parse_exists tactic.expand_exists.parse_exists

/-- Parses a `∀ (a : α), p a`. If `p` is not a pi expression, it will call `parse_exists`
-/
unsafe def parse_pis : parse_ctx → expr → tactic Unit
  | ctx,
    pi n bi ty body =>-- When making a declaration, wrap in an equivalent pi expression.
    let decl is_theorem name type val :=
      ctx.decl is_theorem Name (pi n bi ty type) (lam n bi (to_pexpr ty) val)
    parse_pis
      { ctx with 
        decl
        pis_depth := ctx.pis_depth + 1 }
      body
  | ctx, app (app (const "Exists" [lvl]) type) p =>
    let with_args := fun e : expr =>
      (List.range ctx.pis_depth).foldr (fun n (e : expr) => e (var n)) e
    parse_exists
      { ctx with 
        with_args
        spec_chain :=
          to_pexpr (with_args <| const ctx.original_decl.to_name ctx.original_decl.univ_levels) }
      (app (app (const "Exists" [lvl]) type) p)
  | ctx, e => fail ("unexpected expression " ++ toString e)
#align tactic.expand_exists.parse_pis tactic.expand_exists.parse_pis

end ExpandExists

/-- From a proof that (a) value(s) exist(s) with certain properties, constructs (an) instance(s)
satisfying those properties. For instance:

```lean
@[expand_exists nat_greater nat_greater_spec]
lemma nat_greater_exists (n : ℕ) : ∃ m : ℕ, n < m := ...

#check nat_greater      -- nat_greater : ℕ → ℕ
#check nat_greater_spec -- nat_greater_spec : ∀ (n : ℕ), n < nat_greater n
```

It supports multiple witnesses:

```lean
@[expand_exists nat_greater_m nat_greater_l nat_greater_spec]
lemma nat_greater_exists (n : ℕ) : ∃ (m l : ℕ), n < m ∧ m < l := ...

#check nat_greater_m      -- nat_greater : ℕ → ℕ
#check nat_greater_l      -- nat_greater : ℕ → ℕ
#check nat_greater_spec-- nat_greater_spec : ∀ (n : ℕ),
  n < nat_greater_m n ∧ nat_greater_m n < nat_greater_l n
```

It also supports logical conjunctions:
```lean
@[expand_exists nat_greater nat_greater_lt nat_greater_nonzero]
lemma nat_greater_exists (n : ℕ) : ∃ m : ℕ, n < m ∧ m ≠ 0 := ...

#check nat_greater         -- nat_greater : ℕ → ℕ
#check nat_greater_lt      -- nat_greater_lt : ∀ (n : ℕ), n < nat_greater n
#check nat_greater_nonzero -- nat_greater_nonzero : ∀ (n : ℕ), nat_greater n ≠ 0
```
Note that without the last argument `nat_greater_nonzero`, `nat_greater_lt` would be:
```lean
#check nat_greater_lt -- nat_greater_lt : ∀ (n : ℕ), n < nat_greater n ∧ nat_greater n ≠ 0
```
-/
@[user_attribute]
unsafe def expand_exists_attr :
    user_attribute Unit (List Name) where 
  Name := "expand_exists"
  descr :=
    "From a proof that (a) value(s) exist(s) with certain properties, " ++
      "constructs (an) instance(s) satisfying those properties."
  parser := lean.parser.many lean.parser.ident
  after_set :=
    some fun decl prio persistent => do
      let d ← get_decl decl
      let names ← expand_exists_attr.get_param decl
      expand_exists.parse_pis
          { original_decl := d
            decl := fun is_t n ty val =>
              tactic.to_expr val >>= fun val =>
                tactic.add_decl
                  (if is_t then declaration.thm n d ty (pure val)
                  else declaration.defn n d ty val default tt)
            names }
          d
#align tactic.expand_exists_attr tactic.expand_exists_attr

add_tactic_doc
  { Name := "expand_exists"
    category := DocCategory.attr
    declNames := [`tactic.expand_exists_attr]
    tags := ["lemma derivation", "environment"] }

end Tactic

