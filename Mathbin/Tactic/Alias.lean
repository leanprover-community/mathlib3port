/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Tactic.Core

/-!
# The `alias` command

This file defines an `alias` command, which can be used to create copies
of a theorem or definition with different names.

Syntax:

```lean
/-- doc string -/
alias my_theorem ← alias1 alias2 ...
```

This produces defs or theorems of the form:

```lean
/-- doc string -/
@[alias] theorem alias1 : <type of my_theorem> := my_theorem

/-- doc string -/
@[alias] theorem alias2 : <type of my_theorem> := my_theorem
```

Iff alias syntax:

```lean
alias A_iff_B ↔ B_of_A A_of_B
alias A_iff_B ↔ ..
```

This gets an existing biconditional theorem `A_iff_B` and produces
the one-way implications `B_of_A` and `A_of_B` (with no change in
implicit arguments). A blank `_` can be used to avoid generating one direction.
The `..` notation attempts to generate the 'of'-names automatically when the
input theorem has the form `A_iff_B` or `A_iff_B_left` etc.
-/


open Lean.Parser Tactic Interactive

namespace Tactic.Alias

@[user_attribute]
unsafe def alias_attr : user_attribute where
  Name := `alias
  descr := "This definition is an alias of another."
  parser := failed

unsafe def alias_direct (d : declaration) (doc : Stringₓ) (al : Name) : tactic Unit := do
  updateex_env fun env =>
      env
        (match d with
        | declaration.defn n ls t _ _ _ =>
          declaration.defn al ls t (expr.const n (level.param <$> ls)) ReducibilityHints.abbrev tt
        | declaration.thm n ls t _ => declaration.thm al ls t <| task.pure <| expr.const n (level.param <$> ls)
        | _ => undefined)
  alias_attr al () tt
  add_doc_string al doc

unsafe def mk_iff_mp_app (iffmp : Name) : expr → (ℕ → expr) → tactic expr
  | expr.pi n bi e t, f => expr.lam n bi e <$> mk_iff_mp_app t fun n => f (n + 1) (expr.var n)
  | quote.1 ((%%ₓa) ↔ %%ₓb), f => pure <| @expr.const true iffmp [] a b (f 0)
  | _, f => fail "Target theorem must have the form `Π x y z, a ↔ b`"

unsafe def alias_iff (d : declaration) (doc : Stringₓ) (al : Name) (iffmp : Name) : tactic Unit :=
  (if al = `_ then skip else get_decl al >> skip) <|> do
    let ls := d.univ_params
    let t := d.type
    let v ← mk_iff_mp_app iffmp t fun _ => expr.const d.to_name (level.param <$> ls)
    let t' ← infer_type v
    updateex_env fun env => env (declaration.thm al ls t' <| task.pure v)
    alias_attr al () tt
    add_doc_string al doc

unsafe def make_left_right : Name → tactic (Name × Name)
  | Name.mk_string s p => do
    let buf : CharBuffer := s.toCharBuffer
    let parts := s.splitOn '_'
    let (left, _ :: right) ← pure <| parts.span (· ≠ "iff")
    let pfx (a b : Stringₓ) := a.toList.isPrefixOf b.toList
    let (suffix', right') ← pure <| right.reverse.span fun s => pfx "left" s ∨ pfx "right" s
    let right := right'.reverse
    let suffix := suffix'.reverse
    pure
        (mkStrName p ("_".intercalate (right ++ "of" :: left ++ suffix)),
          mkStrName p ("_".intercalate (left ++ "of" :: right ++ suffix)))
  | _ => failed

/-- The `alias` command can be used to create copies
of a theorem or definition with different names.

Syntax:

```lean
/-- doc string -/
alias my_theorem ← alias1 alias2 ...
```

This produces defs or theorems of the form:

```lean
/-- doc string -/
@[alias] theorem alias1 : <type of my_theorem> := my_theorem

/-- doc string -/
@[alias] theorem alias2 : <type of my_theorem> := my_theorem
```

Iff alias syntax:

```lean
alias A_iff_B ↔ B_of_A A_of_B
alias A_iff_B ↔ ..
```

This gets an existing biconditional theorem `A_iff_B` and produces
the one-way implications `B_of_A` and `A_of_B` (with no change in
implicit arguments). A blank `_` can be used to avoid generating one direction.
The `..` notation attempts to generate the 'of'-names automatically when the
input theorem has the form `A_iff_B` or `A_iff_B_left` etc.
-/
@[user_command]
unsafe def alias_cmd (meta_info : decl_meta_info) (_ : parse <| tk "alias") : lean.parser Unit := do
  let old ← ident
  let d ←
    (do
          let old ← resolve_constant old
          get_decl old) <|>
        fail ("declaration " ++ toString old ++ " not found")
  let doc := fun al : Name => meta_info.doc_string.getOrElse <| "**Alias** of `" ++ toString old ++ "`."
  (do
        tk "←" <|> tk "<-"
        let aliases ← many ident
        ↑(aliases fun al => alias_direct d (doc al) al)) <|>
      do
      tk "↔" <|> tk "<->"
      let (left, right) ←
        mcond ((tk "." *> tk ".") >> pure tt <|> pure ff)
            (make_left_right old <|> fail "invalid name for automatic name generation")
            (Prod.mk <$> types.ident_ <*> types.ident_)
      alias_iff d (doc left) left `iff.mp
      alias_iff d (doc right) right `iff.mpr

add_tactic_doc
  { Name := "alias", category := DocCategory.cmd, declNames := [`tactic.alias.alias_cmd], tags := ["renaming"] }

unsafe def get_lambda_body : expr → expr
  | expr.lam _ _ _ b => get_lambda_body b
  | a => a

unsafe def get_alias_target (n : Name) : tactic (Option Name) := do
  let tt ← has_attribute' `alias n | pure none
  let d ← get_decl n
  let (head, args) := (get_lambda_body d.value).get_app_fn_args
  let head :=
    if head.is_constant_of `iff.mp ∨ head.is_constant_of `iff.mpr then expr.get_app_fn (head.ith_arg 2) else head
  guardb <| head
  pure <| head

end Tactic.Alias

