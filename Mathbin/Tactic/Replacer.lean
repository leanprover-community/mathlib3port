/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module tactic.replacer
! leanprover-community/mathlib commit 706d88f2b8fdfeb0b22796433d7a6c1a010af9f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Core

/-!
# `def_replacer`

A mechanism for defining tactics for use in auto params, whose
meaning is defined incrementally through attributes.
-/


namespace Tactic

unsafe def replacer_core {α : Type} [reflected _ α] (ntac : Name)
    (eval : ∀ (β) [reflected _ β], expr → tactic β) : List Name → tactic α
  | [] => fail ("no implementation defined for " ++ toString ntac)
  | n :: ns => do
    let d ← get_decl n
    let t := d.type
    let tac ←
      (do
            mk_const n >>= eval (tactic α)) <|>
          (do
              let tac ← mk_const n >>= eval (tactic α → tactic α)
              return (tac (replacer_core ns))) <|>
            do
            let tac ← mk_const n >>= eval (Option (tactic α) → tactic α)
            return (tac (guard (ns ≠ []) >> some (replacer_core ns)))
    tac
#align tactic.replacer_core tactic.replacer_core

unsafe def replacer (ntac : Name) {α : Type} [reflected _ α] (F : Type → Type)
    (eF : ∀ β, reflected _ β → reflected _ (F β)) (R : ∀ β, F β → β) : tactic α :=
  attribute.get_instances ntac >>=
    replacer_core ntac fun β eβ e => R β <$> @eval_expr' (F β) (eF β eβ) e
#align tactic.replacer tactic.replacer

unsafe def mk_replacer₁ : expr → Nat → expr × expr
  | expr.pi n bi d b, i =>
    let (e₁, e₂) := mk_replacer₁ b (i + 1)
    (expr.pi n bi d e₁, (q(expr.pi n bi d) : expr) e₂)
  | _, i => (expr.var i, expr.var 0)
#align tactic.mk_replacer₁ tactic.mk_replacer₁

unsafe def mk_replacer₂ (ntac : Name) (v : expr × expr) : expr → Nat → Option expr
  | expr.pi n bi d b, i => do
    let b' ← mk_replacer₂ b (i + 1)
    some (expr.lam n bi d b')
  | q(tactic $(β)), i =>
    some <|
      (expr.const `` replacer []).mk_app
        [reflect ntac, β, reflect β, expr.lam `γ BinderInfo.default q(Type) v.1,
          expr.lam `γ BinderInfo.default q(Type) <|
            expr.lam `eγ BinderInfo.inst_implicit ((q(reflected Type) : expr) β) v.2,
          expr.lam `γ BinderInfo.default q(Type) <|
            expr.lam `f BinderInfo.default v.1 <|
              (List.range i).foldr (fun i e' => e' (expr.var (i + 2))) (expr.var 0)]
  | _, i => none
#align tactic.mk_replacer₂ tactic.mk_replacer₂

unsafe def mk_replacer (ntac : Name) (e : expr) : tactic expr :=
  mk_replacer₂ ntac (mk_replacer₁ e 0) e 0
#align tactic.mk_replacer tactic.mk_replacer

unsafe def valid_types : expr → List expr
  | expr.pi n bi d b => expr.pi n bi d <$> valid_types b
  | q(tactic $(β)) =>
    [q(tactic.{0} $(β)), q(tactic.{0} $(β) → tactic.{0} $(β)),
      q(Option (tactic.{0} $(β)) → tactic.{0} $(β))]
  | _ => []
#align tactic.valid_types tactic.valid_types

unsafe def replacer_attr (ntac : Name) :
    user_attribute where 
  Name := ntac
  descr :=
    "Replaces the definition of `" ++ toString ntac ++ "`. This should be " ++
                "applied to a definition with the type `tactic unit`, which will be " ++
              "called whenever `" ++
            toString ntac ++
          "` is called. The definition " ++
        "can optionally have an argument of type `tactic unit` or " ++
      "`option (tactic unit)` which refers to the previous definition, if any."
  after_set :=
    some fun n _ _ => do
      let d ← get_decl n
      let base ← get_decl ntac
      guardb ((valid_types base).any (· == d)) <|> fail f! "incorrect type for @[{ntac}]"
#align tactic.replacer_attr tactic.replacer_attr

/-- Define a new replaceable tactic. -/
unsafe def def_replacer (ntac : Name) (ty : expr) : tactic Unit :=
  let nattr := .str ntac "attr"
  do
  add_meta_definition nattr [] q(user_attribute) q(replacer_attr $(reflect ntac))
  set_basic_attribute `user_attribute nattr tt
  let v ← mk_replacer ntac ty
  add_meta_definition ntac [] ty v
  add_doc_string ntac <|
      "The `" ++ toString ntac ++ "` tactic is a \"replaceable\" " ++
                "tactic, which means that its meaning is defined by tactics that " ++
              "are defined later with the `@[" ++
            toString ntac ++
          "]` attribute. " ++
        "It is intended for use with `auto_param`s for structure fields."
#align tactic.def_replacer tactic.def_replacer

/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:38:34: unsupported: setup_tactic_parser -/
/-- `def_replacer foo` sets up a stub definition `foo : tactic unit`, which can
effectively be defined and re-defined later, by tagging definitions with `@[foo]`.

- `@[foo] meta def foo_1 : tactic unit := ...` replaces the current definition of `foo`.
- `@[foo] meta def foo_2 (old : tactic unit) : tactic unit := ...` replaces the current
  definition of `foo`, and provides access to the previous definition via `old`.
  (The argument can also be an `option (tactic unit)`, which is provided as `none` if
  this is the first definition tagged with `@[foo]` since `def_replacer` was invoked.)

`def_replacer foo : α → β → tactic γ` allows the specification of a replacer with
custom input and output types. In this case all subsequent redefinitions must have the
same type, or the type `α → β → tactic γ → tactic γ` or
`α → β → option (tactic γ) → tactic γ` analogously to the previous cases.
 -/
@[user_command]
unsafe def def_replacer_cmd (_ : parse <| tk "def_replacer") : lean.parser Unit := do
  let ntac ← ident
  let ty ← optional (tk ":" *> types.texpr)
  match ty with
    | some p => do
      let t ← to_expr p
      def_replacer ntac t
    | none => def_replacer ntac q(tactic Unit)
#align tactic.def_replacer_cmd tactic.def_replacer_cmd

add_tactic_doc
  { Name := "def_replacer"
    category := DocCategory.cmd
    declNames := [`tactic.def_replacer_cmd]
    tags := ["environment", "renaming"] }

unsafe def unprime : Name → tactic Name
  | nn@(Name.mk_string s n) =>
    let s' := (s.splitOn ''').head
    if s'.length < s.length then pure (Name.mk_string s' n)
    else fail f! "expecting primed name: {nn}"
  | n => fail f! "invalid name: {n}"
#align tactic.unprime tactic.unprime

@[user_attribute]
unsafe def replaceable_attr :
    user_attribute where 
  Name := `replaceable
  descr := "make definition replaceable in dependent modules"
  after_set :=
    some fun n' _ _ => do
      let n ← unprime n'
      let d ← get_decl n'
      def_replacer n d
      (replacer_attr n).Set n' () tt
#align tactic.replaceable_attr tactic.replaceable_attr

end Tactic

