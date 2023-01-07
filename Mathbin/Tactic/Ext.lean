/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Jesse Michael Han

! This file was ported from Lean 3 source module tactic.ext
! leanprover-community/mathlib commit 6afc9b06856ad973f6a2619e3e8a0a8d537a58f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Rcases
import Mathbin.Logic.Function.Basic

universe u₁ u₂

open Interactive Interactive.Types

section Ext

open Lean.Parser Nat Tactic

initialize
  registerTraceClass.1 `ext

/-- `derive_struct_ext_lemma n` generates two extensionality lemmas based on
the equality of all non-propositional projections.

On the following:

```lean
@[ext]
structure foo (α : Type*) :=
(x y : ℕ)
(z : {z // z < x})
(k : α)
(h : x < y)
```

`derive_struct_lemma` generates:

```lean
lemma foo.ext : ∀ {α : Type u_1} (x y : foo α),
  x.x = y.x → x.y = y.y → x.z == y.z → x.k = y.k → x = y
lemma foo.ext_iff : ∀ {α : Type u_1} (x y : foo α),
  x = y ↔ x.x = y.x ∧ x.y = y.y ∧ x.z == y.z ∧ x.k = y.k
```

-/
unsafe def derive_struct_ext_lemma (n : Name) : tactic Name := do
  let e ← get_env
  let fs ← e.structure_fields n
  let d ← get_decl n
  let n ← resolve_constant n
  let r := @expr.const true n <| d.univ_params.map level.param
  let (args, _) ← infer_type r >>= open_pis
  let args := args.map expr.to_implicit_local_const
  let t := r.mk_app args
  let x ← mk_local_def `x t
  let y ← mk_local_def `y t
  let args_x := args ++ [x]
  let args_y := args ++ [y]
  let bs ←
    fs.mmap fun f => do
        let d ← get_decl (n ++ f)
        let a := @expr.const true (n ++ f) <| d.univ_params.map level.param
        let t ← infer_type a
        let s ← infer_type t
        if s ≠ q(Prop) then do
            let x := a args_x
            let y := a args_y
            let t ← infer_type x
            let t' ← infer_type y
            some <$>
                if t = t' then mk_app `eq [x, y] >>= mk_local_def `h
                else mk_mapp `heq [none, x, none, y] >>= mk_local_def `h
          else pure none
  let bs := bs.filterMap id
  let eq_t ← mk_app `eq [x, y]
  let t ← pis (args ++ [x, y] ++ bs) eq_t
  let pr ←
    run_async do
        let (_, pr) ←
          solve_aux t do
              let args ← intron args.length
              let x ← intro1
              let y ← intro1
              cases x
              cases y
              bs fun _ => do
                  let e ← intro1
                  cases e
              reflexivity
        instantiate_mvars pr
  let decl_n := .str n "ext"
  add_decl (declaration.thm decl_n d t pr)
  let bs ← bs.mmap infer_type
  let rhs := expr.mk_and_lst bs
  let iff_t ← mk_app `iff [eq_t, rhs]
  let t ← pis (args ++ [x, y]) iff_t
  let pr ←
    run_async do
        let (_, pr) ←
          (solve_aux t) do
              let args ← intron args.length
              let x ← intro1
              let y ← intro1
              cases x
              cases y
              split
              solve1 do
                  let h ← intro1
                  let hs ← injection h
                  subst_vars
                  repeat (refine ``(And.intro _ _) >> reflexivity)
                  done <|> reflexivity
              solve1 do
                  repeat do
                      refine ``(and_imp.mpr _)
                      let h ← intro1
                      cases h
                      skip
                  let h ← intro1
                  cases h
                  reflexivity
        instantiate_mvars pr
  add_decl (declaration.thm (.str n "ext_iff") d t pr)
  pure decl_n
#align derive_struct_ext_lemma derive_struct_ext_lemma

unsafe def get_ext_subject : expr → tactic Name
  | expr.pi n bi d b => do
    let v ← mk_local' n bi d
    let b' ← whnf <| b.instantiate_var v
    get_ext_subject b'
  | expr.app _ e => do
    let t ← infer_type e >>= instantiate_mvars >>= head_beta
    if t then pure <| t
      else
        if t then pure <| Name.mk_numeral 0 Name.anonymous
        else
          if t then pure <| Name.mk_numeral 1 Name.anonymous
          else do
            let t ← pp t
            fail f! "only constants and Pi types are supported: {t}"
  | e => fail f! "Only expressions of the form `_ → _ → ... → R ... e are supported: {e}"
#align get_ext_subject get_ext_subject

open Native

unsafe def saturate_fun : Name → tactic expr
  | Name.mk_numeral 0 Name.anonymous => do
    let v₀ ← mk_mvar
    let v₁ ← mk_mvar
    return <| v₀ v₁
  | Name.mk_numeral 1 Name.anonymous => do
    let u ← mk_meta_univ
    pure <| expr.sort u
  | n => do
    let e ← resolve_constant n >>= mk_const
    let a ← get_arity e
    e <$> (List.iota a).mmap fun _ => mk_mvar
#align saturate_fun saturate_fun

unsafe def equiv_type_constr (n n' : Name) : tactic Unit := do
  let e ← saturate_fun n
  let e' ← saturate_fun n'
  unify e e' <|> fail f! "{n } and {n'} are not definitionally equal types"
#align equiv_type_constr equiv_type_constr

section PerformanceHack

library_note "user attribute parameters"/--
For performance reasons, it is inadvisable to use `user_attribute.get_param`.
The parameter is stored as a reflected expression.  When calling `get_param`,
the stored parameter is evaluated using `eval_expr`, which first compiles the
expression into VM bytecode. The unevaluated expression is available using
`user_attribute.get_param_untyped`.

In particular, `user_attribute.get_param` MUST NEVER BE USED in the
implementation of an attribute cache. This is because calling `eval_expr`
disables the attribute cache.

There are several possible workarounds:
 1. Set a different attribute depending on the parameter.
 2. Use your own evaluation function instead of `eval_expr`, such as e.g. `expr.to_nat`.
 3. Write your own `has_reflect Param` instance (using a more efficient serialization format).
   The `user_attribute` code unfortunately checks whether the expression has the correct type,
   but you can use `` `(id %%e : Param) `` to pretend that your expression `e` has type `Param`.
-/


/-!
For performance reasons, the parameters of the `@[ext]` attribute are stored
in two auxiliary attributes:
```lean
attribute [ext thunk] funext

-- is turned into
attribute [_ext_core (@id name @funext)] thunk
attribute [_ext_lemma_core] funext
```

see Note [user attribute parameters]
-/


attribute [local semireducible] reflected

@[local instance]
private unsafe def hacky_name_reflect : has_reflect Name := fun n =>
  q((id $(expr.const n []) : Name))
#align hacky_name_reflect hacky_name_reflect

@[user_attribute]
private unsafe def ext_attr_core : user_attribute (name_map Name) Name
    where
  Name := `_ext_core
  descr := "(internal attribute used by ext)"
  cache_cfg :=
    { dependencies := []
      mk_cache := fun ns =>
        ns.mfoldl
          (fun m n => do
            let ext_l ← ext_attr_core.get_param_untyped n
            pure (m n ext_l))
          mk_name_map }
  parser := failure
#align ext_attr_core ext_attr_core

end PerformanceHack

/-- Private attribute used to tag extensionality lemmas. -/
@[user_attribute]
private unsafe def ext_lemma_attr_core : user_attribute
    where
  Name := `_ext_lemma_core
  descr := "(internal attribute used by ext)"
  parser := failure
#align ext_lemma_attr_core ext_lemma_attr_core

/-- Returns the extensionality lemmas in the environment, as a map from structure
name to lemma name.
-/
unsafe def get_ext_lemmas : tactic (name_map Name) :=
  ext_attr_core.get_cache
#align get_ext_lemmas get_ext_lemmas

/-- Returns the extensionality lemmas in the environment, as a list of lemma names.
-/
unsafe def get_ext_lemma_names : tactic (List Name) :=
  attribute.get_instances ext_lemma_attr_core.Name
#align get_ext_lemma_names get_ext_lemma_names

/-- Marks `lem` as an extensionality lemma corresponding to type constructor `constr`;
if `persistent` is true then this is a global attribute, else local. -/
unsafe def add_ext_lemma (constr lem : Name) (persistent : Bool) : tactic Unit :=
  ext_attr_core.Set constr lem persistent >> ext_lemma_attr_core.Set lem () persistent
#align add_ext_lemma add_ext_lemma

/-- Tag lemmas of the form:

```lean
@[ext]
lemma my_collection.ext (a b : my_collection)
  (h : ∀ x, a.lookup x = b.lookup y) :
  a = b := ...
```

The attribute indexes extensionality lemma using the type of the
objects (i.e. `my_collection`) which it gets from the statement of
the lemma.  In some cases, the same lemma can be used to state the
extensionality of multiple types that are definitionally equivalent.

```lean
attribute [ext thunk, ext stream] funext
```

Also, the following:

```lean
@[ext]
lemma my_collection.ext (a b : my_collection)
  (h : ∀ x, a.lookup x = b.lookup y) :
  a = b := ...
```

is equivalent to

```lean
@[ext my_collection]
lemma my_collection.ext (a b : my_collection)
  (h : ∀ x, a.lookup x = b.lookup y) :
  a = b := ...
```

This allows us specify type synonyms along with the type
that is referred to in the lemma statement.

```lean
@[ext, ext my_type_synonym]
lemma my_collection.ext (a b : my_collection)
  (h : ∀ x, a.lookup x = b.lookup y) :
  a = b := ...
```

The `ext` attribute can be applied to a structure to generate its extensionality lemmas:

```lean
@[ext]
structure foo (α : Type*) :=
(x y : ℕ)
(z : {z // z < x})
(k : α)
(h : x < y)
```

will generate:

```lean
@[ext] lemma foo.ext : ∀ {α : Type u_1} (x y : foo α),
x.x = y.x → x.y = y.y → x.z == y.z → x.k = y.k → x = y
lemma foo.ext_iff : ∀ {α : Type u_1} (x y : foo α),
x = y ↔ x.x = y.x ∧ x.y = y.y ∧ x.z == y.z ∧ x.k = y.k
```

-/
@[user_attribute]
unsafe def extensional_attribute : user_attribute Unit (Option Name)
    where
  Name := `ext
  descr := "lemmas usable by `ext` tactic"
  parser := optional ident
  after_set :=
    some fun n _ b => do
      let add ← extensional_attribute.get_param n
      let e ← get_env
      let n ← if (e.structure_fields n).isSome then derive_struct_ext_lemma n else pure n
      let s ← mk_const n >>= infer_type >>= get_ext_subject
      match add with
        | none => add_ext_lemma s n b
        | some add => equiv_type_constr s add >> add_ext_lemma add n b
#align extensional_attribute extensional_attribute

add_tactic_doc
  { Name := "ext"
    category := DocCategory.attr
    declNames := [`extensional_attribute]
    tags := ["rewrite", "logic"] }

library_note "partially-applied ext lemmas"/--
When possible, `ext` lemmas are stated without a full set of arguments. As an example, for bundled
homs `f`, `g`, and `of`, `f.comp of = g.comp of → f = g` is a better `ext` lemma than
`(∀ x, f (of x) = g (of x)) → f = g`, as the former allows a second type-specific extensionality
lemmas to be applied to `f.comp of = g.comp of`.
If the domain of `of` is `ℕ` or `ℤ` and `of` is a `ring_hom`, such a lemma could then make the goal
`f (of 1) = g (of 1)`.

For bundled morphisms, there is a `ext` lemma that always applies of the form
`(∀ x, ⇑f x = ⇑g x) → f = g`. When adding type-specific `ext` lemmas like the one above, we want
these to be tried first. This happens automatically since the type-specific lemmas are inevitably
defined later.
-/


-- We mark some existing extensionality lemmas.
attribute [ext] Array'.ext propext Function.hfunext

/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Ext.lean:18:19: unsupported: attribute [ext id] -/
attribute [ext] _root_.funext

-- This line is equivalent to:
--   attribute [ext (→)] _root_.funext
-- but (→) is not actually a binary relation with a constant at the head,
-- so we use the special name [anon].0 to represent (→).
run_cmd
  add_ext_lemma (Name.mk_numeral 0 Name.anonymous) `` _root_.funext true

-- We create some extensionality lemmas for existing structures.
attribute [ext] ULift

namespace PLift

-- This is stronger than the one generated automatically.
@[ext]
theorem ext {P : Prop} (a b : PLift P) : a = b := by cases a; cases b; rfl
#align plift.ext PLift.ext

end PLift

-- Conservatively, we'll only add extensionality lemmas for `has_*` structures
-- as they become useful.
attribute [ext] Zero

#print Unit.ext /-
@[ext]
theorem Unit.ext {x y : Unit} : x = y := by
  cases x
  cases y
  rfl
#align unit.ext Unit.ext
-/

#print PUnit.ext /-
@[ext]
theorem PUnit.ext {x y : PUnit} : x = y := by
  cases x
  cases y
  rfl
#align punit.ext PUnit.ext
-/

namespace Tactic

/-- Helper structure for `ext` and `ext1`. `lemmas` keeps track of extensionality lemmas
  applied so far. -/
unsafe structure ext_state : Type where
  patts : List rcases_patt := []
  trace_msg : List String := []
  fuel : Option ℕ := none
#align tactic.ext_state tactic.ext_state

/-- Helper function for `try_intros`. Additionally populates the `trace_msg` field
  of `ext_state`. -/
private unsafe def try_intros_core : StateT ext_state tactic Unit := do
  let ⟨patts, trace_msg, fuel⟩ ← get
  match patts with
    | [] =>
      (do
          let es ← StateT.lift intros
          (when (es > 0)) do
              let msg := "intros " ++ " ".intercalate (es fun e => e)
              modify fun ⟨patts, trace_msg, fuel⟩ => ⟨patts, trace_msg ++ [msg], fuel⟩) <|>
        pure ()
    | x :: xs => do
      let tgt ← StateT.lift (target >>= whnf)
      (when tgt) do
          StateT.lift (rintro [x])
          let msg ← StateT.lift ((· ++ ·) "rintro " <$> format.to_string <$> x ff)
          modify fun ⟨_, trace_msg, fuel⟩ => ⟨xs, trace_msg ++ [msg], fuel⟩
          try_intros_core
#align tactic.try_intros_core tactic.try_intros_core

/-- Try to introduce as many arguments as possible, using the given patterns to destruct the
  introduced variables. Returns the unused patterns. -/
unsafe def try_intros (patts : List rcases_patt) : tactic (List rcases_patt) :=
  let σ := ext_state.mk patts [] none
  (ext_state.patts ∘ Prod.snd) <$> StateT.run try_intros_core σ
#align tactic.try_intros tactic.try_intros

/-- Apply one extensionality lemma, and destruct the arguments using the patterns
  in the ext_state. -/
unsafe def ext1_core (cfg : ApplyCfg := { }) : StateT ext_state tactic Unit := do
  let ⟨patts, trace_msg, _⟩ ← get
  let new_msgs ←
    StateT.lift <|
        focus1 do
          let m ← get_ext_lemmas
          let tgt ← target
          when_tracing `ext <|
              ← do
                dbg_trace "[ext] goal: {← tgt}"
          let subject ← get_ext_subject tgt
          let new_trace_msg ←
            (do
                  let rule ← m.find subject
                  if is_trace_enabled_for `ext then
                      (← do
                          dbg_trace "[ext] matched goal to rule: {← rule}") >>
                        timetac "[ext] application attempt time" (applyc rule cfg)
                    else applyc rule cfg
                  pure ["apply " ++ rule]) <|>
                (do
                    let ls ← get_ext_lemma_names
                    let nms := ls.map Name.toString
                    let rule ←
                      ls.any_of fun n =>
                          (if is_trace_enabled_for `ext then
                              (← do
                                  dbg_trace "[ext] trying to apply ext lemma: {← n}") >>
                                timetac "[ext] application attempt time" (applyc n cfg)
                            else applyc n cfg) *>
                            pure n
                    pure ["apply " ++ rule]) <|>
                  fail f! "no applicable extensionality rule found for {subject}"
          pure new_trace_msg
  modify fun ⟨patts, trace_msg, fuel⟩ => ⟨patts, trace_msg ++ new_msgs, fuel⟩
  try_intros_core
#align tactic.ext1_core tactic.ext1_core

/-- Apply multiple extensionality lemmas, destructing the arguments using the given patterns. -/
unsafe def ext_core (cfg : ApplyCfg := { }) : StateT ext_state tactic Unit := do
  let acc@⟨_, _, fuel⟩ ← get
  match fuel with
    | some 0 => pure ()
    | n => do
      ext1_core cfg
      modify fun ⟨patts, lemmas, _⟩ => ⟨patts, lemmas, Nat.pred <$> n⟩
      ext_core <|> pure ()
#align tactic.ext_core tactic.ext_core

/-- Apply one extensionality lemma, and destruct the arguments using the given patterns.
  Returns the unused patterns. -/
unsafe def ext1 (xs : List rcases_patt) (cfg : ApplyCfg := { }) (trace : Bool := false) :
    tactic (List rcases_patt) := do
  let ⟨_, σ⟩ ← StateT.run (ext1_core cfg) { patts := xs }
  when trace <| tactic.trace <| "Try this: " ++ ", ".intercalate σ
  pure σ
#align tactic.ext1 tactic.ext1

/-- Apply multiple extensionality lemmas, destructing the arguments using the given patterns.
  `ext ps (some n)` applies at most `n` extensionality lemmas. Returns the unused patterns. -/
unsafe def ext (xs : List rcases_patt) (fuel : Option ℕ) (cfg : ApplyCfg := { })
    (trace : Bool := false) : tactic (List rcases_patt) := do
  let ⟨_, σ⟩ ←
    StateT.run (ext_core cfg)
        { patts := xs
          fuel }
  when trace <| tactic.trace <| "Try this: " ++ ", ".intercalate σ
  pure σ
#align tactic.ext tactic.ext

-- mathport name: parser.optional
local postfix:1024 "?" => optional

-- mathport name: parser.many
local postfix:1024 "*" => many

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`ext1 id` selects and apply one extensionality lemma (with attribute\n`ext`), using `id`, if provided, to name a local constant\nintroduced by the lemma. If `id` is omitted, the local constant is\nnamed automatically, as per `intro`. Placing a `?` after `ext1`\n (e.g. `ext1? i ⟨a,b⟩ : 3`) will display a sequence of tactic\napplications that can replace the call to `ext1`.\n-/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `interactive.ext1 [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`trace]
         [":"
          (Term.app
           `parse
           [(Tactic.Tactic.Ext.parser.optional (Term.app `tk [(str "\"?\"")]) "?")])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`xs]
         [":" (Term.app `parse [(Tactic.Tactic.Ext.parser.many `rcases_patt_parse_hi "*")])]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `tactic [`Unit]))])
      (Command.declValSimple
       ":="
       (Init.Control.Functor.«term_$>_»
        (Term.app
         `ext1
         [`xs
          (Term.structInst "{" [] [] (Term.optEllipsis []) [] "}")
          (Term.proj `trace "." `isSome)])
        " $> "
        (Term.tuple "(" [] ")"))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Control.Functor.«term_$>_»
       (Term.app
        `ext1
        [`xs
         (Term.structInst "{" [] [] (Term.optEllipsis []) [] "}")
         (Term.proj `trace "." `isSome)])
       " $> "
       (Term.tuple "(" [] ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [] ")")
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 100, term))
      (Term.app
       `ext1
       [`xs
        (Term.structInst "{" [] [] (Term.optEllipsis []) [] "}")
        (Term.proj `trace "." `isSome)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `trace "." `isSome)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `trace
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.structInst "{" [] [] (Term.optEllipsis []) [] "}")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `xs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ext1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 101 >? 1022, (some 1023, term) <=? (some 100, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 100, (some 100, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `tactic [`Unit])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Unit
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `parse [(Tactic.Tactic.Ext.parser.many `rcases_patt_parse_hi "*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Tactic.Ext.parser.many', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Tactic.Ext.parser.many', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.Tactic.Ext.parser.many `rcases_patt_parse_hi "*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Tactic.Ext.parser.many', expected 'Tactic.Tactic.Ext.parser.many._@.Tactic.Ext._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      `ext1 id` selects and apply one extensionality lemma (with attribute
      `ext`), using `id`, if provided, to name a local constant
      introduced by the lemma. If `id` is omitted, the local constant is
      named automatically, as per `intro`. Placing a `?` after `ext1`
       (e.g. `ext1? i ⟨a,b⟩ : 3`) will display a sequence of tactic
      applications that can replace the call to `ext1`.
      -/
    unsafe
  def
    interactive.ext1
    ( trace : parse tk "?" ? ) ( xs : parse rcases_patt_parse_hi * ) : tactic Unit
    := ext1 xs { } trace . isSome $> ( )
#align tactic.interactive.ext1 tactic.interactive.ext1

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "- `ext` applies as many extensionality lemmas as possible;\n- `ext ids`, with `ids` a list of identifiers, finds extentionality and applies them\n  until it runs out of identifiers in `ids` to name the local constants.\n- `ext` can also be given an `rcases` pattern in place of an identifier.\n  This will destruct the introduced local constant.\n- Placing a `?` after `ext` (e.g. `ext? i ⟨a,b⟩ : 3`) will display\n  a sequence of tactic applications that can replace the call to `ext`.\n- `set_option trace.ext true` will trace every attempted lemma application,\n  along with the time it takes for the application to succeed or fail.\n  This is useful for debugging slow `ext` calls.\n\nWhen trying to prove:\n\n```lean\nα β : Type,\nf g : α → set β\n⊢ f = g\n```\n\napplying `ext x y` yields:\n\n```lean\nα β : Type,\nf g : α → set β,\nx : α,\ny : β\n⊢ y ∈ f x ↔ y ∈ f x\n```\n\nby applying functional extensionality and set extensionality.\n\nWhen trying to prove:\n\n```lean\nα β γ : Type\nf g : α × β → γ\n⊢ f = g\n```\n\napplying `ext ⟨a, b⟩` yields:\n\n```lean\nα β γ : Type,\nf g : α × β → γ,\na : α,\nb : β\n⊢ f (a, b) = g (a, b)\n```\n\nby applying functional extensionality and destructing the introduced pair.\n\nIn the previous example, applying `ext? ⟨a,b⟩` will produce the trace message:\n\n```lean\nTry this: apply funext, rintro ⟨a, b⟩\n```\n\nA maximum depth can be provided with `ext x y z : 3`.\n-/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `interactive.ext [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.arrow
          («term_<|_»
           `parse
           "<|"
           (Tactic.Tactic.Ext.parser.optional (Term.app `tk [(str "\"?\"")]) "?"))
          "→"
          (Term.arrow
           (Term.app `parse [(Tactic.Tactic.Ext.parser.many `rintro_patt_parse_hi "*")])
           "→"
           (Term.arrow
            (Term.app
             `parse
             [(Tactic.Tactic.Ext.parser.optional
               («term_*>_» (Term.app `tk [(str "\":\"")]) "*>" `small_nat)
               "?")])
            "→"
            (Term.app `tactic [`Unit])))))])
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[`trace "," («term[_]» "[" [] "]") "," (Term.app `some [`n])]]
           "=>"
           (Term.app
            `iterate_range
            [(num "1")
             `n
             (Init.Control.Functor.«term_$>_»
              (Term.app
               `ext1
               [(«term[_]» "[" [] "]")
                (Term.structInst "{" [] [] (Term.optEllipsis []) [] "}")
                (Term.proj `trace "." `isSome)])
              " $> "
              (Term.tuple "(" [] ")"))]))
          (Term.matchAlt
           "|"
           [[`trace "," («term[_]» "[" [] "]") "," `none]]
           "=>"
           (Term.app
            `repeat1
            [(Init.Control.Functor.«term_$>_»
              (Term.app
               `ext1
               [(«term[_]» "[" [] "]")
                (Term.structInst "{" [] [] (Term.optEllipsis []) [] "}")
                (Term.proj `trace "." `isSome)])
              " $> "
              (Term.tuple "(" [] ")"))]))
          (Term.matchAlt
           "|"
           [[`trace "," `xs "," `n]]
           "=>"
           (Init.Control.Functor.«term_$>_»
            (Term.app
             `ext
             [(Term.proj `xs "." `join)
              `n
              (Term.structInst "{" [] [] (Term.optEllipsis []) [] "}")
              (Term.proj `trace "." `isSome)])
            " $> "
            (Term.tuple "(" [] ")")))])
        []))
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Control.Functor.«term_$>_»
       (Term.app
        `ext
        [(Term.proj `xs "." `join)
         `n
         (Term.structInst "{" [] [] (Term.optEllipsis []) [] "}")
         (Term.proj `trace "." `isSome)])
       " $> "
       (Term.tuple "(" [] ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [] ")")
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 100, term))
      (Term.app
       `ext
       [(Term.proj `xs "." `join)
        `n
        (Term.structInst "{" [] [] (Term.optEllipsis []) [] "}")
        (Term.proj `trace "." `isSome)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `trace "." `isSome)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `trace
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.structInst "{" [] [] (Term.optEllipsis []) [] "}")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `xs "." `join)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `xs
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 101 >? 1022, (some 1023, term) <=? (some 100, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 100, (some 100, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `xs
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `trace
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `repeat1
       [(Init.Control.Functor.«term_$>_»
         (Term.app
          `ext1
          [(«term[_]» "[" [] "]")
           (Term.structInst "{" [] [] (Term.optEllipsis []) [] "}")
           (Term.proj `trace "." `isSome)])
         " $> "
         (Term.tuple "(" [] ")"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Control.Functor.«term_$>_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Control.Functor.«term_$>_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Control.Functor.«term_$>_»
       (Term.app
        `ext1
        [(«term[_]» "[" [] "]")
         (Term.structInst "{" [] [] (Term.optEllipsis []) [] "}")
         (Term.proj `trace "." `isSome)])
       " $> "
       (Term.tuple "(" [] ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [] ")")
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 100, term))
      (Term.app
       `ext1
       [(«term[_]» "[" [] "]")
        (Term.structInst "{" [] [] (Term.optEllipsis []) [] "}")
        (Term.proj `trace "." `isSome)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `trace "." `isSome)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `trace
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.structInst "{" [] [] (Term.optEllipsis []) [] "}")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ext1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 101 >? 1022, (some 1023, term) <=? (some 100, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 100, (some 100,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Init.Control.Functor.«term_$>_»
      (Term.app
       `ext1
       [(«term[_]» "[" [] "]")
        (Term.structInst "{" [] [] (Term.optEllipsis []) [] "}")
        (Term.proj `trace "." `isSome)])
      " $> "
      (Term.tuple "(" [] ")"))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `repeat1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `trace
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `iterate_range
       [(num "1")
        `n
        (Init.Control.Functor.«term_$>_»
         (Term.app
          `ext1
          [(«term[_]» "[" [] "]")
           (Term.structInst "{" [] [] (Term.optEllipsis []) [] "}")
           (Term.proj `trace "." `isSome)])
         " $> "
         (Term.tuple "(" [] ")"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Control.Functor.«term_$>_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Control.Functor.«term_$>_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Init.Control.Functor.«term_$>_»
       (Term.app
        `ext1
        [(«term[_]» "[" [] "]")
         (Term.structInst "{" [] [] (Term.optEllipsis []) [] "}")
         (Term.proj `trace "." `isSome)])
       " $> "
       (Term.tuple "(" [] ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [] ")")
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 100, term))
      (Term.app
       `ext1
       [(«term[_]» "[" [] "]")
        (Term.structInst "{" [] [] (Term.optEllipsis []) [] "}")
        (Term.proj `trace "." `isSome)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `trace "." `isSome)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `trace
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.structInst "{" [] [] (Term.optEllipsis []) [] "}")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term[_]»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ext1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 101 >? 1022, (some 1023, term) <=? (some 100, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 100, (some 100,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Init.Control.Functor.«term_$>_»
      (Term.app
       `ext1
       [(«term[_]» "[" [] "]")
        (Term.structInst "{" [] [] (Term.optEllipsis []) [] "}")
        (Term.proj `trace "." `isSome)])
      " $> "
      (Term.tuple "(" [] ")"))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `iterate_range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `trace
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       («term_<|_»
        `parse
        "<|"
        (Tactic.Tactic.Ext.parser.optional (Term.app `tk [(str "\"?\"")]) "?"))
       "→"
       (Term.arrow
        (Term.app `parse [(Tactic.Tactic.Ext.parser.many `rintro_patt_parse_hi "*")])
        "→"
        (Term.arrow
         (Term.app
          `parse
          [(Tactic.Tactic.Ext.parser.optional
            («term_*>_» (Term.app `tk [(str "\":\"")]) "*>" `small_nat)
            "?")])
         "→"
         (Term.app `tactic [`Unit]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       (Term.app `parse [(Tactic.Tactic.Ext.parser.many `rintro_patt_parse_hi "*")])
       "→"
       (Term.arrow
        (Term.app
         `parse
         [(Tactic.Tactic.Ext.parser.optional
           («term_*>_» (Term.app `tk [(str "\":\"")]) "*>" `small_nat)
           "?")])
        "→"
        (Term.app `tactic [`Unit])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       (Term.app
        `parse
        [(Tactic.Tactic.Ext.parser.optional
          («term_*>_» (Term.app `tk [(str "\":\"")]) "*>" `small_nat)
          "?")])
       "→"
       (Term.app `tactic [`Unit]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tactic [`Unit])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Unit
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app
       `parse
       [(Tactic.Tactic.Ext.parser.optional
         («term_*>_» (Term.app `tk [(str "\":\"")]) "*>" `small_nat)
         "?")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Tactic.Ext.parser.optional', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Tactic.Ext.parser.optional', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.Tactic.Ext.parser.optional
       («term_*>_» (Term.app `tk [(str "\":\"")]) "*>" `small_nat)
       "?")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Tactic.Ext.parser.optional', expected 'Tactic.Tactic.Ext.parser.optional._@.Tactic.Ext._hyg.16'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      - `ext` applies as many extensionality lemmas as possible;
      - `ext ids`, with `ids` a list of identifiers, finds extentionality and applies them
        until it runs out of identifiers in `ids` to name the local constants.
      - `ext` can also be given an `rcases` pattern in place of an identifier.
        This will destruct the introduced local constant.
      - Placing a `?` after `ext` (e.g. `ext? i ⟨a,b⟩ : 3`) will display
        a sequence of tactic applications that can replace the call to `ext`.
      - `set_option trace.ext true` will trace every attempted lemma application,
        along with the time it takes for the application to succeed or fail.
        This is useful for debugging slow `ext` calls.
      
      When trying to prove:
      
      ```lean
      α β : Type,
      f g : α → set β
      ⊢ f = g
      ```
      
      applying `ext x y` yields:
      
      ```lean
      α β : Type,
      f g : α → set β,
      x : α,
      y : β
      ⊢ y ∈ f x ↔ y ∈ f x
      ```
      
      by applying functional extensionality and set extensionality.
      
      When trying to prove:
      
      ```lean
      α β γ : Type
      f g : α × β → γ
      ⊢ f = g
      ```
      
      applying `ext ⟨a, b⟩` yields:
      
      ```lean
      α β γ : Type,
      f g : α × β → γ,
      a : α,
      b : β
      ⊢ f (a, b) = g (a, b)
      ```
      
      by applying functional extensionality and destructing the introduced pair.
      
      In the previous example, applying `ext? ⟨a,b⟩` will produce the trace message:
      
      ```lean
      Try this: apply funext, rintro ⟨a, b⟩
      ```
      
      A maximum depth can be provided with `ext x y z : 3`.
      -/
    unsafe
  def
    interactive.ext
    : parse <| tk "?" ? → parse rintro_patt_parse_hi * → parse tk ":" *> small_nat ? → tactic Unit
    | trace , [ ] , some n => iterate_range 1 n ext1 [ ] { } trace . isSome $> ( )
      | trace , [ ] , none => repeat1 ext1 [ ] { } trace . isSome $> ( )
      | trace , xs , n => ext xs . join n { } trace . isSome $> ( )
#align tactic.interactive.ext tactic.interactive.ext

/-- * `ext1 id` selects and apply one extensionality lemma (with
  attribute `ext`), using `id`, if provided, to name a
  local constant introduced by the lemma. If `id` is omitted, the
  local constant is named automatically, as per `intro`.

* `ext` applies as many extensionality lemmas as possible;
* `ext ids`, with `ids` a list of identifiers, finds extensionality lemmas
  and applies them until it runs out of identifiers in `ids` to name
  the local constants.
* `ext` can also be given an `rcases` pattern in place of an identifier.
  This will destruct the introduced local constant.
- Placing a `?` after `ext`/`ext1` (e.g. `ext? i ⟨a,b⟩ : 3`) will display
  a sequence of tactic applications that can replace the call to `ext`/`ext1`.
- `set_option trace.ext true` will trace every attempted lemma application,
  along with the time it takes for the application to succeed or fail.
  This is useful for debugging slow `ext` calls.

When trying to prove:

```lean
α β : Type,
f g : α → set β
⊢ f = g
```

applying `ext x y` yields:

```lean
α β : Type,
f g : α → set β,
x : α,
y : β
⊢ y ∈ f x ↔ y ∈ g x
```
by applying functional extensionality and set extensionality.

When trying to prove:

```lean
α β γ : Type
f g : α × β → γ
⊢ f = g
```

applying `ext ⟨a, b⟩` yields:

```lean
α β γ : Type,
f g : α × β → γ,
a : α,
b : β
⊢ f (a, b) = g (a, b)
```

by applying functional extensionality and destructing the introduced pair.

In the previous example, applying `ext? ⟨a,b⟩` will produce the trace message:

```lean
Try this: apply funext, rintro ⟨a, b⟩
```

A maximum depth can be provided with `ext x y z : 3`.
-/
add_tactic_doc
  { Name := "ext1 / ext"
    category := DocCategory.tactic
    declNames := [`tactic.interactive.ext1, `tactic.interactive.ext]
    tags := ["rewriting", "logic"] }

end Tactic

end Ext

