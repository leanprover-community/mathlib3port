/-
Copyright (c) 2019 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Scott Morrison, Keeley Hoek, Robert Y. Lewis, Floris van Doorn

! This file was ported from Lean 3 source module meta.expr
! leanprover-community/mathlib commit 6d0adfa76594f304b4650d098273d4366edeb61b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Option.Defs
import Mathbin.Data.String.Defs
import Mathbin.Tactic.DeriveInhabited

/-!
# Additional operations on expr and related types

This file defines basic operations on the types expr, name, declaration, level, environment.

This file is mostly for non-tactics. Tactics should generally be placed in `tactic.core`.

## Tags

expr, name, declaration, level, environment, meta, metaprogramming, tactic
-/


open Tactic

deriving instance has_reflect, DecidableEq for BinderInfo, CongrArgKind

namespace BinderInfo

/-! ### Declarations about `binder_info` -/


instance : Inhabited BinderInfo :=
  ⟨BinderInfo.default⟩

/-- The brackets corresponding to a given binder_info. -/
def brackets : BinderInfo → String × String
  | BinderInfo.implicit => ("{", "}")
  | BinderInfo.strict_implicit => ("{{", "}}")
  | BinderInfo.inst_implicit => ("[", "]")
  | _ => ("(", ")")
#align binder_info.brackets BinderInfo.brackets

end BinderInfo

namespace Name

/-! ### Declarations about `name` -/


/-- Find the largest prefix `n` of a `name` such that `f n ≠ none`, then replace this prefix
with the value of `f n`. -/
def mapPrefix (f : Name → Option Name) : Name → Name
  | anonymous => anonymous
  | mk_string s n' => (f (mk_string s n')).getOrElse (mk_string s <| map_prefix n')
  | mk_numeral d n' => (f (mk_numeral d n')).getOrElse (mk_numeral d <| map_prefix n')
#align name.map_prefix Name.mapPrefix

/-- If `nm` is a simple name (having only one string component) starting with `_`, then
`deinternalize_field nm` removes the underscore. Otherwise, it does nothing. -/
unsafe def deinternalize_field : Name → Name
  | mk_string s Name.anonymous =>
    let i := s.mkIterator
    if i.curr = '_' then i.next.nextToString else s
  | n => n
#align name.deinternalize_field name.deinternalize_field

/-- `get_nth_prefix nm n` removes the last `n` components from `nm` -/
unsafe def get_nth_prefix : Name → ℕ → Name
  | nm, 0 => nm
  | nm, n + 1 => get_nth_prefix nm.getPrefix n
#align name.get_nth_prefix name.get_nth_prefix

/-- Auxiliary definition for `pop_nth_prefix` -/
private unsafe def pop_nth_prefix_aux : Name → ℕ → Name × ℕ
  | anonymous, n => (anonymous, 1)
  | nm, n =>
    let (pfx, height) := pop_nth_prefix_aux nm.getPrefix n
    if height ≤ n then (anonymous, height + 1) else (nm.updatePrefix pfx, height + 1)
#align name.pop_nth_prefix_aux name.pop_nth_prefix_aux

/-- Pops the top `n` prefixes from the given name. -/
unsafe def pop_nth_prefix (nm : Name) (n : ℕ) : Name :=
  Prod.fst <| pop_nth_prefix_aux nm n
#align name.pop_nth_prefix name.pop_nth_prefix

/-- Pop the prefix of a name -/
unsafe def pop_prefix (n : Name) : Name :=
  pop_nth_prefix n 1
#align name.pop_prefix name.pop_prefix

/-- Auxiliary definition for `from_components` -/
private def from_components_aux : Name → List String → Name
  | n, [] => n
  | n, s :: rest => from_components_aux (Name.mk_string s n) rest
#align name.from_components_aux name.from_components_aux

/-- Build a name from components. For example `from_components ["foo","bar"]` becomes
  ``` `foo.bar``` -/
def fromComponents : List String → Name :=
  fromComponentsAux Name.anonymous
#align name.from_components Name.fromComponents

/-- `name`s can contain numeral pieces, which are not legal names
  when typed/passed directly to the parser. We turn an arbitrary
  name into a legal identifier name by turning the numbers to strings. -/
unsafe def sanitize_name : Name → Name
  | Name.anonymous => Name.anonymous
  | Name.mk_string s p => Name.mk_string s <| sanitize_name p
  | Name.mk_numeral s p => (Name.mk_string s! "n{s}") <| sanitize_name p
#align name.sanitize_name name.sanitize_name

/-- Append a string to the last component of a name. -/
def appendSuffix : Name → String → Name
  | mk_string s n, s' => mk_string (s ++ s') n
  | n, _ => n
#align name.append_suffix Name.appendSuffix

/-- Update the last component of a name. -/
def updateLast (f : String → String) : Name → Name
  | mk_string s n => mk_string (f s) n
  | n => n
#align name.update_last Name.updateLast

/-- `append_to_last nm s is_prefix` adds `s` to the last component of `nm`,
  either as prefix or as suffix (specified by `is_prefix`), separated by `_`.
  Used by `simps_add_projections`. -/
def appendToLast (nm : Name) (s : String) (is_prefix : Bool) : Name :=
  nm.updateLast fun s' => if is_prefix then s ++ "_" ++ s' else s' ++ "_" ++ s
#align name.append_to_last Name.appendToLast

/-- The first component of a name, turning a number to a string -/
unsafe def head : Name → String
  | mk_string s anonymous => s
  | mk_string s p => head p
  | mk_numeral n p => head p
  | anonymous => "[anonymous]"
#align name.head name.head

/-- Tests whether the first component of a name is `"_private"` -/
unsafe def is_private (n : Name) : Bool :=
  n.head = "_private"
#align name.is_private name.is_private

/-- Returns the number of characters used to print all the string components of a name,
  including periods between name segments. Ignores numerical parts of a name. -/
unsafe def length : Name → ℕ
  | mk_string s anonymous => s.length
  | mk_string s p => s.length + 1 + p.length
  | mk_numeral n p => p.length
  | anonymous => "[anonymous]".length
#align name.length name.length

/-- Checks whether `nm` has a prefix (including itself) such that P is true -/
def hasPrefix (P : Name → Bool) : Name → Bool
  | anonymous => false
  | mk_string s nm => P (mk_string s nm) ∨ has_prefix nm
  | mk_numeral s nm => P (mk_numeral s nm) ∨ has_prefix nm
#align name.has_prefix Name.hasPrefix

/-- Appends `'` to the end of a name. -/
unsafe def add_prime : Name → Name
  | Name.mk_string s p => Name.mk_string (s ++ "'") p
  | n => Name.mk_string "x'" n
#align name.add_prime name.add_prime

/-- `last_string n` returns the rightmost component of `n`, ignoring numeral components.
For example, ``last_string `a.b.c.33`` will return `` `c ``. -/
def lastString : Name → String
  | anonymous => "[anonymous]"
  | mk_string s _ => s
  | mk_numeral _ n => last_string n
#align name.last_string Name.lastString

/-- Like `++`, except that if the right argument starts with `_root_` the namespace will be
ignored.
```
append_namespace `a.b `c.d = `a.b.c.d
append_namespace `a.b `_root_.c.d = `c.d
```
-/
unsafe def append_namespace (ns : Name) : Name → Name
  | mk_string s anonymous => if s = "_root_" then anonymous else mk_string s ns
  | mk_string s p => mk_string s (append_namespace p)
  | mk_numeral n p => mk_numeral n (append_namespace p)
  | anonymous => ns
#align name.append_namespace name.append_namespace

/-- Constructs a (non-simple) name from a string.

Example: ``name.from_string "foo.bar" = `foo.bar``
-/
unsafe def from_string (s : String) : Name :=
  from_components <| s.split (· = '.')
#align name.from_string name.from_string

library_note "likely generated binder names"/--
In surface Lean, we can write anonymous Π binders (i.e. binders where the
argument is not named) using the function arrow notation:

```lean
inductive test : Type
| intro : unit → test
```

After elaboration, however, every binder must have a name, so Lean generates
one. In the example, the binder in the type of `intro` is anonymous, so Lean
gives it the name `ᾰ`:

```lean
test.intro : ∀ (ᾰ : unit), test
```

When there are multiple anonymous binders, they are named `ᾰ_1`, `ᾰ_2` etc.

Thus, when we want to know whether the user named a binder, we can check whether
the name follows this scheme. Note, however, that this is not reliable. When the
user writes (for whatever reason)

```lean
inductive test : Type
| intro : ∀ (ᾰ : unit), test
```

we cannot tell that the binder was, in fact, named.

The function `name.is_likely_generated_binder_name` checks if
a name is of the form `ᾰ`, `ᾰ_1`, etc.
-/


/-- Check whether a simple name was likely generated by Lean to name an anonymous
binder. Such names are either `ᾰ` or `ᾰ_n` for some natural `n`. See
note [likely generated binder names].
-/
unsafe def is_likely_generated_binder_simple_name : String → Bool
  | "ᾰ" => true
  | n =>
    match n.getRest "ᾰ_" with
    | none => false
    | some suffix => suffix.isNat
#align name.is_likely_generated_binder_simple_name name.is_likely_generated_binder_simple_name

/-- Check whether a name was likely generated by Lean to name an anonymous binder.
Such names are either `ᾰ` or `ᾰ_n` for some natural `n`. See
note [likely generated binder names].
-/
unsafe def is_likely_generated_binder_name (n : Name) : Bool :=
  match n with
  | mk_string s anonymous => is_likely_generated_binder_simple_name s
  | _ => false
#align name.is_likely_generated_binder_name name.is_likely_generated_binder_name

end Name

namespace Level

/-! ### Declarations about `level` -/


/-- Tests whether a universe level is non-zero for all assignments of its variables -/
unsafe def nonzero : level → Bool
  | succ _ => true
  | max l₁ l₂ => l₁.nonzero || l₂.nonzero
  | imax _ l₂ => l₂.nonzero
  | _ => false
#align level.nonzero level.nonzero

/-- `l.fold_mvar f` folds a function `f : name → α → α`
over each `n : name` appearing in a `level.mvar n` in `l`.
-/
unsafe def fold_mvar {α} : level → (Name → α → α) → α → α
  | zero, f => id
  | succ a, f => fold_mvar a f
  | param a, f => id
  | mvar a, f => f a
  | max a b, f => fold_mvar a f ∘ fold_mvar b f
  | imax a b, f => fold_mvar a f ∘ fold_mvar b f
#align level.fold_mvar level.fold_mvar

/-- `l.params` is the set of parameters occuring in `l`.
For example if `l = max 1 (max (u+1) (max v w))` then `l.params = {u, v, w}`.
-/
protected unsafe def params (u : level) : name_set :=
  (u.fold mk_name_set) fun v l =>
    match v with
    | param nm => l.insert nm
    | _ => l
#align level.params level.params

end Level

/-! ### Declarations about `binder` -/


/-- The type of binders containing a name, the binding info and the binding type -/
unsafe structure binder where
  Name : Name
  info : BinderInfo
  type : expr
  deriving DecidableEq, Inhabited
#align binder binder

namespace Binder

/-- Turn a binder into a string. Uses expr.to_string for the type. -/
protected unsafe def to_string (b : binder) : String :=
  let (l, r) := b.info.brackets
  l ++ b.Name.toString ++ " : " ++ b.type.toString ++ r
#align binder.to_string binder.to_string

unsafe instance : ToString binder :=
  ⟨binder.to_string⟩

unsafe instance : has_to_format binder :=
  ⟨fun b => b.toString⟩

unsafe instance : has_to_tactic_format binder :=
  ⟨fun b =>
    let (l, r) := b.info.brackets
    (fun e => l ++ b.Name.toString ++ " : " ++ e ++ r) <$> pp b.type⟩

end Binder

/-!
### Converting between expressions and numerals

There are a number of ways to convert between expressions and numerals, depending on the input and
output types and whether you want to infer the necessary type classes.

See also the tactics `expr.of_nat`, `expr.of_int`, `expr.of_rat`.
-/


/-- `nat.mk_numeral n` embeds `n` as a numeral expression inside a type with 0, 1, and +.
`type`: an expression representing the target type. This must live in Type 0.
`has_zero`, `has_one`, `has_add`: expressions of the type `has_zero %%type`, etc.
 -/
unsafe def nat.mk_numeral (type has_zero has_one has_add : expr) : ℕ → expr :=
  let z : expr := q(@Zero.zero.{0} $(type) $(Zero))
  let o : expr := q(@One.one.{0} $(type) $(One))
  Nat.binaryRec z fun b n e =>
    if n = 0 then o
    else if b then q(@bit1.{0} $(type) $(One) $(Add) $(e)) else q(@bit0.{0} $(type) $(Add) $(e))
#align nat.mk_numeral nat.mk_numeral

/-- `int.mk_numeral z` embeds `z` as a numeral expression inside a type with 0, 1, +, and -.
`type`: an expression representing the target type. This must live in Type 0.
`has_zero`, `has_one`, `has_add`, `has_neg`: expressions of the type `has_zero %%type`, etc.
 -/
unsafe def int.mk_numeral (type has_zero has_one has_add has_neg : expr) : ℤ → expr
  | Int.ofNat n => n.mk_numeral type Zero One Add
  | -[n+1] =>
    let ne := (n + 1).mk_numeral type Zero One Add
    q(@Neg.neg.{0} $(type) $(Neg) $(Ne))
#align int.mk_numeral int.mk_numeral

/-- `nat.to_pexpr n` creates a `pexpr` that will evaluate to `n`.
The `pexpr` does not hold any typing information:
`to_expr ``((%%(nat.to_pexpr 5) : ℤ))` will create a native integer numeral `(5 : ℤ)`.
-/
unsafe def nat.to_pexpr : ℕ → pexpr
  | 0 => ``(0)
  | 1 => ``(1)
  | n => if n % 2 = 0 then ``(bit0 $(nat.to_pexpr n / 2)) else ``(bit1 $(nat.to_pexpr n / 2))
#align nat.to_pexpr nat.to_pexpr

/-- `int.to_pexpr n` creates a `pexpr` that will evaluate to `n`.
The `pexpr` does not hold any typing information:
`to_expr ``((%%(int.to_pexpr (-5)) : ℚ))` will create a native `ℚ` numeral `(-5 : ℚ)`.
-/
unsafe def int.to_pexpr : ℤ → pexpr
  | Int.ofNat k => k.to_pexpr
  | Int.negSucc k => ``(-$(k + 1.to_pexpr))
#align int.to_pexpr int.to_pexpr

namespace Expr

/-- Turns an expression into a natural number, assuming it is only built up from
`has_one.one`, `bit0`, `bit1`, `has_zero.zero`, `nat.zero`, and `nat.succ`.
-/
protected unsafe def to_nat : expr → Option ℕ
  | q(Zero.zero) => some 0
  | q(One.one) => some 1
  | q(bit0 $(e)) => bit0 <$> e.toNat
  | q(bit1 $(e)) => bit1 <$> e.toNat
  | q(Nat.succ $(e)) => (· + 1) <$> e.toNat
  | q(Nat.zero) => some 0
  | _ => none
#align expr.to_nat expr.to_nat

/-- Turns an expression into a integer, assuming it is only built up from
`has_one.one`, `bit0`, `bit1`, `has_zero.zero` and a optionally a single `has_neg.neg` as head.
-/
protected unsafe def to_int : expr → Option ℤ
  | q(Neg.neg $(e)) => do
    let n ← e.toNat
    some (-n)
  | e => coe <$> e.toNat
#align expr.to_int expr.to_int

/-- Turns an expression into a list, assuming it is only built up from `list.nil` and `list.cons`.
-/
protected unsafe def to_list {α} (f : expr → Option α) : expr → Option (List α)
  | q(List.nil) => some []
  | q(List.cons $(x) $(l)) => List.cons <$> f x <*> l.toList
  | _ => none
#align expr.to_list expr.to_list

-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      `is_num_eq n1 n2` returns true if `n1` and `n2` are both numerals with the same numeral structure,
      ignoring differences in type and type class arguments.
      -/
    unsafe
  def
    is_num_eq
    : expr → expr → Bool
    | q( @ Zero.zero _ _ ) , q( @ Zero.zero _ _ ) => true
      | q( @ One.one _ _ ) , q( @ One.one _ _ ) => true
      | q( bit0 $ ( a ) ) , q( bit0 $ ( b ) ) => a . is_num_eq b
      | q( bit1 $ ( a ) ) , q( bit1 $ ( b ) ) => a . is_num_eq b
      | q( - $ ( a ) ) , q( - $ ( b ) ) => a . is_num_eq b
      | q( $ ( a ) / $ ( a' ) ) , q( $ ( b ) / $ ( b' ) ) => a . is_num_eq b
      | _ , _ => false
#align expr.is_num_eq expr.is_num_eq

end Expr

/-! ### Declarations about `pexpr` -/


namespace Pexpr

/-- If `e` is an annotation of `frozen_name` to `expr.const n`,
`e.get_frozen_name` returns `n`.
Otherwise, returns `name.anonymous`.
-/
unsafe def get_frozen_name (e : pexpr) : Name :=
  match e.is_annotation with
  | some (`frozen_name, expr.const n _) => n
  | _ => Name.anonymous
#align pexpr.get_frozen_name pexpr.get_frozen_name

/-- If `e : pexpr` is a sequence of applications `f e₁ e₂ ... eₙ`,
`e.get_app_fn_args` returns `(f, [e₁, ... eₙ])`.
See also `expr.get_app_fn_args`.
-/
unsafe def get_app_fn_args : pexpr → optParam (List pexpr) [] → pexpr × List pexpr
  | expr.app e1 e2, r => get_app_fn_args e1 (e2 :: r)
  | e1, r => (e1, r)
#align pexpr.get_app_fn_args pexpr.get_app_fn_args

/-- If `e : pexpr` is a sequence of applications `f e₁ e₂ ... eₙ`,
`e.get_app_fn` returns `f`.
See also `expr.get_app_fn`.
-/
unsafe def get_app_fn : pexpr → List pexpr :=
  Prod.snd ∘ get_app_fn_args
#align pexpr.get_app_fn pexpr.get_app_fn

/-- If `e : pexpr` is a sequence of applications `f e₁ e₂ ... eₙ`,
`e.get_app_args` returns `[e₁, ... eₙ]`.
See also `expr.get_app_args`.
-/
unsafe def get_app_args : pexpr → List pexpr :=
  Prod.snd ∘ get_app_fn_args
#align pexpr.get_app_args pexpr.get_app_args

end Pexpr

/-! ### Declarations about `expr` -/


namespace Expr

/-- List of names removed by `clean`. All these names must resolve to functions defeq `id`. -/
unsafe def clean_ids : List Name :=
  [`` id, `` idRhs, `` idDelta, `` hidden]
#align expr.clean_ids expr.clean_ids

/-- Clean an expression by removing `id`s listed in `clean_ids`. -/
unsafe def clean (e : expr) : expr :=
  e.replace fun e n =>
    match e with
    | app (app (const n _) _) e' => if n ∈ clean_ids then some e' else none
    | app (lam _ _ _ (var 0)) e' => some e'
    | _ => none
#align expr.clean expr.clean

/-- `replace_with e s s'` replaces ocurrences of `s` with `s'` in `e`. -/
unsafe def replace_with (e : expr) (s : expr) (s' : expr) : expr :=
  e.replace fun c d => if c = s then some (s'.lift_vars 0 d) else none
#align expr.replace_with expr.replace_with

/-- Implementation of `expr.mreplace`. -/
unsafe def mreplace_aux {m : Type _ → Type _} [Monad m] (R : expr → Nat → m (Option expr)) :
    expr → ℕ → m expr
  | app f x, n =>
    Option.getDM (R (app f x) n) do
      let Rf ← mreplace_aux f n
      let Rx ← mreplace_aux x n
      return <| app Rf Rx
  | lam nm bi ty bd, n =>
    Option.getDM (R (lam nm bi ty bd) n) do
      let Rty ← mreplace_aux ty n
      let Rbd ← mreplace_aux bd (n + 1)
      return <| lam nm bi Rty Rbd
  | pi nm bi ty bd, n =>
    Option.getDM (R (pi nm bi ty bd) n) do
      let Rty ← mreplace_aux ty n
      let Rbd ← mreplace_aux bd (n + 1)
      return <| pi nm bi Rty Rbd
  | elet nm ty a b, n =>
    Option.getDM (R (elet nm ty a b) n) do
      let Rty ← mreplace_aux ty n
      let Ra ← mreplace_aux a n
      let Rb ← mreplace_aux b n
      return <| elet nm Rty Ra Rb
  | macro c es, n =>
    Option.getDM (R (macro c es) n) <| macro c <$> es.mmap fun e => mreplace_aux e n
  | e, n => Option.getDM (R e n) (return e)
#align expr.mreplace_aux expr.mreplace_aux

/-- Monadic analogue of `expr.replace`.

The `mreplace R e` visits each subexpression `s` of `e`, and is called with `R s n`, where
`n` is the number of binders above `e`.
If `R s n` fails, the whole replacement fails.
If `R s n` returns `some t`, `s` is replaced with `t` (and `mreplace` does not visit
its subexpressions).
If `R s n` return `none`, then `mreplace` continues visiting subexpressions of `s`.

WARNING: This function performs exponentially worse on large terms than `expr.replace`,
if a subexpression occurs more than once in an expression, `expr.replace` visits them only once,
but this function will visit every occurence of it. Do not use this on large expressions.
-/
unsafe def mreplace {m : Type _ → Type _} [Monad m] (R : expr → Nat → m (Option expr)) (e : expr) :
    m expr :=
  mreplace_aux R e 0
#align expr.mreplace expr.mreplace

/-- Match a variable. -/
unsafe def match_var {elab} : expr elab → Option ℕ
  | var n => some n
  | _ => none
#align expr.match_var expr.match_var

/-- Match a sort. -/
unsafe def match_sort {elab} : expr elab → Option level
  | sort u => some u
  | _ => none
#align expr.match_sort expr.match_sort

/-- Match a constant. -/
unsafe def match_const {elab} : expr elab → Option (Name × List level)
  | const n lvls => some (n, lvls)
  | _ => none
#align expr.match_const expr.match_const

/-- Match a metavariable. -/
unsafe def match_mvar {elab} : expr elab → Option (Name × Name × expr elab)
  | mvar unique pretty type => some (unique, pretty, type)
  | _ => none
#align expr.match_mvar expr.match_mvar

/-- Match a local constant. -/
unsafe def match_local_const {elab} : expr elab → Option (Name × Name × BinderInfo × expr elab)
  | local_const unique pretty bi type => some (unique, pretty, bi, type)
  | _ => none
#align expr.match_local_const expr.match_local_const

/-- Match an application. -/
unsafe def match_app {elab} : expr elab → Option (expr elab × expr elab)
  | app t u => some (t, u)
  | _ => none
#align expr.match_app expr.match_app

/-- Match an application of `coe_fn`. -/
unsafe def match_app_coe_fn : expr → Option (expr × expr × expr × expr × expr)
  | app q(@coeFn $(α) $(β) $(inst) $(fexpr)) x => some (α, β, inst, fexpr, x)
  | _ => none
#align expr.match_app_coe_fn expr.match_app_coe_fn

/-- Match an abstraction. -/
unsafe def match_lam {elab} : expr elab → Option (Name × BinderInfo × expr elab × expr elab)
  | lam var_name bi type body => some (var_name, bi, type, body)
  | _ => none
#align expr.match_lam expr.match_lam

/-- Match a Π type. -/
unsafe def match_pi {elab} : expr elab → Option (Name × BinderInfo × expr elab × expr elab)
  | pi var_name bi type body => some (var_name, bi, type, body)
  | _ => none
#align expr.match_pi expr.match_pi

/-- Match a let. -/
unsafe def match_elet {elab} : expr elab → Option (Name × expr elab × expr elab × expr elab)
  | elet var_name type assignment body => some (var_name, type, assignment, body)
  | _ => none
#align expr.match_elet expr.match_elet

/-- Match a macro. -/
unsafe def match_macro {elab} : expr elab → Option (macro_def × List (expr elab))
  | macro df args => some (df, args)
  | _ => none
#align expr.match_macro expr.match_macro

/-- Tests whether an expression is a meta-variable. -/
unsafe def is_mvar : expr → Bool
  | mvar _ _ _ => true
  | _ => false
#align expr.is_mvar expr.is_mvar

/-- Tests whether an expression is a sort. -/
unsafe def is_sort : expr → Bool
  | sort _ => true
  | e => false
#align expr.is_sort expr.is_sort

/-- Get the universe levels of a `const` expression -/
unsafe def univ_levels : expr → List level
  | const n ls => ls
  | _ => []
#align expr.univ_levels expr.univ_levels

/-- Replace any metavariables in the expression with underscores, in preparation for printing
`refine ...` statements.
-/
unsafe def replace_mvars (e : expr) : expr :=
  e.replace fun e' _ => if e'.is_mvar then some (unchecked_cast pexpr.mk_placeholder) else none
#align expr.replace_mvars expr.replace_mvars

/-- If `e` is a local constant, `to_implicit_local_const e` changes the binder info of `e` to
 `implicit`. See also `to_implicit_binder`, which also changes lambdas and pis. -/
unsafe def to_implicit_local_const : expr → expr
  | expr.local_const uniq n bi t => expr.local_const uniq n BinderInfo.implicit t
  | e => e
#align expr.to_implicit_local_const expr.to_implicit_local_const

/-- If `e` is a local constant, lamda, or pi expression, `to_implicit_binder e` changes the binder
info of `e` to `implicit`. See also `to_implicit_local_const`, which only changes local constants.
-/
unsafe def to_implicit_binder : expr → expr
  | local_const n₁ n₂ _ d => local_const n₁ n₂ BinderInfo.implicit d
  | lam n _ d b => lam n BinderInfo.implicit d b
  | pi n _ d b => pi n BinderInfo.implicit d b
  | e => e
#align expr.to_implicit_binder expr.to_implicit_binder

/-- Returns a list of all local constants in an expression (without duplicates). -/
unsafe def list_local_consts (e : expr) : List expr :=
  e.fold [] fun e' _ es => if e'.is_local_constant then insert e' es else es
#align expr.list_local_consts expr.list_local_consts

/-- Returns the set of all local constants in an expression. -/
unsafe def list_local_consts' (e : expr) : expr_set :=
  e.fold mk_expr_set fun e' _ es => if e'.is_local_constant then es.insert e' else es
#align expr.list_local_consts' expr.list_local_consts'

/-- Returns the unique names of all local constants in an expression. -/
unsafe def list_local_const_unique_names (e : expr) : name_set :=
  e.fold mk_name_set fun e' _ es =>
    if e'.is_local_constant then es.insert e'.local_uniq_name else es
#align expr.list_local_const_unique_names expr.list_local_const_unique_names

/-- Returns a `name_set` of all constants in an expression. -/
unsafe def list_constant (e : expr) : name_set :=
  e.fold mk_name_set fun e' _ es => if e'.is_constant then es.insert e'.const_name else es
#align expr.list_constant expr.list_constant

/-- Returns a `list name` containing the constant names of an `expr` in the same order
  that `expr.fold` traverses it. -/
unsafe def list_constant' (e : expr) : List Name :=
  (e.fold [] fun e' _ es => if e'.is_constant then es.insert e'.const_name else es).reverse
#align expr.list_constant' expr.list_constant'

/-- Returns a list of all meta-variables in an expression (without duplicates). -/
unsafe def list_meta_vars (e : expr) : List expr :=
  e.fold [] fun e' _ es => if e'.is_mvar then insert e' es else es
#align expr.list_meta_vars expr.list_meta_vars

/-- Returns the set of all meta-variables in an expression. -/
unsafe def list_meta_vars' (e : expr) : expr_set :=
  e.fold mk_expr_set fun e' _ es => if e'.is_mvar then es.insert e' else es
#align expr.list_meta_vars' expr.list_meta_vars'

/-- Returns a list of all universe meta-variables in an expression (without duplicates). -/
unsafe def list_univ_meta_vars (e : expr) : List Name :=
  native.rb_set.to_list <|
    (e.fold native.mk_rb_set) fun e' i s =>
      match e' with
      | sort u => u.fold_mvar (flip native.rb_set.insert) s
      | const _ ls => ls.foldl (fun s' l => l.fold_mvar (flip native.rb_set.insert) s') s
      | _ => s
#align expr.list_univ_meta_vars expr.list_univ_meta_vars

/-- Test `t` contains the specified subexpression `e`, or a metavariable.
This represents the notion that `e` "may occur" in `t`,
possibly after subsequent unification.
-/
unsafe def contains_expr_or_mvar (t : expr) (e : expr) : Bool :=
  -- We can't use `t.has_meta_var` here, as that detects universe metavariables, too.
    ¬t.list_meta_vars.Empty ∨
    e.occurs t
#align expr.contains_expr_or_mvar expr.contains_expr_or_mvar

/-- Returns a `name_set` of all constants in an expression starting with a certain prefix. -/
unsafe def list_names_with_prefix (pre : Name) (e : expr) : name_set :=
  (e.fold mk_name_set) fun e' _ l =>
    match e' with
    | expr.const n _ => if n.getPrefix = pre then l.insert n else l
    | _ => l
#align expr.list_names_with_prefix expr.list_names_with_prefix

/-- Returns true if `e` contains a name `n` where `p n` is true.
  Returns `true` if `p name.anonymous` is true. -/
unsafe def contains_constant (e : expr) (p : Name → Prop) [DecidablePred p] : Bool :=
  e.fold false fun e' _ b => if p e'.const_name then true else b
#align expr.contains_constant expr.contains_constant

/-- Returns true if `e` contains a `sorry`.
See also `name.contains_sorry`.
-/
unsafe def contains_sorry (e : expr) : Bool :=
  e.fold false fun e' _ b => if (is_sorry e').isSome then true else b
#align expr.contains_sorry expr.contains_sorry

/-- `app_symbol_in e l` returns true iff `e` is an application of a constant whose name is in `l`.
-/
unsafe def app_symbol_in (e : expr) (l : List Name) : Bool :=
  match e.get_app_fn with
  | expr.const n _ => n ∈ l
  | _ => false
#align expr.app_symbol_in expr.app_symbol_in

/-- `get_simp_args e` returns the arguments of `e` that simp can reach via congruence lemmas. -/
unsafe def get_simp_args (e : expr) : tactic (List expr) :=
  if-- `mk_specialized_congr_lemma_simp` throws an assertion violation if its argument is not an app
      ¬e.is_app then
    pure []
  else do
    let cgr ← mk_specialized_congr_lemma_simp e
    pure do
        let (arg_kind, arg) ← cgr e
        guard <| arg_kind = CongrArgKind.eq
        pure arg
#align expr.get_simp_args expr.get_simp_args

/-- Simplifies the expression `t` with the specified options.
  The result is `(new_e, pr)` with the new expression `new_e` and a proof
  `pr : e = new_e`. -/
unsafe def simp (t : expr) (cfg : SimpConfig := { }) (discharger : tactic Unit := failed)
    (no_defaults := false) (attr_names : List Name := []) (hs : List simp_arg_type := []) :
    tactic (expr × expr × name_set) := do
  let (s, to_unfold) ← mk_simp_set no_defaults attr_names hs
  simplify s to_unfold t cfg `eq discharger
#align expr.simp expr.simp

/-- Definitionally simplifies the expression `t` with the specified options.
  The result is the simplified expression. -/
unsafe def dsimp (t : expr) (cfg : DsimpConfig := { }) (no_defaults := false)
    (attr_names : List Name := []) (hs : List simp_arg_type := []) : tactic expr := do
  let (s, to_unfold) ← mk_simp_set no_defaults attr_names hs
  s to_unfold t cfg
#align expr.dsimp expr.dsimp

/-- Get the names of the bound variables by a sequence of pis or lambdas. -/
unsafe def binding_names : expr → List Name
  | pi n _ _ e => n :: e.binding_names
  | lam n _ _ e => n :: e.binding_names
  | e => []
#align expr.binding_names expr.binding_names

/-- head-reduce a single let expression -/
unsafe def reduce_let : expr → expr
  | elet _ _ v b => b.instantiate_var v
  | e => e
#align expr.reduce_let expr.reduce_let

/-- head-reduce all let expressions -/
unsafe def reduce_lets : expr → expr
  | elet _ _ v b => reduce_lets <| b.instantiate_var v
  | e => e
#align expr.reduce_lets expr.reduce_lets

/-- Instantiate lambdas in the second argument by expressions from the first. -/
unsafe def instantiate_lambdas : List expr → expr → expr
  | e' :: es, lam n bi t e => instantiate_lambdas es (e.instantiate_var e')
  | _, e => e
#align expr.instantiate_lambdas expr.instantiate_lambdas

/-- Repeatedly apply `expr.subst`. -/
unsafe def substs : expr → List expr → expr
  | e, es => es.foldl expr.subst e
#align expr.substs expr.substs

/-- `instantiate_lambdas_or_apps es e` instantiates lambdas in `e` by expressions from `es`.
If the length of `es` is larger than the number of lambdas in `e`,
then the term is applied to the remaining terms.
Also reduces head let-expressions in `e`, including those after instantiating all lambdas.

This is very similar to `expr.substs`, but this also reduces head let-expressions. -/
unsafe def instantiate_lambdas_or_apps : List expr → expr → expr
  | v :: es, lam n bi t b => instantiate_lambdas_or_apps es <| b.instantiate_var v
  | es, elet _ _ v b => instantiate_lambdas_or_apps es <| b.instantiate_var v
  | es, e => mk_app e es
#align expr.instantiate_lambdas_or_apps expr.instantiate_lambdas_or_apps

library_note "open expressions"/--
Some declarations work with open expressions, i.e. an expr that has free variables.
Terms will free variables are not well-typed, and one should not use them in tactics like
`infer_type` or `unify`. You can still do syntactic analysis/manipulation on them.
The reason for working with open types is for performance: instantiating variables requires
iterating through the expression. In one performance test `pi_binders` was more than 6x
quicker than `mk_local_pis` (when applied to the type of all imported declarations 100x).
-/


/-- Get the codomain/target of a pi-type.
  This definition doesn't instantiate bound variables, and therefore produces a term that is open.
  See note [open expressions]. -/
unsafe def pi_codomain : expr → expr
  | pi n bi d b => pi_codomain b
  | e => e
#align expr.pi_codomain expr.pi_codomain

/-- Get the body/value of a lambda-expression.
  This definition doesn't instantiate bound variables, and therefore produces a term that is open.
  See note [open expressions]. -/
unsafe def lambda_body : expr → expr
  | lam n bi d b => lambda_body b
  | e => e
#align expr.lambda_body expr.lambda_body

/-- Auxiliary defintion for `pi_binders`.
  See note [open expressions]. -/
unsafe def pi_binders_aux : List binder → expr → List binder × expr
  | es, pi n bi d b => pi_binders_aux (⟨n, bi, d⟩ :: es) b
  | es, e => (es, e)
#align expr.pi_binders_aux expr.pi_binders_aux

/-- Get the binders and codomain of a pi-type.
  This definition doesn't instantiate bound variables, and therefore produces a term that is open.
  The.tactic `get_pi_binders` in `tactic.core` does the same, but also instantiates the
  free variables.
  See note [open expressions]. -/
unsafe def pi_binders (e : expr) : List binder × expr :=
  let (es, e) := pi_binders_aux [] e
  (es.reverse, e)
#align expr.pi_binders expr.pi_binders

/-- Auxiliary defintion for `get_app_fn_args`. -/
unsafe def get_app_fn_args_aux : List expr → expr → expr × List expr
  | r, app f a => get_app_fn_args_aux (a :: r) f
  | r, e => (e, r)
#align expr.get_app_fn_args_aux expr.get_app_fn_args_aux

/-- A combination of `get_app_fn` and `get_app_args`: lists both the
  function and its arguments of an application -/
unsafe def get_app_fn_args : expr → expr × List expr :=
  get_app_fn_args_aux []
#align expr.get_app_fn_args expr.get_app_fn_args

/-- `drop_pis es e` instantiates the pis in `e` with the expressions from `es`. -/
unsafe def drop_pis : List expr → expr → tactic expr
  | v :: vs, pi n bi d b => do
    let t ← infer_type v
    guard (t == d)
    drop_pis vs (b v)
  | [], e => return e
  | _, _ => failed
#align expr.drop_pis expr.drop_pis

/-- `instantiate_pis es e` instantiates the pis in `e` with the expressions from `es`.
  Does not check whether the result remains type-correct. -/
unsafe def instantiate_pis : List expr → expr → expr
  | v :: vs, pi n bi d b => instantiate_pis vs (b.instantiate_var v)
  | _, e => e
#align expr.instantiate_pis expr.instantiate_pis

/-- `mk_op_lst op empty [x1, x2, ...]` is defined as `op x1 (op x2 ...)`.
  Returns `empty` if the list is empty. -/
unsafe def mk_op_lst (op : expr) (empty : expr) : List expr → expr
  | [] => Empty
  | [e] => e
  | e :: es => op e <| mk_op_lst es
#align expr.mk_op_lst expr.mk_op_lst

/-- `mk_and_lst [x1, x2, ...]` is defined as `x1 ∧ (x2 ∧ ...)`, or `true` if the list is empty. -/
unsafe def mk_and_lst : List expr → expr :=
  mk_op_lst q(And) q(True)
#align expr.mk_and_lst expr.mk_and_lst

/-- `mk_or_lst [x1, x2, ...]` is defined as `x1 ∨ (x2 ∨ ...)`, or `false` if the list is empty. -/
unsafe def mk_or_lst : List expr → expr :=
  mk_op_lst q(Or) q(False)
#align expr.mk_or_lst expr.mk_or_lst

/-- `local_binding_info e` returns the binding info of `e` if `e` is a local constant.
Otherwise returns `binder_info.default`. -/
unsafe def local_binding_info : expr → BinderInfo
  | expr.local_const _ _ bi _ => bi
  | _ => BinderInfo.default
#align expr.local_binding_info expr.local_binding_info

/-- `is_default_local e` tests whether `e` is a local constant with binder info
`binder_info.default` -/
unsafe def is_default_local : expr → Bool
  | expr.local_const _ _ BinderInfo.default _ => true
  | _ => false
#align expr.is_default_local expr.is_default_local

/-- `has_local_constant e l` checks whether local constant `l` occurs in expression `e` -/
unsafe def has_local_constant (e l : expr) : Bool :=
  e.has_local_in <| mk_name_set.insert l.local_uniq_name
#align expr.has_local_constant expr.has_local_constant

/-- Turns a local constant into a binder -/
unsafe def to_binder : expr → binder
  | local_const _ nm bi t => ⟨nm, bi, t⟩
  | _ => default
#align expr.to_binder expr.to_binder

/-- Strip-away the context-dependent unique id for the given local const and return: its friendly
`name`, its `binder_info`, and its `type : expr`. -/
unsafe def get_local_const_kind : expr → Name × BinderInfo × expr
  | expr.local_const _ n bi e => (n, bi, e)
  | _ => (Name.anonymous, BinderInfo.default, expr.const Name.anonymous [])
#align expr.get_local_const_kind expr.get_local_const_kind

/-- `local_const_set_type e t` sets the type of `e` to `t`, if `e` is a `local_const`. -/
unsafe def local_const_set_type {elab : Bool} : expr elab → expr elab → expr elab
  | expr.local_const x n bi t, new_t => expr.local_const x n bi new_t
  | e, new_t => e
#align expr.local_const_set_type expr.local_const_set_type

/-- `unsafe_cast e` freely changes the `elab : bool` parameter of the passed `expr`. Mainly used to
access core `expr` manipulation functions for `pexpr`-based use, but which are restricted to
`expr tt` at the site of definition unnecessarily.

DANGER: Unless you know exactly what you are doing, this is probably not the function you are
looking for. For `pexpr → expr` see `tactic.to_expr`. For `expr → pexpr` see `to_pexpr`. -/
unsafe def unsafe_cast {elab₁ elab₂ : Bool} : expr elab₁ → expr elab₂ :=
  unchecked_cast
#align expr.unsafe_cast expr.unsafe_cast

/-- `replace_subexprs e mappings` takes an `e : expr` and interprets a `list (expr × expr)` as
a collection of rules for variable replacements. A pair `(f, t)` encodes a rule which says "whenever
`f` is encountered in `e` verbatim, replace it with `t`". -/
unsafe def replace_subexprs {elab : Bool} (e : expr elab) (mappings : List (expr × expr)) :
    expr elab :=
  unsafe_cast <|
    e.unsafe_cast.replace fun e n =>
      (mappings.filter fun ent : expr × expr => ent.1 = e).head'.map Prod.snd
#align expr.replace_subexprs expr.replace_subexprs

/-- `is_implicitly_included_variable e vs` accepts `e`, an `expr.local_const`, and a list `vs` of
    other `expr.local_const`s. It determines whether `e` should be considered "available in context"
    as a variable by virtue of the fact that the variables `vs` have been deemed such.

    For example, given `variables (n : ℕ) [prime n] [ih : even n]`, a reference to `n` implies that
    the typeclass instance `prime n` should be included, but `ih : even n` should not.

    DANGER: It is possible that for `f : expr` another `expr.local_const`, we have
    `is_implicitly_included_variable f vs = ff` but
    `is_implicitly_included_variable f (e :: vs) = tt`. This means that one usually wants to
    iteratively add a list of local constants (usually, the `variables` declared in the local scope)
    which satisfy `is_implicitly_included_variable` to an initial `vs`, repeating if any variables
    were added in a particular iteration. The function `all_implicitly_included_variables` below
    implements this behaviour.

    Note that if `e ∈ vs` then `is_implicitly_included_variable e vs = tt`. -/
unsafe def is_implicitly_included_variable (e : expr) (vs : List expr) : Bool :=
  if ¬e.local_pp_name.toString.startsWith "_" then e ∈ vs
  else
    (e.local_type.fold true) fun se _ b =>
      if ¬b then false else if ¬se.is_local_constant then true else se ∈ vs
#align expr.is_implicitly_included_variable expr.is_implicitly_included_variable

/-- Private work function for `all_implicitly_included_variables`, performing the actual series of
    iterations, tracking with a boolean whether any updates occured this iteration. -/
private unsafe def all_implicitly_included_variables_aux :
    List expr → List expr → List expr → Bool → List expr
  | [], vs, rs, tt => all_implicitly_included_variables_aux rs vs [] false
  | [], vs, rs, ff => vs
  | e :: rest, vs, rs, b =>
    let (vs, rs, b) :=
      if e.is_implicitly_included_variable vs then (e :: vs, rs, true) else (vs, e :: rs, b)
    all_implicitly_included_variables_aux rest vs rs b
#align expr.all_implicitly_included_variables_aux expr.all_implicitly_included_variables_aux

/-- `all_implicitly_included_variables es vs` accepts `es`, a list of `expr.local_const`, and `vs`,
    another such list. It returns a list of all variables `e` in `es` or `vs` for which an inclusion
    of the variables in `vs` into the local context implies that `e` should also be included. See
    `is_implicitly_included_variable e vs` for the details.

    In particular, those elements of `vs` are included automatically. -/
unsafe def all_implicitly_included_variables (es vs : List expr) : List expr :=
  all_implicitly_included_variables_aux es vs [] false
#align expr.all_implicitly_included_variables expr.all_implicitly_included_variables

/-- Get the list of explicit arguments of a function. -/
unsafe def list_explicit_args (f : expr) : tactic (List expr) :=
  tactic.fold_explicit_args f [] fun ll e => return <| ll ++ [e]
#align expr.list_explicit_args expr.list_explicit_args

/-- `replace_explicit_args f parg` assumes that `f` is an expression corresponding to a function
application.  It replaces the explicit arguments of `f`, in succession, by the elements of `parg`.
The implicit arguments of `f` remain unchanged. -/
unsafe def replace_explicit_args (f : expr) (parg : List expr) : tactic expr := do
  let finf ← get_fun_info f.get_app_fn
  let is_ex_arg : List Bool := finf.params.map fun e => ¬e.isImplicit ∧ ¬e.isInstImplicit
  let nargs := List.replaceIf f.get_app_args is_ex_arg parg
  return <| expr.mk_app f nargs
#align expr.replace_explicit_args expr.replace_explicit_args

/-- Infer the type of an application of the form `f x1 x2 ... xn`, where `f` is an identifier.
This also works if `x1, ... xn` contain free variables. -/
protected unsafe def simple_infer_type (env : environment) (e : expr) : exceptional expr := do
  let (@const tt n ls, es) ← return e.get_app_fn_args |
    exceptional.fail "expression is not a constant applied to arguments"
  let d ← env.get n
  return <| (d es).instantiate_univ_params <| d ls
#align expr.simple_infer_type expr.simple_infer_type

/-- Auxilliary function for `head_eta_expand`. -/
unsafe def head_eta_expand_aux : ℕ → expr → expr → expr
  | n + 1, e, pi x bi d b => lam x bi d <| head_eta_expand_aux n e b
  | _, e, _ => e
#align expr.head_eta_expand_aux expr.head_eta_expand_aux

/-- `head_eta_expand n e t` eta-expands `e` `n` times, with the binders info and domains obtained
  by its type `t`. -/
unsafe def head_eta_expand (n : ℕ) (e t : expr) : expr :=
  ((e.lift_vars 0 n).mk_app <| (List.range n).reverse.map var).head_eta_expand_aux n t
#align expr.head_eta_expand expr.head_eta_expand

/-- `e.eta_expand env dict` eta-expands all expressions that have as head a constant `n` in
`dict`. They are expanded until they are applied to one more argument than the maximum in
`dict.find n`. -/
protected unsafe def eta_expand (env : environment) (dict : name_map <| List ℕ) : expr → expr
  | e =>
    e.replace fun e _ => do
      let (e0, es) := e.get_app_fn_args
      let ns := (dict.find e0.const_name).iget
      guard (not ns)
      let e' := e0.mk_app <| es.map eta_expand
      let needed_n := ns.foldr max 0 + 1
      if needed_n ≤ es then some e'
        else do
          let e'_type ← (e' env).toOption
          some <| head_eta_expand (needed_n - es) e' e'_type
#align expr.eta_expand expr.eta_expand

/-- `e.apply_replacement_fun f test` applies `f` to each identifier
(inductive type, defined function etc) in an expression, unless
* The identifier occurs in an application with first argument `arg`; and
* `test arg` is false.
However, if `f` is in the dictionary `relevant`, then the argument `relevant.find f`
is tested, instead of the first argument.

Reorder contains the information about what arguments to reorder:
e.g. `g x₁ x₂ x₃ ... xₙ` becomes `g x₂ x₁ x₃ ... xₙ` if `reorder.find g = some [1]`.
We assume that all functions where we want to reorder arguments are fully applied.
This can be done by applying `expr.eta_expand` first.
-/
protected unsafe def apply_replacement_fun (f : Name → Name) (test : expr → Bool)
    (relevant : name_map ℕ) (reorder : name_map <| List ℕ) : expr → expr
  | e =>
    e.replace fun e _ =>
      match e with
      | const n ls =>
        some <|
          const
              (f
                n) <|-- if the first two arguments are reordered, we also reorder the first two universe parameters
              if 1 ∈ (reorder.find n).iget then ls.inth 1 :: ls.head :: ls.drop 2
            else ls
      | app g x =>
        let f := g.get_app_fn
        let nm := f.const_name
        let n_args := g.get_app_num_args
        -- this might be inefficient
          if n_args ∈ (reorder.find nm).iget ∧ test g.get_app_args.head then
          -- interchange `x` and the last argument of `g`
            some <|
            apply_replacement_fun g.app_fn (apply_replacement_fun x) <|
              apply_replacement_fun g.app_arg
        else
          if n_args = (relevant.find nm).lhoare 0 ∧ f.is_constant ∧ ¬test x then
            some <| (f.mk_app <| g.get_app_args.map apply_replacement_fun) (apply_replacement_fun x)
          else none
      | _ => none
#align expr.apply_replacement_fun expr.apply_replacement_fun

end Expr

/-! ### Declarations about `environment` -/


namespace Environment

/-- Tests whether `n` is a structure. -/
unsafe def is_structure (env : environment) (n : Name) : Bool :=
  (env.structure_fields n).isSome
#align environment.is_structure environment.is_structure

/-- Get the full names of all projections of the structure `n`. Returns `none` if `n` is not a
  structure. -/
unsafe def structure_fields_full (env : environment) (n : Name) : Option (List Name) :=
  (env.structure_fields n).map (List.map fun n' => n ++ n')
#align environment.structure_fields_full environment.structure_fields_full

/-- Tests whether `nm` is a generalized inductive type that is not a normal inductive type.
  Note that `is_ginductive` returns `tt` even on regular inductive types.
  This returns `tt` if `nm` is (part of a) mutually defined inductive type or a nested inductive
  type. -/
unsafe def is_ginductive' (e : environment) (nm : Name) : Bool :=
  e.is_ginductive nm ∧ ¬e.is_inductive nm
#align environment.is_ginductive' environment.is_ginductive'

/-- For all declarations `d` where `f d = some x` this adds `x` to the returned list.  -/
unsafe def decl_filter_map {α : Type} (e : environment) (f : declaration → Option α) : List α :=
  (e.fold []) fun d l =>
    match f d with
    | some r => r :: l
    | none => l
#align environment.decl_filter_map environment.decl_filter_map

/-- Maps `f` to all declarations in the environment. -/
unsafe def decl_map {α : Type} (e : environment) (f : declaration → α) : List α :=
  e.decl_filter_map fun d => some (f d)
#align environment.decl_map environment.decl_map

/-- Lists all declarations in the environment -/
unsafe def get_decls (e : environment) : List declaration :=
  e.decl_map id
#align environment.get_decls environment.get_decls

/-- Lists all trusted (non-meta) declarations in the environment -/
unsafe def get_trusted_decls (e : environment) : List declaration :=
  e.decl_filter_map fun d => if d.is_trusted then some d else none
#align environment.get_trusted_decls environment.get_trusted_decls

/-- Lists the name of all declarations in the environment -/
unsafe def get_decl_names (e : environment) : List Name :=
  e.decl_map declaration.to_name
#align environment.get_decl_names environment.get_decl_names

/-- Fold a monad over all declarations in the environment. -/
unsafe def mfold {α : Type} {m : Type → Type} [Monad m] (e : environment) (x : α)
    (fn : declaration → α → m α) : m α :=
  e.fold (return x) fun d t => t >>= fn d
#align environment.mfold environment.mfold

/-- Filters all declarations in the environment. -/
unsafe def filter (e : environment) (test : declaration → Bool) : List declaration :=
  (e.fold []) fun d ds => if test d then d :: ds else ds
#align environment.filter environment.filter

/-- Filters all declarations in the environment. -/
unsafe def mfilter (e : environment) (test : declaration → tactic Bool) :
    tactic (List declaration) :=
  (e.mfold []) fun d ds => do
    let b ← test d
    return <| if b then d :: ds else ds
#align environment.mfilter environment.mfilter

/-- Checks whether `s` is a prefix of the file where `n` is declared.
  This is used to check whether `n` is declared in mathlib, where `s` is the mathlib directory. -/
unsafe def is_prefix_of_file (e : environment) (s : String) (n : Name) : Bool :=
  s.isPrefixOf <| (e.decl_olean n).getOrElse ""
#align environment.is_prefix_of_file environment.is_prefix_of_file

end Environment

/-!
### `is_eta_expansion`

 In this section we define the tactic `is_eta_expansion` which checks whether an expression
  is an eta-expansion of a structure. (not to be confused with eta-expanion for `λ`).

-/


namespace Expr

/-- `is_eta_expansion_of args univs l` checks whether for all elements `(nm, pr)` in `l` we have
  `pr = nm.{univs} args`.
  Used in `is_eta_expansion`, where `l` consists of the projections and the fields of the value we
  want to eta-reduce. -/
unsafe def is_eta_expansion_of (args : List expr) (univs : List level) (l : List (Name × expr)) :
    Bool :=
  l.all fun ⟨proj, val⟩ => val = (const proj univs).mk_app args
#align expr.is_eta_expansion_of expr.is_eta_expansion_of

/-- `is_eta_expansion_test l` checks whether there is a list of expresions `args` such that for all
  elements `(nm, pr)` in `l` we have `pr = nm args`. If so, returns the last element of `args`.
  Used in `is_eta_expansion`, where `l` consists of the projections and the fields of the value we
  want to eta-reduce. -/
unsafe def is_eta_expansion_test : List (Name × expr) → Option expr
  | [] => none
  | ⟨proj, val⟩ :: l =>
    match val.get_app_fn with
    | (const nm univs : expr) =>
      if nm = proj then
        let args := val.get_app_args
        let e := args.ilast
        if is_eta_expansion_of args univs l then some e else none
      else none
    | _ => none
#align expr.is_eta_expansion_test expr.is_eta_expansion_test

/-- `is_eta_expansion_aux val l` checks whether `val` can be eta-reduced to an expression `e`.
  Here `l` is intended to consists of the projections and the fields of `val`.
  This tactic calls `is_eta_expansion_test l`, but first removes all proofs from the list `l` and
  afterward checks whether the resulting expression `e` unifies with `val`.
  This last check is necessary, because `val` and `e` might have different types. -/
unsafe def is_eta_expansion_aux (val : expr) (l : List (Name × expr)) : tactic (Option expr) := do
  let l' ← l.mfilter fun ⟨proj, val⟩ => not <$> is_proof val
  match is_eta_expansion_test l' with
    | some e => (Option.map fun _ => e) <$> try_core (unify e val)
    | none => return none
#align expr.is_eta_expansion_aux expr.is_eta_expansion_aux

/-- `is_eta_expansion val` checks whether there is an expression `e` such that `val` is the
  eta-expansion of `e`.
  With eta-expansion we here mean the eta-expansion of a structure, not of a function.
  For example, the eta-expansion of `x : α × β` is `⟨x.1, x.2⟩`.
  This assumes that `val` is a fully-applied application of the constructor of a structure.

  This is useful to reduce expressions generated by the notation
    `{ field_1 := _, ..other_structure }`
  If `other_structure` is itself a field of the structure, then the elaborator will insert an
  eta-expanded version of `other_structure`. -/
unsafe def is_eta_expansion (val : expr) : tactic (Option expr) := do
  let e ← get_env
  let type ← infer_type val
  let projs ← e.structure_fields_full type.get_app_fn.const_name
  let args := val.get_app_args.drop type.get_app_args.length
  is_eta_expansion_aux val (projs args)
#align expr.is_eta_expansion expr.is_eta_expansion

end Expr

/-! ### Declarations about `declaration` -/


namespace Declaration

/-- `declaration.update_with_fun f test tgt decl`
sets the name of the given `decl : declaration` to `tgt`, and applies both `expr.eta_expand` and
`expr.apply_replacement_fun` to the value and type of `decl`.
-/
protected unsafe def update_with_fun (env : environment) (f : Name → Name) (test : expr → Bool)
    (relevant : name_map ℕ) (reorder : name_map <| List ℕ) (tgt : Name) (decl : declaration) :
    declaration :=
  let decl := decl.update_name <| tgt
  let decl :=
    decl.update_type <|
      (decl.type.eta_expand env reorder).apply_replacement_fun f test relevant reorder
  decl.update_value <|
    (decl.value.eta_expand env reorder).apply_replacement_fun f test relevant reorder
#align declaration.update_with_fun declaration.update_with_fun

/-- Checks whether the declaration is declared in the current file.
  This is a simple wrapper around `environment.in_current_file`
  Use `environment.in_current_file` instead if performance matters. -/
unsafe def in_current_file (d : declaration) : tactic Bool := do
  let e ← get_env
  return <| e d
#align declaration.in_current_file declaration.in_current_file

/-- Checks whether a declaration is a theorem -/
unsafe def is_theorem : declaration → Bool
  | thm _ _ _ _ => true
  | _ => false
#align declaration.is_theorem declaration.is_theorem

/-- Checks whether a declaration is a constant -/
unsafe def is_constant : declaration → Bool
  | cnst _ _ _ _ => true
  | _ => false
#align declaration.is_constant declaration.is_constant

/-- Checks whether a declaration is a axiom -/
unsafe def is_axiom : declaration → Bool
  | ax _ _ _ => true
  | _ => false
#align declaration.is_axiom declaration.is_axiom

/-- Checks whether a declaration is automatically generated in the environment.
  There is no cheap way to check whether a declaration in the namespace of a generalized
  inductive type is automatically generated, so for now we say that all of them are automatically
  generated. -/
unsafe def is_auto_generated (e : environment) (d : declaration) : Bool :=
  e.is_constructor d.to_name ∨
    (e.is_projection d.to_name).isSome ∨
      e.is_constructor d.to_name.getPrefix ∧
          d.to_name.last ∈ ["inj", "inj_eq", "sizeof_spec", "inj_arrow"] ∨
        e.is_inductive d.to_name.getPrefix ∧
            d.to_name.last ∈
              ["below", "binduction_on", "brec_on", "cases_on", "dcases_on", "drec_on", "drec",
                "rec", "rec_on", "no_confusion", "no_confusion_type", "sizeof", "ibelow",
                "has_sizeof_inst"] ∨
          d.to_name.hasPrefix fun nm => e.is_ginductive' nm
#align declaration.is_auto_generated declaration.is_auto_generated

/-- Returns true iff `d` is an automatically-generated or internal declaration.
-/
unsafe def is_auto_or_internal (env : environment) (d : declaration) : Bool :=
  d.to_name.is_internal || d.is_auto_generated env
#align declaration.is_auto_or_internal declaration.is_auto_or_internal

/-- Returns the list of universe levels of a declaration. -/
unsafe def univ_levels (d : declaration) : List level :=
  d.univ_params.map level.param
#align declaration.univ_levels declaration.univ_levels

/-- Returns the `reducibility_hints` field of a `defn`, and `reducibility_hints.opaque` otherwise -/
protected unsafe def reducibility_hints : declaration → ReducibilityHints
  | declaration.defn _ _ _ _ red _ => red
  | _ => ReducibilityHints.opaque
#align declaration.reducibility_hints declaration.reducibility_hints

/-- formats the arguments of a `declaration.thm` -/
private unsafe def print_thm (nm : Name) (tp : expr) (body : task expr) : tactic format := do
  let tp ← pp tp
  let body ← pp body.get
  return <| "<theorem " ++ to_fmt nm ++ " : " ++ tp ++ " := " ++ body ++ ">"
#align declaration.print_thm declaration.print_thm

/-- formats the arguments of a `declaration.defn` -/
private unsafe def print_defn (nm : Name) (tp : expr) (body : expr) (is_trusted : Bool) :
    tactic format := do
  let tp ← pp tp
  let body ← pp body
  return <|
      ("<" ++ if is_trusted then "def " else "meta def ") ++ to_fmt nm ++ " : " ++ tp ++ " := " ++
          body ++
        ">"
#align declaration.print_defn declaration.print_defn

/-- formats the arguments of a `declaration.cnst` -/
private unsafe def print_cnst (nm : Name) (tp : expr) (is_trusted : Bool) : tactic format := do
  let tp ← pp tp
  return <|
      ("<" ++ if is_trusted then "constant " else "meta constant ") ++ to_fmt nm ++ " : " ++ tp ++
        ">"
#align declaration.print_cnst declaration.print_cnst

/-- formats the arguments of a `declaration.ax` -/
private unsafe def print_ax (nm : Name) (tp : expr) : tactic format := do
  let tp ← pp tp
  return <| "<axiom " ++ to_fmt nm ++ " : " ++ tp ++ ">"
#align declaration.print_ax declaration.print_ax

/-- pretty-prints a `declaration` object. -/
unsafe def to_tactic_format : declaration → tactic format
  | declaration.thm nm _ tp bd => print_thm nm tp bd
  | declaration.defn nm _ tp bd _ is_trusted => print_defn nm tp bd is_trusted
  | declaration.cnst nm _ tp is_trusted => print_cnst nm tp is_trusted
  | declaration.ax nm _ tp => print_ax nm tp
#align declaration.to_tactic_format declaration.to_tactic_format

unsafe instance : has_to_tactic_format declaration :=
  ⟨to_tactic_format⟩

end Declaration

unsafe instance pexpr.decidable_eq {elab} : DecidableEq (expr elab) :=
  unchecked_cast expr.has_decidable_eq
#align pexpr.decidable_eq pexpr.decidable_eq

section

attribute [local semireducible] reflected

unsafe instance {α} [has_reflect α] : has_reflect (Thunk α)
  | a => expr.lam `x BinderInfo.default (reflect Unit) (reflect <| a ())

end

