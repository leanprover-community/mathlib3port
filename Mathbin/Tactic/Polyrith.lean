/-
Copyright (c) 2022 Dhruv Bhatia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Bhatia, Eric Wieser

! This file was ported from Lean 3 source module tactic.polyrith
! leanprover-community/mathlib commit 6afc9b06856ad973f6a2619e3e8a0a8d537a58f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.LinearCombination
import Mathbin.Data.Buffer.Parser.Numeral
import Mathbin.Data.Json

/-!

# polyrith Tactic

In this file, the `polyrith` tactic is created.  This tactic, which
works over `field`s, attempts to prove a multivariate polynomial target over said
field by using multivariable polynomial hypotheses/proof terms over the same field.
Used as is, the tactic makes use of those hypotheses in the local context that are
over the same field as the target. However, the user can also specifiy which hypotheses
from the local context to use, along with proof terms that might not already be in the
local context. Note: since this tactic uses SageMath via an API call done in Python,
it can only be used with a working internet connection, and with a local installation of Python.

## Implementation Notes

The tactic `linear_combination` is often used to prove such goals by allowing the user to
specify a coefficient for each hypothesis. If the target polynomial can be written as a
linear combination of the hypotheses with the chosen coefficients, then the `linear_combination`
tactic succeeds. In other words, `linear_combination` is a certificate checker, and it is left
to the user to find a collection of good coefficients. The `polyrith` tactic automates this
process using the theory of Groebner bases.

Polyrith does this by first parsing the relevant hypotheses into a form that Python can understand.
It then calls a Python file that uses the SageMath API to compute the coefficients. These
coefficients are then sent back to Lean, which parses them into pexprs. The information is then
given to the `linear_combination` tactic, which completes the process by checking the certificate.

`polyrith` calls an external python script `scripts/polyrith_sage.py`. Because this is not a Lean
file, changes to this script may not be noticed during Lean compilation if you have already
generated olean files. If you are modifying this python script, you likely know what you're doing;
remember to force recompilation of any files that call `polyrith`.

## TODO

* Give Sage more information about the specific ring being used for the coefficients. For now,
  we always use ℚ (or `QQ` in Sage).
* Handle `•` terms.
* Support local Sage installations.

## References

* See the book [*Ideals, Varieties, and Algorithms*][coxlittleOshea1997] by David Cox, John Little,
  and Donal O'Shea for the background theory on Groebner bases
* This code was heavily inspired by the code for the tactic `linarith`, which was written by
  Robert Lewis, who advised me on this project as part of a Computer Science independant study
  at Brown University.

-/


open Tactic Native

namespace Polyrith

/-! # Poly Datatype -/


/-- A datatype representing the semantics of multivariable polynomials.
Each `poly` can be converted into a string.
-/
inductive Poly
  | const : ℚ → poly
  | var : ℕ → poly
  | add : poly → poly → poly
  | sub : poly → poly → poly
  | mul : poly → poly → poly
  | pow : poly → ℕ → poly
  | neg : poly → poly
  deriving DecidableEq
#align polyrith.poly Polyrith.Poly

/-- This converts a poly object into a string representing it. The string
maintains the semantic structure of the poly object.

The output of this function must be valid Python syntax, and it assumes the variables `varN` from
`scripts/polyrith.py.`
-/
unsafe def poly.mk_string : Poly → String
  | poly.const z => toString z
  | poly.var n => "var" ++ toString n
  | poly.add p q => "(" ++ poly.mk_string p ++ " + " ++ poly.mk_string q ++ ")"
  | poly.sub p q => "(" ++ poly.mk_string p ++ " - " ++ poly.mk_string q ++ ")"
  | poly.mul p q => "(" ++ poly.mk_string p ++ " * " ++ poly.mk_string q ++ ")"
  | poly.pow p n => toString <| f!"({(poly.mk_string p)} ^ {n})"
  | poly.neg p => "-" ++ poly.mk_string p
#align polyrith.poly.mk_string polyrith.poly.mk_string

unsafe instance : Add Poly :=
  ⟨Poly.add⟩

unsafe instance : Sub Poly :=
  ⟨Poly.sub⟩

unsafe instance : Mul Poly :=
  ⟨Poly.mul⟩

unsafe instance : Pow Poly ℕ :=
  ⟨Poly.pow⟩

unsafe instance : Neg Poly :=
  ⟨Poly.neg⟩

unsafe instance : Repr Poly :=
  ⟨poly.mk_string⟩

unsafe instance : has_to_format Poly :=
  ⟨to_fmt ∘ poly.mk_string⟩

unsafe instance : Inhabited Poly :=
  ⟨Poly.const 0⟩

/-!
# Parsing algorithms

The following section contains code that can convert an `expr` of type `Prop` into a `poly` object
(provided that it is an equality)
-/


/-- `(vars, p) ← poly_form_of_atom red vars e` is the atomic case for `poly_form_of_expr`.
If `e` appears with index `k` in `vars`, it returns the singleton sum `p = poly.var k`.
Otherwise it updates `vars`, adding `e` with index `n`, and returns the singleton `p = poly.var n`.
-/
unsafe def poly_form_of_atom (red : Transparency) (vars : List expr) (e : expr) :
    tactic (List expr × poly) := do
  let index_of_e ←
    vars.mfoldlWithIndex
        (fun n last e' =>
          match last with
          | none => tactic.try_core <| tactic.is_def_eq e e' red >> return n
          | some k => return k)
        none
  return
      (match index_of_e with
      | some k => (vars, poly.var k)
      | none => (vars e, poly.var vars))
#align polyrith.poly_form_of_atom polyrith.poly_form_of_atom

-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      `poly_form_of_expr red map e` computes the polynomial form of `e`.
      
      `map` is a lookup map from atomic expressions to variable numbers.
      If a new atomic expression is encountered, it is added to the map with a new number.
      It matches atomic expressions up to reducibility given by `red`.
      
      Because it matches up to definitional equality, this function must be in the `tactic` monad,
      and forces some functions that call it into `tactic` as well.
      -/
    unsafe
  def
    poly_form_of_expr
    ( red : Transparency ) : List expr → expr → tactic ( List expr × poly )
    |
        m , q( $ ( e1 ) * $ ( e2 ) )
        =>
        do
          let ( m' , comp1 ) ← poly_form_of_expr m e1
            let ( m' , comp2 ) ← poly_form_of_expr m' e2
            return ( m' , comp1 * comp2 )
      |
        m , q( $ ( e1 ) + $ ( e2 ) )
        =>
        do
          let ( m' , comp1 ) ← poly_form_of_expr m e1
            let ( m' , comp2 ) ← poly_form_of_expr m' e2
            return ( m' , comp1 + comp2 )
      |
        m , q( $ ( e1 ) - $ ( e2 ) )
        =>
        do
          let ( m' , comp1 ) ← poly_form_of_expr m e1
            let ( m' , comp2 ) ← poly_form_of_expr m' e2
            return ( m' , comp1 - comp2 )
      | m , q( - $ ( e ) ) => do let ( m' , comp ) ← poly_form_of_expr m e return ( m' , - comp )
      |
        m , p @ q( @ Pow.pow _ ℕ _ $ ( e ) $ ( n ) )
        =>
        match
          n . toNat
          with
          | some k => do let ( m' , comp ) ← poly_form_of_expr m e return ( m' , comp ^ k )
            | none => poly_form_of_atom red m p
      |
        m , e
        =>
        match
          e . to_rat
          with
          | some z => return ⟨ m , Poly.const z ⟩ | none => poly_form_of_atom red m e
#align polyrith.poly_form_of_expr polyrith.poly_form_of_expr

/-!
# Un-Parsing algorithms

The following section contains code that can convert an a `poly` object into a `pexpr`.
-/


/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `n -/
-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      This can convert a `poly` into a `pexpr` that would evaluate to a polynomial.
      To do so, it uses a list `m` of expressions, the atomic expressions that appear in the `poly`.
      The index of an expression in this list corresponds to its `poly.var` argument: that is,
      if `e` is the `k`th element of `m`, then it is represented as `poly.var k`.
      
      `poly` objects only contain coefficients from `ℚ`. However, the `poly` object might
      be referring to a polynomial over some other field. As such, the resulting `pexpr` contains
      no typing information.
      -/
    unsafe
  def
    poly.to_pexpr
    : List expr → Poly → tactic pexpr
    | _ , poly.const z => return z . to_pexpr
      |
        m , poly.var n
        =>
        do
          let some e ← return <| m . nth n | throwError "unknown variable poly.var { ← n }"
            return ` `( $ ( e ) )
      |
        m , poly.add p q
        =>
        do
          let p_pexpr ← poly.to_pexpr m p
            let q_pexpr ← poly.to_pexpr m q
            return ` `( $ ( p_pexpr ) + $ ( q_pexpr ) )
      |
        m , poly.sub p q
        =>
        do
          let p_pexpr ← poly.to_pexpr m p
            let q_pexpr ← poly.to_pexpr m q
            if
              p_pexpr = ` `( 0 )
              then
              return ` `( - $ ( q_pexpr ) )
              else
              return ` `( $ ( p_pexpr ) - $ ( q_pexpr ) )
      |
        m , poly.mul p q
        =>
        do
          let p_pexpr ← poly.to_pexpr m p
            let q_pexpr ← poly.to_pexpr m q
            return ` `( $ ( p_pexpr ) * $ ( q_pexpr ) )
      |
        m , poly.pow p n
        =>
        do let p_pexpr ← poly.to_pexpr m p return ` `( $ ( p_pexpr ) ^ n $ ( n.to_pexpr ) )
      | m , poly.neg p => do let p_pexpr ← poly.to_pexpr m p return ` `( - $ ( p_pexpr ) )
#align polyrith.poly.to_pexpr polyrith.poly.to_pexpr

/-!
# Parsing SageMath output into a poly

The following section contains code that can convert a string of appropriate format into
a `poly` object. This is used later on to convert the coefficients given by Sage into
`poly` objects.
-/


open Parser

/-- A parser object that parses `string`s of the form `"poly.var n"`
to the appropriate `poly` object representing a variable.
Here, `n` is a natural number
-/
unsafe def var_parser : Parser Poly := do
  str "poly.var " >> poly.var <$> Parser.nat
#align polyrith.var_parser polyrith.var_parser

/-- A parser object that parses `string`s of the form `"poly.const r"`
to the appropriate `poly` object representing a rational coefficient.
Here, `r` is a rational number
-/
unsafe def const_fraction_parser : Parser Poly :=
  str "poly.const " >> poly.const <$> Parser.rat
#align polyrith.const_fraction_parser polyrith.const_fraction_parser

/-- A parser object that parses `string`s of the form `"poly.add p q"`
to the appropriate `poly` object representing the sum of two `poly`s.
Here, `p` and `q` are themselves string forms of `poly`s.
-/
unsafe def add_parser (cont : Parser Poly) : Parser Poly :=
  str "poly.add " >> poly.add <$> cont <*> (ch ' ' >> cont)
#align polyrith.add_parser polyrith.add_parser

/-- A parser object that parses `string`s of the form `"poly.sub p q"`
to the appropriate `poly` object representing the subtraction of two `poly`s.
Here, `p` and `q` are themselves string forms of `poly`s.
-/
unsafe def sub_parser (cont : Parser Poly) : Parser Poly :=
  str "poly.sub " >> poly.sub <$> cont <*> (ch ' ' >> cont)
#align polyrith.sub_parser polyrith.sub_parser

/-- A parser object that parses `string`s of the form `"poly.mul p q"`
to the appropriate `poly` object representing the product of two `poly`s.
Here, `p` and `q` are themselves string forms of `poly`s.
-/
unsafe def mul_parser (cont : Parser Poly) : Parser Poly :=
  str "poly.mul " >> poly.mul <$> cont <*> (ch ' ' >> cont)
#align polyrith.mul_parser polyrith.mul_parser

/-- A parser object that parses `string`s of the form `"poly.pow p n"`
to the appropriate `poly` object representing a `poly` raised to the
power of a natural number. Here, `p` is the string form of a `poly`
and `n` is a natural number.
-/
unsafe def pow_parser (cont : Parser Poly) : Parser Poly :=
  str "poly.pow " >> poly.pow <$> cont <*> (ch ' ' >> Nat)
#align polyrith.pow_parser polyrith.pow_parser

/-- A parser object that parses `string`s of the form `"poly.neg p"`
to the appropriate `poly` object representing the negation of a `poly`.
Here, `p` is the string form of a `poly`.
-/
unsafe def neg_parser (cont : Parser Poly) : Parser Poly :=
  str "poly.neg " >> poly.neg <$> cont
#align polyrith.neg_parser polyrith.neg_parser

/-- A parser for `poly` that uses an s-essresion style formats such as
`(poly.add (poly.var 0) (poly.const 1)`. -/
unsafe def poly_parser : Parser Poly :=
  ch '(' *>
      (var_parser <|>
        const_fraction_parser <|>
          add_parser poly_parser <|>
            sub_parser poly_parser <|>
              mul_parser poly_parser <|> pow_parser poly_parser <|> neg_parser poly_parser) <*
    ch ')'
#align polyrith.poly_parser polyrith.poly_parser

unsafe instance : non_null_json_serializable Poly
    where
  to_json p := json.null
  -- we don't actually need this, but the typeclass asks for it
  of_json j := do
    let s ← of_json String j
    match poly_parser s with
      | Sum.inl s =>
        exceptional.fail
          f! "unable to parse polynomial from.
            
            {s}"
      | Sum.inr p => pure p

/-- A schema for success messages from the python script -/
structure SageJsonSuccess where
  success : { b : Bool // b = tt }
  trace : Option String := none
  data : Option (List Poly) := none
  deriving non_null_json_serializable, Inhabited
#align polyrith.sage_json_success Polyrith.SageJsonSuccess

/-- A schema for failure messages from the python script -/
structure SageJsonFailure where
  success : { b : Bool // b = ff }
  errorName : String
  errorValue : String
  deriving non_null_json_serializable, Inhabited
#align polyrith.sage_json_failure Polyrith.SageJsonFailure

/-- Parse the json output from `scripts/polyrith.py` into either an error message, a list of `poly`
objects, or `none` if only trace output was requested. -/
unsafe def convert_sage_output (j : json) : tactic (Option (List Poly)) := do
  let r : Sum sage_json_success sage_json_failure ←
    decorate_ex "internal json error: "
        (-- try the error format first, so that if both fail we get the message from the success parser
            Sum.inr <$>
            of_json SageJsonFailure j <|>
          Sum.inl <$> of_json SageJsonSuccess j)
  match r with
    | Sum.inr f => throwError "polyrith failed to retrieve a solution from Sage! {(← f)}: {← f}"
    | Sum.inl s => do
      s trace
      pure s
#align polyrith.convert_sage_output polyrith.convert_sage_output

/-!
# Parsing context into poly

The following section contains code that collects hypotheses of the appropriate type
from the context (and from the list of hypotheses and proof terms specified by the user)
and converts them into `poly` objects.
-/


-- failed to format: unknown constant 'term.pseudo.antiquot'
/-- Convert an expression of the form `lhs = rhs` into the form `lhs - rhs` -/ unsafe
  def
    equality_to_left_side
    : expr → tactic expr
    | q( $ ( lhs ) = $ ( rhs ) ) => to_expr ` `( $ ( lhs ) - $ ( rhs ) )
      | e => fail "expression is not an equality"
#align polyrith.equality_to_left_side polyrith.equality_to_left_side

/-- `(vars, poly, typ) ← parse_target_to_poly` interprets the current target (an equality over
some field) into a `poly`. The result is a list of the atomic expressions in the target,
the `poly` itself, and an `expr` representing the type of the field. -/
unsafe def parse_target_to_poly : tactic (List expr × poly × expr) := do
  let e@q(@Eq $(R) _ _) ← target
  let left_side ← equality_to_left_side e
  let (m, p) ← poly_form_of_expr Transparency.reducible [] left_side
  return (m, p, R)
#align polyrith.parse_target_to_poly polyrith.parse_target_to_poly

/-- Filter `l` to the elements which are equalities of type `expt`. -/
unsafe def get_equalities_of_type (expt : expr) (l : List expr) : tactic (List expr) :=
  l.mfilter fun h_eq =>
    succeeds do
      let q(@Eq $(R) _ _) ← infer_type h_eq
      unify expt R
#align polyrith.get_equalities_of_type polyrith.get_equalities_of_type

/-- The purpose of this tactic is to collect all the hypotheses
and proof terms (specified by the user) that are equalities
of the same type as the target. It takes in an `expr` representing
the type, a list of expressions representing the atoms
(typically this starts as only containing
information about the target), a `bool` representing whether the
user used the key word "only", and a `list pexpr` of all the
hypotheses and proof terms selected by the user.

If the key word "only" is used, it collects together only those
hypotheses/proof terms selected by the user. If not, they are
combined with hypotheses from the local context. We throw out
those hypotheses that are not equalities of the given type,
and then modify each equality such that everything has been
moved to the left of the "=" sign.

The tactic returns the names of these hypotheses (as `expr`s),
a list of atoms updated with information from all these hypotheses,
and a list of these hypotheses converted into `poly` objects.
-/
unsafe def parse_ctx_to_polys (expt : expr) (m : List expr) (only_on : Bool) (hyps : List pexpr) :
    tactic (List expr × List expr × List Poly) := do
  let hyps ← hyps.mmap i_to_expr
  let hyps ← if only_on then return hyps else (· ++ hyps) <$> local_context
  let eq_names ← get_equalities_of_type expt hyps
  let eqs ← eq_names.mmap infer_type
  let eqs_to_left ← eqs.mmap equality_to_left_side
  let-- convert the expressions to polynomials, tracking the variables in `m`
    (m, poly_list)
    ←
    eqs_to_left.mfoldl
        (fun (s : _ × List Poly) new_exp => do
          let (m, poly_list) := s
          let (m', new_poly) ← poly_form_of_expr Transparency.reducible m new_exp
          return (m', poly_list ++ [new_poly]))
        (m, [])
  return (eq_names, m, poly_list)
#align polyrith.parse_ctx_to_polys polyrith.parse_ctx_to_polys

/-!
# Connecting with Python

The following section contains code that allows lean to communicate with a python script.
-/


/-- This tactic calls python from the command line with the args in `arg_list`.
The output printed to the console is returned as a `string`.
It assumes that `python3` is available on the path.
-/
unsafe def sage_output (arg_list : List String := []) : tactic json := do
  let path ← get_mathlib_dir
  let args := [path ++ "../scripts/polyrith_sage.py"] ++ arg_list
  let s ←
    unsafe_run_io <|
        Io.cmd
          { cmd := "python3"
            args }
  let some j ← pure (json.parse s) |
    throwError "Invalid json: {← s}"
  pure j
#align polyrith.sage_output polyrith.sage_output

/-- Adds parentheses around additions and subtractions, for printing at
precedence 65.
-/
unsafe def add_parens : expr → tactic format
  | e@q(_ + _) => f!"({← e})"
  | e@q(_ - _) => f!"({← e})"
  | e => f!"{← e}"
#align polyrith.add_parens polyrith.add_parens

/-- Given a pair of `expr`s, where one represents the hypothesis/proof term,
and the other representes the coefficient attached to it, this tactic
creates a string combining the two in the appropriate format for
`linear_combination`.

The boolean value returned is `tt` if the format needs to be negated
to accurately reflect the input expressions.
The negation is not applied in the format output by this function,
because it may appear as a negation (if this is the first component)
or a subtraction.
-/
unsafe def component_to_lc_format : expr × expr → tactic (Bool × format)
  | (ex, q(@One.one _ _)) => Prod.mk false <$> f!"{← ex}"
  | (ex, q(@One.one _ _ / $(cf))) => do
    let f ← add_parens cf
    Prod.mk ff <$> f!"{(← ex)} / {← f}"
  | (ex, q(-$(cf))) => do
    let (neg, fmt) ← component_to_lc_format (ex, cf)
    return (!neg, fmt)
  | (ex, cf) => do
    let f ← add_parens cf
    Prod.mk ff <$> f!"{(← f)} * {← ex}"
#align polyrith.component_to_lc_format polyrith.component_to_lc_format

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
private unsafe def intersperse_ops_aux : List (Bool × format) → format
  | [] => ""
  | (ff, fmt)::t => " +" ++ format.soft_break ++ fmt ++ intersperse_ops_aux t
  | (tt, fmt)::t => " -" ++ format.soft_break ++ fmt ++ intersperse_ops_aux t
#align polyrith.intersperse_ops_aux polyrith.intersperse_ops_aux

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Given a `list (bool × format)`, this function uses `+` and `-` to conjoin the
`format`s in the list. A `format` is negated if its corresponding `bool` is `tt`.
-/
unsafe def intersperse_ops : List (Bool × format) → format
  | [] => ""
  | (ff, fmt)::t => fmt ++ intersperse_ops_aux t
  | (tt, fmt)::t => "-" ++ fmt ++ intersperse_ops_aux t
#align polyrith.intersperse_ops polyrith.intersperse_ops

/-- This tactic repeats the process above for a `list` of pairs of `expr`s.-/
unsafe def components_to_lc_format (components : List (expr × expr)) : tactic format :=
  intersperse_ops <$> components.mmap component_to_lc_format
#align polyrith.components_to_lc_format polyrith.components_to_lc_format

/-!
# Connecting with Python

The following section contains code that allows lean to communicate with a python script.
-/


initialize
  registerTraceClass.1 `polyrith

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The first half of `tactic.polyrith` produces a list of arguments to be sent to Sage.
-/
unsafe def create_args (only_on : Bool) (hyps : List pexpr) :
    tactic (List expr × List expr × expr × List String) := do
  let (m, p, R) ← parse_target_to_poly
  let (eq_names, m, polys) ← parse_ctx_to_polys R m only_on hyps
  let args := [toString R, toString m.length, (polys.map poly.mk_string).toString, p.mk_string]
  return <| (eq_names, m, R, toString (is_trace_enabled_for `polyrith)::args)
#align polyrith.create_args polyrith.create_args

/-- The second half of `tactic.polyrith` processes the output from Sage into
a call to `linear_combination`.
-/
unsafe def process_output (eq_names : List expr) (m : List expr) (R : expr) (sage_out : json) :
    tactic format :=
  focus1 do
    let some coeffs_as_poly ← convert_sage_output sage_out |
      throwError"internal error: No output available"
    let coeffs_as_pexpr ← coeffs_as_poly.mmap (poly.to_pexpr m)
    let eq_names_pexpr := eq_names.map to_pexpr
    let coeffs_as_expr ← coeffs_as_pexpr.mmap fun e => to_expr ``(($(e) : $(R)))
    linear_combo.linear_combination eq_names_pexpr coeffs_as_pexpr
    let components :=
      (eq_names.zip coeffs_as_expr).filter fun pr => not <| pr.2.is_app_of `has_zero.zero
    let expr_string ← components_to_lc_format components
    let lc_fmt : format := "linear_combination " ++ format.nest 2 (format.group expr_string)
    done <|>
        throwError "polyrith found the following certificate, but it failed to close the goal:
          {← lc_fmt}"
    return <| "linear_combination " ++ format.nest 2 (format.group expr_string)
#align polyrith.process_output polyrith.process_output

/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
/-- Tactic for the special case when no hypotheses are available. -/
unsafe def no_hypotheses_case : tactic (Option format) :=
  (do
      sorry
      return <| some "ring") <|>
    fail "polyrith did not find any relevant hypotheses and the goal is not provable by ring"
#align polyrith.no_hypotheses_case polyrith.no_hypotheses_case

/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
/-- Tactic for the special case when there are no variables. -/
unsafe def no_variables_case : tactic (Option format) :=
  (do
      sorry
      return <| some "ring") <|>
    fail "polyrith did not find any variables and the goal is not provable by ring"
#align polyrith.no_variables_case polyrith.no_variables_case

/-- This is the main body of the `polyrith` tactic. It takes in the following inputs:
* `(only_on : bool)` - This represents whether the user used the key word "only"
* `(hyps : list pexpr)` - the hypotheses/proof terms selecteed by the user

First, the tactic converts the target into a `poly`, and finds out what type it
is an equality of. (It also fills up a list of `expr`s with its atoms). Then, it
collects all the relevant hypotheses/proof terms from the context, and from those
selected by the user, taking into account whether `only_on` is true. (The list of atoms is
updated accordingly as well).

This information is used to create a list of args that get used in a call to
the appropriate python file that executes a grobner basis computation. The
output of this computation is a `string` representing the certificate. This
string is parsed into a list of `poly` objects that are then converted into
`pexpr`s (using the updated list of atoms).

the names of the hypotheses, along with the corresponding coefficients are
given to `linear_combination`. If that tactic succeeds, the user is prompted
to replace the call to `polyrith` with the appropriate call to
`linear_combination`.

This returns `none` if this was a "dry run" attempt that does not actually invoke sage.
-/
unsafe def _root_.tactic.polyrith (only_on : Bool) (hyps : List pexpr) : tactic (Option format) :=
  do
  sleep 10
  let-- otherwise can lead to weird errors when actively editing code with polyrith calls
    (eq_names, m, R, args)
    ← create_args only_on hyps
  if eq_names = 0 then no_hypotheses_case
    else
      if m = 0 then no_variables_case
      else do
        let sage_out ← sage_output args
        if is_trace_enabled_for `polyrith then do
            convert_sage_output sage_out
            return none
          else some <$> process_output eq_names m R sage_out
#align tactic.polyrith tactic.polyrith

/-! # Interactivity -/


/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:38:34: unsupported: setup_tactic_parser -/
/-- Attempts to prove polynomial equality goals through polynomial arithmetic
on the hypotheses (and additional proof terms if the user specifies them).
It proves the goal by generating an appropriate call to the tactic
`linear_combination`. If this call succeeds, the call to `linear_combination`
is suggested to the user.

* `polyrith` will use all relevant hypotheses in the local context.
* `polyrith [t1, t2, t3]` will add proof terms t1, t2, t3 to the local context.
* `polyrith only [h1, h2, h3, t1, t2, t3]` will use only local hypotheses
  `h1`, `h2`, `h3`, and proofs `t1`, `t2`, `t3`. It will ignore the rest of the local context.

Notes:
* This tactic only works with a working internet connection, since it calls Sage
  using the SageCell web API at <https://sagecell.sagemath.org/>.
  Many thanks to the Sage team and organization for allowing this use.
* This tactic assumes that the user has `python3` installed and available on the path.
  (Test by opening a terminal and executing `python3 --version`.)
  It also assumes that the `requests` library is installed: `python3 -m pip install requests`.

Examples:

```lean
example (x y : ℚ) (h1 : x*y + 2*x = 1) (h2 : x = y) :
  x*y = -2*y + 1 :=
by polyrith
-- Try this: linear_combination h1 - 2 * h2

example (x y z w : ℚ) (hzw : z = w) : x*z + 2*y*z = x*w + 2*y*w :=
by polyrith
-- Try this: linear_combination (2 * y + x) * hzw

constant scary : ∀ a b : ℚ, a + b = 0

example (a b c d : ℚ) (h : a + b = 0) (h2: b + c = 0) : a + b + c + d = 0 :=
by polyrith only [scary c d, h]
-- Try this: linear_combination scary c d + h
```
-/
unsafe def _root_.tactic.interactive.polyrith (restr : parse (tk "only")?)
    (hyps : parse pexpr_list ?) : tactic Unit := do
  let some f ← tactic.polyrith restr.isSome (hyps.getOrElse []) |
    skip
  ← do
      dbg_trace "Try this: {← f}"
#align tactic.interactive.polyrith tactic.interactive.polyrith

add_tactic_doc
  { Name := "polyrith"
    category := DocCategory.tactic
    declNames := [`tactic.interactive.polyrith]
    tags := ["arithmetic", "finishing", "decision procedure"] }

end Polyrith

