/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa

! This file was ported from Lean 3 source module tactic.compute_degree
! leanprover-community/mathlib commit b363547b3113d350d053abdf2884e9850a56b205
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Polynomial.Degree.Lemmas

/-! # `compute_degree_le` a tactic for computing degrees of polynomials

This file defines the tactic `compute_degree_le`.

Using `compute_degree_le` when the goal is of the form `f.nat_degree ≤ d`, tries to solve the goal.
It may leave side-goals, in case it is not entirely successful.

See the doc-string for more details.

##  Future work

* Deal with goals of the form `f.(nat_)degree = d` (PR #14040 does exactly this).
* Add better functionality to deal with exponents that are not necessarily closed natural numbers.
* Add support for proving goals of the from `f.(nat_)degree ≠ 0`.
* Make sure that `degree` and `nat_degree` are equally supported.

##  Implementation details

We start with a goal of the form `f.(nat_)degree ≤ d`.  Recurse into `f` breaking apart sums,
products and powers.  Take care of numerals, `C a, X (^ n), monomial a n` separately. -/


namespace Tactic

namespace ComputeDegree

open Expr Polynomial

-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      `guess_degree e` assumes that `e` is an expression in a polynomial ring, and makes an attempt
      at guessing the `nat_degree` of `e`.  Heuristics for `guess_degree`:
      * `0, 1, C a`,      guess `0`,
      * `polynomial.X`,   guess `1`,
      *  `bit0/1 f, -f`,  guess `guess_degree f`,
      * `f + g, f - g`,   guess `max (guess_degree f) (guess_degree g)`,
      * `f * g`,          guess `guess_degree f + guess_degree g`,
      * `f ^ n`,          guess `guess_degree f * n`,
      * `monomial n r`,   guess `n`,
      * `f` not as above, guess `f.nat_degree`.
      
      The guessed degree should coincide with the behaviour of `resolve_sum_step`:
      `resolve_sum_step` cannot solve a goal `f.nat_degree ≤ d` if `guess_degree f < d`.
       -/
    unsafe
  def
    guess_degree
    : expr → tactic expr
    | q( Zero.zero ) => pure q( 0 )
      | q( One.one ) => pure q( 0 )
      | q( - $ ( f ) ) => guess_degree f
      | app q( ⇑ c ) x => pure q( 0 )
      | q( x ) => pure q( 1 )
      | q( bit0 $ ( a ) ) => guess_degree a
      | q( bit1 $ ( a ) ) => guess_degree a
      |
        q( $ ( a ) + $ ( b ) )
        =>
        do
          let [ da , db ] ← [ a , b ] . mapM guess_degree
            pure <| expr.mk_app q( ( max : ℕ → ℕ → ℕ ) ) [ da , db ]
      |
        q( $ ( a ) - $ ( b ) )
        =>
        do
          let [ da , db ] ← [ a , b ] . mapM guess_degree
            pure <| expr.mk_app q( ( max : ℕ → ℕ → ℕ ) ) [ da , db ]
      |
        q( $ ( a ) * $ ( b ) )
        =>
        do
          let [ da , db ] ← [ a , b ] . mapM guess_degree
            pure <| expr.mk_app q( ( ( · + · ) : ℕ → ℕ → ℕ ) ) [ da , db ]
      |
        q( $ ( a ) ^ $ ( b ) )
        =>
        do let da ← guess_degree a pure <| expr.mk_app q( ( ( · * · ) : ℕ → ℕ → ℕ ) ) [ da , b ]
      | app q( ⇑ ( monomial $ ( n ) ) ) x => pure n
      |
        e
        =>
        do
          let q( @ Polynomial $ ( R ) $ ( inst ) ) ← infer_type e
            let pe ← to_expr ` `( @ natDegree $ ( R ) $ ( inst ) ) true false
            pure <| expr.mk_app pe [ e ]
#align tactic.compute_degree.guess_degree tactic.compute_degree.guess_degree

-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      `resolve_sum_step` assumes that the current goal is of the form `f.nat_degree ≤ d`, failing
      otherwise.  It tries to make progress on the goal by progressing into `f` if `f` is
      * a sum, difference, opposite, product, or a power;
      * a monomial;
      * `C a`;
      * `0, 1` or `bit0 a, bit1 a` (to deal with numerals).
      
      The side-goals produced by `resolve_sum_step` are either again of the same shape `f'.nat_degree ≤ d`
      or of the form `m ≤ n`, where `m n : ℕ`.
      
      If `d` is less than `guess_degree f`, this tactic will create unsolvable goals.
      -/
    unsafe
  def
    resolve_sum_step
    : tactic Unit
    :=
      do
        let t ← target >>= instantiate_mvars
          let
            q( natDegree $ ( tl ) ≤ $ ( tr ) )
              ←
              whnf t reducible
              | throwError "Goal is not of the form `f.nat_degree ≤ d`"
          match
            tl
            with
            |
                q( $ ( tl1 ) + $ ( tl2 ) )
                =>
                refine ` `( ( natDegree_add_le_iff_left _ _ _ ) . mpr _ )
              | q( $ ( tl1 ) - $ ( tl2 ) ) => refine ` `( ( natDegree_sub_le_iff_left _ ) . mpr _ )
              |
                q( $ ( tl1 ) * $ ( tl2 ) )
                =>
                do
                  let [ d1 , d2 ] ← [ tl1 , tl2 ] . mapM guess_degree
                    refine
                      `
                        `(
                          natDegree_mul_le . trans
                            <|
                            ( add_le_add _ _ ) . trans ( _ : $ ( d1 ) + $ ( d2 ) ≤ $ ( tr ) )
                          )
              | q( - $ ( f ) ) => refine ` `( ( natDegree_neg _ ) . le . trans _ )
              | q( x ^ $ ( n ) ) => refine ` `( ( natDegree_x_pow_le $ ( n ) ) . trans _ )
              |
                app q( ⇑ ( @ monomial $ ( R ) $ ( inst ) $ ( n ) ) ) x
                =>
                refine ` `( ( natDegree_monomial_le $ ( x ) ) . trans _ )
              |
                app q( ⇑ c ) x
                =>
                refine ` `( ( natDegree_c $ ( x ) ) . le . trans ( Nat.zero_le $ ( tr ) ) )
              | q( x ) => refine ` `( natDegree_x_le . trans _ )
              | q( Zero.zero ) => refine ` `( natDegree_zero . le . trans ( Nat.zero_le _ ) )
              | q( One.one ) => refine ` `( natDegree_one . le . trans ( Nat.zero_le _ ) )
              | q( bit0 $ ( a ) ) => refine ` `( ( natDegree_bit0 $ ( a ) ) . trans _ )
              | q( bit1 $ ( a ) ) => refine ` `( ( natDegree_bit1 $ ( a ) ) . trans _ )
              |
                q( $ ( tl1 ) ^ $ ( n ) )
                =>
                do
                  refine ` `( natDegree_pow_le . trans _ )
                    refine
                      `
                        `(
                          dite
                            ( $ ( n ) = 0 )
                              ( fun n0 : $ ( n ) = 0 => by simp only [ n0 , zero_mul , zero_le ] )
                              _
                          )
                    let n0 ← get_unused_name "n0" >>= intro
                    refine
                      `
                        `(
                          ( mul_comm _ _ ) . le . trans
                            ( ( Nat.le_div_iff_mul_le' ( Nat.pos_of_ne_zero $ ( n0 ) ) ) . mp _ )
                          )
                    let
                      lem1
                        ←
                        to_expr ` `( Nat.mul_div_cancel _ ( Nat.pos_of_ne_zero $ ( n0 ) ) ) tt ff
                    let lem2 ← to_expr ` `( Nat.div_self ( Nat.pos_of_ne_zero $ ( n0 ) ) ) tt ff
                    focus1
                        (
                          refine ` `( ( $ ( n0 ) rfl ) . elim )
                            <|>
                            rewrite_target lem1 <|> rewrite_target lem2
                          )
                      <|>
                      skip
              | e => throwError "'{ ← e }' is not supported"
#align tactic.compute_degree.resolve_sum_step tactic.compute_degree.resolve_sum_step

/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
/-- `norm_assum` simply tries `norm_num` and `assumption`.
It is used to try to discharge as many as possible of the side-goals of `compute_degree_le`.
Several side-goals are of the form `m ≤ n`, for natural numbers `m, n` or of the form `c ≠ 0`,
with `c` a coefficient of the polynomial `f` in question. -/
unsafe def norm_assum : tactic Unit :=
  try sorry >> try assumption
#align tactic.compute_degree.norm_assum tactic.compute_degree.norm_assum

-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      `eval_guessing n e` takes a natural number `n` and an expression `e` and gives an
      estimate for the evaluation of `eval_expr' ℕ e`.  It is tailor made for estimating degrees of
      polynomials.
      
      It decomposes `e` recursively as a sequence of additions, multiplications and `max`.
      On the atoms of the process, `eval_guessing` tries to use `eval_expr' ℕ`, resorting to using
      `n` if `eval_expr' ℕ` fails.
      
      For use with degree of polynomials, we mostly use `n = 0`. -/
    unsafe
  def
    eval_guessing
    ( n : ℕ ) : expr → tactic ℕ
    | q( $ ( a ) + $ ( b ) ) => ( · + · ) <$> eval_guessing a <*> eval_guessing b
      | q( $ ( a ) * $ ( b ) ) => ( · * · ) <$> eval_guessing a <*> eval_guessing b
      | q( max $ ( a ) $ ( b ) ) => max <$> eval_guessing a <*> eval_guessing b
      | e => eval_expr' ℕ e <|> pure n
#align tactic.compute_degree.eval_guessing tactic.compute_degree.eval_guessing

/-- A general description of `compute_degree_le_aux` is in the doc-string of `compute_degree`.
The difference between the two is that `compute_degree_le_aux` makes no effort to close side-goals,
nor fails if the goal does not change. -/
unsafe def compute_degree_le_aux : tactic Unit := do
  try <| refine ``(degree_le_natDegree.trans (WithBot.coe_le_coe.mpr _))
  let q(natDegree $(tl) ≤ $(tr)) ← target |
    fail "Goal is not of the form\n`f.nat_degree ≤ d` or `f.degree ≤ d`"
  let expected_deg ← guess_degree tl >>= eval_guessing 0
  let deg_bound ← eval_expr' ℕ tr <|> pure expected_deg
  if deg_bound < expected_deg then
      fail
        s! "the given polynomial has a term of expected degree
          at least '{expected_deg}'"
    else repeat <| resolve_sum_step
#align tactic.compute_degree.compute_degree_le_aux tactic.compute_degree.compute_degree_le_aux

end ComputeDegree

namespace Interactive

open ComputeDegree Polynomial

/-- `compute_degree_le` tries to solve a goal of the form `f.nat_degree ≤ d` or `f.degree ≤ d`,
where `f : R[X]` and `d : ℕ` or `d : with_bot ℕ`.

If the given degree `d` is smaller than the one that the tactic computes,
then the tactic suggests the degree that it computed.

Examples:

```lean
open polynomial
open_locale polynomial

variables {R : Type*} [semiring R] {a b c d e : R}

example {F} [ring F] {a : F} {n : ℕ} (h : n ≤ 10) :
  nat_degree (X ^ n + C a * X ^ 10 : F[X]) ≤ 10 :=
by compute_degree_le

example : nat_degree (7 * X : R[X]) ≤ 1 :=
by compute_degree_le

example {p : R[X]} {n : ℕ} {p0 : p.nat_degree = 0} :
 (p ^ n).nat_degree ≤ 0 :=
by compute_degree_le
```
-/
unsafe def compute_degree_le : tactic Unit :=
  focus1 do
    check_target_changes compute_degree_le_aux
    try <| any_goals' norm_assum
#align tactic.interactive.compute_degree_le tactic.interactive.compute_degree_le

add_tactic_doc
  { Name := "compute_degree_le"
    category := DocCategory.tactic
    declNames := [`tactic.interactive.compute_degree_le]
    tags := ["arithmetic", "finishing"] }

end Interactive

end Tactic

