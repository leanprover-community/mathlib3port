/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
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

/-- `guess_degree e` assumes that `e` is an expression in a polynomial ring, and makes an attempt
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
unsafe def guess_degree : expr → tactic expr
  | quote.1 Zero.zero => pure (quote.1 0)
  | quote.1 One.one => pure (quote.1 0)
  | quote.1 (-%%ₓf) => guess_degree f
  | app (quote.1 ⇑C) x => pure (quote.1 0)
  | quote.1 x => pure (quote.1 1)
  | quote.1 (bit0 (%%ₓa)) => guess_degree a
  | quote.1 (bit1 (%%ₓa)) => guess_degree a
  | quote.1 ((%%ₓa) + %%ₓb) => do
    let [da, db] ← [a, b].mmap guess_degree
    pure <| expr.mk_app (quote.1 (max : ℕ → ℕ → ℕ)) [da, db]
  | quote.1 ((%%ₓa) - %%ₓb) => do
    let [da, db] ← [a, b].mmap guess_degree
    pure <| expr.mk_app (quote.1 (max : ℕ → ℕ → ℕ)) [da, db]
  | quote.1 ((%%ₓa) * %%ₓb) => do
    let [da, db] ← [a, b].mmap guess_degree
    pure <| expr.mk_app (quote.1 ((· + ·) : ℕ → ℕ → ℕ)) [da, db]
  | quote.1 ((%%ₓa) ^ %%ₓb) => do
    let da ← guess_degree a
    pure <| expr.mk_app (quote.1 ((· * ·) : ℕ → ℕ → ℕ)) [da, b]
  | app (quote.1 ⇑(monomial (%%ₓn))) x => pure n
  | e => do
    let quote.1 (@Polynomial (%%ₓR) (%%ₓinst)) ← infer_type e
    let pe ← to_expr (pquote.1 (@natDegree (%%ₓR) (%%ₓinst))) true false
    pure <| expr.mk_app pe [e]

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:66:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Expr.lean:389:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:66:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Expr.lean:389:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
/-- `resolve_sum_step e` takes the type of the current goal `e` as input.
It tries to make progress on the goal `e` by reducing it to subgoals.
It assumes that `e` is of the form `f.nat_degree ≤ d`, failing otherwise.

`resolve_sum_step` progresses into `f` if `f` is
* a sum, difference, opposite, product, or a power;
* a monomial;
* `C a`;
* `0, 1` or `bit0 a, bit1 a` (to deal with numerals).

The side-goals produced by `resolve_sum_step` are either again of the same shape `f'.nat_degree ≤ d`
or of the form `m ≤ n`, where `m n : ℕ`.

If `d` is less than `guess_degree f`, this tactic will create unsolvable goals.
-/
unsafe def resolve_sum_step : expr → tactic Unit
  | quote.1 (natDegree (%%ₓtl) ≤ %%ₓtr) =>
    match tl with
    | quote.1 ((%%ₓtl1) + %%ₓtl2) => refine (pquote.1 ((nat_degree_add_le_iff_left _ _ _).mpr _))
    | quote.1 ((%%ₓtl1) - %%ₓtl2) => refine (pquote.1 ((nat_degree_sub_le_iff_left _).mpr _))
    | quote.1 ((%%ₓtl1) * %%ₓtl2) => do
      let [d1, d2] ← [tl1, tl2].mmap guess_degree
      refine (pquote.1 (nat_degree_mul_le.trans <| (add_le_add _ _).trans (_ : ((%%ₓd1) + %%ₓd2) ≤ %%ₓtr)))
    | quote.1 (-%%ₓf) => refine (pquote.1 ((nat_degree_neg _).le.trans _))
    | quote.1 (X ^ %%ₓn) => refine (pquote.1 ((nat_degree_X_pow_le (%%ₓn)).trans _))
    | app (quote.1 ⇑(@monomial (%%ₓR) (%%ₓinst) (%%ₓn))) x =>
      refine (pquote.1 ((nat_degree_monomial_le (%%ₓx)).trans _))
    | app (quote.1 ⇑C) x => refine (pquote.1 ((nat_degree_C (%%ₓx)).le.trans (Nat.zero_leₓ (%%ₓtr))))
    | quote.1 x => refine (pquote.1 (nat_degree_X_le.trans _))
    | quote.1 Zero.zero => refine (pquote.1 (nat_degree_zero.le.trans (Nat.zero_leₓ _)))
    | quote.1 One.one => refine (pquote.1 (nat_degree_one.le.trans (Nat.zero_leₓ _)))
    | quote.1 (bit0 (%%ₓa)) => refine (pquote.1 ((nat_degree_bit0 (%%ₓa)).trans _))
    | quote.1 (bit1 (%%ₓa)) => refine (pquote.1 ((nat_degree_bit1 (%%ₓa)).trans _))
    | quote.1 ((%%ₓtl1) ^ %%ₓn) => do
      refine (pquote.1 (nat_degree_pow_le.trans _))
      refine
          (pquote.1
            (dite ((%%ₓn) = 0)
              (fun n0 : (%%ₓn) = 0 => by
                simp only [n0, zero_mul, zero_le])
              _))
      let n0 ← get_unused_name "n0" >>= intro
      refine (pquote.1 ((mul_comm _ _).le.trans ((Nat.le_div_iff_mul_le' (Nat.pos_of_ne_zeroₓ (%%ₓn0))).mp _)))
      let lem1 ← to_expr (pquote.1 (Nat.mul_div_cancelₓ _ (Nat.pos_of_ne_zeroₓ (%%ₓn0)))) true false
      let lem2 ← to_expr (pquote.1 (Nat.div_selfₓ (Nat.pos_of_ne_zeroₓ (%%ₓn0)))) true false
      focus1 (refine (pquote.1 ((%%ₓn0) rfl).elim) <|> rewrite_target lem1 <|> rewrite_target lem2) <|> skip
    | e =>
      "./././Mathport/Syntax/Translate/Expr.lean:389:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"
  | e =>
    "./././Mathport/Syntax/Translate/Expr.lean:389:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"

-- ./././Mathport/Syntax/Translate/Expr.lean:332:4: warning: unsupported (TODO): `[tacs]
/-- `norm_assum` simply tries `norm_num` and `assumption`.
It is used to try to discharge as many as possible of the side-goals of `compute_degree_le`.
Several side-goals are of the form `m ≤ n`, for natural numbers `m, n` or of the form `c ≠ 0`,
with `c` a coefficient of the polynomial `f` in question. -/
unsafe def norm_assum : tactic Unit :=
  try sorry >> try assumption

/-- `eval_guessing n e` takes a natural number `n` and an expression `e` and gives an
estimate for the evaluation of `eval_expr' ℕ e`.  It is tailor made for estimating degrees of
polynomials.

It decomposes `e` recursively as a sequence of additions, multiplications and `max`.
On the atoms of the process, `eval_guessing` tries to use `eval_expr' ℕ`, resorting to using
`n` if `eval_expr' ℕ` fails.

For use with degree of polynomials, we mostly use `n = 0`. -/
unsafe def eval_guessing (n : ℕ) : expr → tactic ℕ
  | quote.1 ((%%ₓa) + %%ₓb) => (· + ·) <$> eval_guessing a <*> eval_guessing b
  | quote.1 ((%%ₓa) * %%ₓb) => (· * ·) <$> eval_guessing a <*> eval_guessing b
  | quote.1 (max (%%ₓa) (%%ₓb)) => max <$> eval_guessing a <*> eval_guessing b
  | e => eval_expr' ℕ e <|> pure n

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
unsafe def compute_degree_le : tactic Unit := do
  let t ← target
  try <| refine (pquote.1 (degree_le_nat_degree.trans (WithBot.coe_le_coe.mpr _)))
  let quote.1 (natDegree (%%ₓtl) ≤ %%ₓtr) ← target |
    fail "Goal is not of the form\n`f.nat_degree ≤ d` or `f.degree ≤ d`"
  let expected_deg ← guess_degree tl >>= eval_guessing 0
  let deg_bound ← eval_expr' ℕ tr <|> pure expected_deg
  if deg_bound < expected_deg then
      fail
        s! "the given polynomial has a term of expected degree
          at least '{expected_deg}'"
    else repeat <| target >>= resolve_sum_step
  (do
        let gs ← get_goals >>= List.mmapₓ infer_type
        success_if_fail <| gs <| unify t) <|>
      fail "Goal did not change"
  try <| any_goals' norm_assum

add_tactic_doc
  { Name := "compute_degree_le", category := DocCategory.tactic, declNames := [`tactic.interactive.compute_degree_le],
    tags := ["arithmetic", "finishing"] }

end Interactive

end Tactic

