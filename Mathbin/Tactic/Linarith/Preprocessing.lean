/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis

! This file was ported from Lean 3 source module tactic.linarith.preprocessing
! leanprover-community/mathlib commit a437a2499163d85d670479f69f625f461cc5fef9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Prod.Lex
import Mathbin.Tactic.CancelDenoms
import Mathbin.Tactic.Linarith.Datatypes
import Mathbin.Tactic.Zify

/-!
# Linarith preprocessing

This file contains methods used to preprocess inputs to `linarith`.

In particular, `linarith` works over comparisons of the form `t R 0`, where `R ∈ {<,≤,=}`.
It assumes that expressions in `t` have integer coefficients and that the type of `t` has
well-behaved subtraction.

## Implementation details

A `global_preprocessor` is a function `list expr → tactic(list expr)`. Users can add custom
preprocessing steps by adding them to the `linarith_config` object. `linarith.default_preprocessors`
is the main list, and generally none of these should be skipped unless you know what you're doing.
-/


open Native Tactic Expr

namespace Linarith

/-! ### Preprocessing -/


open Tactic

/- ./././Mathport/Syntax/Translate/Basic.lean:334:40: warning: unsupported option eqn_compiler.max_steps -/
set_option eqn_compiler.max_steps 50000

/-- If `prf` is a proof of `¬ e`, where `e` is a comparison,
`rem_neg prf e` flips the comparison in `e` and returns a proof.
For example, if `prf : ¬ a < b`, ``rem_neg prf `(a < b)`` returns a proof of `a ≥ b`.
-/
unsafe def rem_neg (prf : expr) : expr → tactic expr
  | q(_ ≤ _) => mk_app `` lt_of_not_ge [prf]
  | q(_ < _) => mk_app `` le_of_not_gt [prf]
  | q(_ > _) => mk_app `` le_of_not_gt [prf]
  | q(_ ≥ _) => mk_app `` lt_of_not_ge [prf]
  | e => failed
#align linarith.rem_neg linarith.rem_neg

-- failed to format: unknown constant 'term.pseudo.antiquot'
private unsafe
  def
    rearr_comp_aux
    : expr → expr → tactic expr
    | prf , q( $ ( a ) ≤ 0 ) => return prf
      | prf , q( $ ( a ) < 0 ) => return prf
      | prf , q( $ ( a ) = 0 ) => return prf
      | prf , q( $ ( a ) ≥ 0 ) => mk_app ` ` neg_nonpos_of_nonneg [ prf ]
      | prf , q( $ ( a ) > 0 ) => mk_app `neg_neg_of_pos [ prf ]
      | prf , q( 0 ≥ $ ( a ) ) => to_expr ` `( idRhs ( $ ( a ) ≤ 0 ) $ ( prf ) )
      | prf , q( 0 > $ ( a ) ) => to_expr ` `( idRhs ( $ ( a ) < 0 ) $ ( prf ) )
      | prf , q( 0 = $ ( a ) ) => mk_app `eq.symm [ prf ]
      | prf , q( 0 ≤ $ ( a ) ) => mk_app ` ` neg_nonpos_of_nonneg [ prf ]
      | prf , q( 0 < $ ( a ) ) => mk_app `neg_neg_of_pos [ prf ]
      | prf , q( $ ( a ) ≤ $ ( b ) ) => mk_app ` ` sub_nonpos_of_le [ prf ]
      | prf , q( $ ( a ) < $ ( b ) ) => mk_app `sub_neg_of_lt [ prf ]
      | prf , q( $ ( a ) = $ ( b ) ) => mk_app `sub_eq_zero_of_eq [ prf ]
      | prf , q( $ ( a ) > $ ( b ) ) => mk_app `sub_neg_of_lt [ prf ]
      | prf , q( $ ( a ) ≥ $ ( b ) ) => mk_app ` ` sub_nonpos_of_le [ prf ]
      |
        prf , q( ¬ $ ( t ) )
        =>
        do let nprf ← rem_neg prf t let tp ← infer_type nprf rearr_comp_aux nprf tp
      | prf , a => trace a >> fail "couldn't rearrange comp"
#align linarith.rearr_comp_aux linarith.rearr_comp_aux

/-- `rearr_comp e` takes a proof `e` of an equality, inequality, or negation thereof,
and turns it into a proof of a comparison `_ R 0`, where `R ∈ {=, ≤, <}`.
 -/
unsafe def rearr_comp (e : expr) : tactic expr :=
  infer_type e >>= rearr_comp_aux e
#align linarith.rearr_comp linarith.rearr_comp

/-- If `e` is of the form `((n : ℕ) : ℤ)`, `is_nat_int_coe e` returns `n : ℕ`. -/
unsafe def is_nat_int_coe : expr → Option expr
  | q(@coe ℕ ℤ $(_) $(n)) => some n
  | _ => none
#align linarith.is_nat_int_coe linarith.is_nat_int_coe

/-- If `e : ℕ`, returns a proof of `0 ≤ (e : ℤ)`. -/
unsafe def mk_coe_nat_nonneg_prf (e : expr) : tactic expr :=
  mk_app `int.coe_nat_nonneg [e]
#align linarith.mk_coe_nat_nonneg_prf linarith.mk_coe_nat_nonneg_prf

-- failed to format: unknown constant 'term.pseudo.antiquot'
/-- `get_nat_comps e` returns a list of all subexpressions of `e` of the form `((t : ℕ) : ℤ)`. -/
    unsafe
  def
    get_nat_comps
    : expr → List expr
    | q( $ ( a ) + $ ( b ) ) => ( get_nat_comps a ) . append ( get_nat_comps b )
      | q( $ ( a ) * $ ( b ) ) => ( get_nat_comps a ) . append ( get_nat_comps b )
      | e => match is_nat_int_coe e with | some e' => [ e' ] | none => [ ]
#align linarith.get_nat_comps linarith.get_nat_comps

-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      If `pf` is a proof of a strict inequality `(a : ℤ) < b`,
      `mk_non_strict_int_pf_of_strict_int_pf pf` returns a proof of `a + 1 ≤ b`,
      and similarly if `pf` proves a negated weak inequality.
      -/
    unsafe
  def
    mk_non_strict_int_pf_of_strict_int_pf
    ( pf : expr ) : tactic expr
    :=
      do
        let tp ← infer_type pf
          match
            tp
            with
            | q( $ ( a ) < $ ( b ) ) => to_expr ` `( Int.add_one_le_iff . mpr $ ( pf ) )
              | q( $ ( a ) > $ ( b ) ) => to_expr ` `( Int.add_one_le_iff . mpr $ ( pf ) )
              |
                q( ¬ $ ( a ) ≤ $ ( b ) )
                =>
                to_expr ` `( Int.add_one_le_iff . mpr ( le_of_not_gt $ ( pf ) ) )
              |
                q( ¬ $ ( a ) ≥ $ ( b ) )
                =>
                to_expr ` `( Int.add_one_le_iff . mpr ( le_of_not_gt $ ( pf ) ) )
              | _ => fail "mk_non_strict_int_pf_of_strict_int_pf failed: proof is not an inequality"
#align linarith.mk_non_strict_int_pf_of_strict_int_pf linarith.mk_non_strict_int_pf_of_strict_int_pf

/-- `is_nat_prop tp` is true iff `tp` is an inequality or equality between natural numbers
or the negation thereof.
-/
unsafe def is_nat_prop : expr → Bool
  | q(@Eq ℕ $(_) _) => true
  | q(@LE.le ℕ $(_) _ _) => true
  | q(@LT.lt ℕ $(_) _ _) => true
  | q(@GE.ge ℕ $(_) _ _) => true
  | q(@GT.gt ℕ $(_) _ _) => true
  | q(¬$(p)) => is_nat_prop p
  | _ => false
#align linarith.is_nat_prop linarith.is_nat_prop

/-- `is_strict_int_prop tp` is true iff `tp` is a strict inequality between integers
or the negation of a weak inequality between integers.
-/
unsafe def is_strict_int_prop : expr → Bool
  | q(@LT.lt ℤ $(_) _ _) => true
  | q(@GT.gt ℤ $(_) _ _) => true
  | q(¬@LE.le ℤ $(_) _ _) => true
  | q(¬@GE.ge ℤ $(_) _ _) => true
  | _ => false
#align linarith.is_strict_int_prop linarith.is_strict_int_prop

private unsafe def filter_comparisons_aux : expr → Bool
  | q(¬$(p)) => p.app_symbol_in [`has_lt.lt, `has_le.le, `gt, `ge]
  | tp => tp.app_symbol_in [`has_lt.lt, `has_le.le, `gt, `ge, `eq]
#align linarith.filter_comparisons_aux linarith.filter_comparisons_aux

/-- Removes any expressions that are not proofs of inequalities, equalities, or negations thereof.
-/
unsafe def filter_comparisons : preprocessor
    where
  Name := "filter terms that are not proofs of comparisons"
  transform h :=
    (do
        let tp ← infer_type h
        is_prop tp >>= guardb
        guardb (filter_comparisons_aux tp)
        return [h]) <|>
      return []
#align linarith.filter_comparisons linarith.filter_comparisons

/-- Replaces proofs of negations of comparisons with proofs of the reversed comparisons.
For example, a proof of `¬ a < b` will become a proof of `a ≥ b`.
-/
unsafe def remove_negations : preprocessor
    where
  Name := "replace negations of comparisons"
  transform h := do
    let tp ← infer_type h
    match tp with
      | q(¬$(p)) => singleton <$> rem_neg h p
      | _ => return [h]
#align linarith.remove_negations linarith.remove_negations

/-- If `h` is an equality or inequality between natural numbers,
`nat_to_int` lifts this inequality to the integers.
It also adds the facts that the integers involved are nonnegative.
To avoid adding the same nonnegativity facts many times, it is a global preprocessor.
 -/
unsafe def nat_to_int : global_preprocessor
    where
  Name := "move nats to ints"
  transform l :=-- we lock the tactic state here because a `simplify` call inside of
  -- `zify_proof` corrupts the tactic state when run under `io.run_tactic`.
  do
    let l ←
      lock_tactic_state <|
          l.mmap fun h => (infer_type h >>= guardb ∘ is_nat_prop) >> zify_proof [] h <|> return h
    let nonnegs ←
      l.mfoldl
          (fun (es : expr_set) h => do
            let (a, b) ← infer_type h >>= get_rel_sides
            return <| (es (get_nat_comps a)).insert_list (get_nat_comps b))
          mk_rb_set
    (· ++ ·) l <$> nonnegs mk_coe_nat_nonneg_prf
#align linarith.nat_to_int linarith.nat_to_int

/-- `strengthen_strict_int h` turns a proof `h` of a strict integer inequality `t1 < t2`
into a proof of `t1 ≤ t2 + 1`. -/
unsafe def strengthen_strict_int : preprocessor
    where
  Name := "strengthen strict inequalities over int"
  transform h := do
    let tp ← infer_type h
    guardb (is_strict_int_prop tp) >> singleton <$> mk_non_strict_int_pf_of_strict_int_pf h <|>
        return [h]
#align linarith.strengthen_strict_int linarith.strengthen_strict_int

/-- `mk_comp_with_zero h` takes a proof `h` of an equality, inequality, or negation thereof,
and turns it into a proof of a comparison `_ R 0`, where `R ∈ {=, ≤, <}`.
 -/
unsafe def make_comp_with_zero : preprocessor
    where
  Name := "make comparisons with zero"
  transform e := singleton <$> rearr_comp e <|> return []
#align linarith.make_comp_with_zero linarith.make_comp_with_zero

/-- `normalize_denominators_in_lhs h lhs` assumes that `h` is a proof of `lhs R 0`.
It creates a proof of `lhs' R 0`, where all numeric division in `lhs` has been cancelled.
-/
unsafe def normalize_denominators_in_lhs (h lhs : expr) : tactic expr := do
  let (v, lhs') ← cancel_factors.derive lhs
  if v = 1 then return h
    else do
      let (ih, h'') ← mk_single_comp_zero_pf v h
      let (_, nep, _) ← infer_type h'' >>= rewrite_core lhs'
      mk_eq_mp nep h''
#align linarith.normalize_denominators_in_lhs linarith.normalize_denominators_in_lhs

/-- `cancel_denoms pf` assumes `pf` is a proof of `t R 0`. If `t` contains the division symbol `/`,
it tries to scale `t` to cancel out division by numerals.
-/
unsafe def cancel_denoms : preprocessor
    where
  Name := "cancel denominators"
  transform pf :=
    (do
        let some (_, lhs) ← parse_into_comp_and_expr <$> infer_type pf
        guardb <| lhs (· = `has_div.div)
        singleton <$> normalize_denominators_in_lhs pf lhs) <|>
      return [pf]
#align linarith.cancel_denoms linarith.cancel_denoms

-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      `find_squares m e` collects all terms of the form `a ^ 2` and `a * a` that appear in `e`
      and adds them to the set `m`.
      A pair `(a, tt)` is added to `m` when `a^2` appears in `e`, and `(a, ff)` is added to `m`
      when `a*a` appears in `e`.  -/
    unsafe
  def
    find_squares
    : rb_set ( expr × Bool ) → expr → tactic ( rb_set <| expr ×ₗ Bool )
    | s , q( $ ( a ) ^ 2 ) => do let s ← find_squares s a return ( s ( a , tt ) )
      |
        s , e @ q( $ ( e1 ) * $ ( e2 ) )
        =>
        if
          e1 = e2
          then
          do let s ← find_squares s e1 return ( s ( e1 , ff ) )
          else
          e . mfoldl find_squares s
      | s , e => e . mfoldl find_squares s
#align linarith.find_squares linarith.find_squares

/-- `nlinarith_extras` is the preprocessor corresponding to the `nlinarith` tactic.

* For every term `t` such that `t^2` or `t*t` appears in the input, adds a proof of `t^2 ≥ 0`
  or `t*t ≥ 0`.
* For every pair of comparisons `t1 R1 0` and `t2 R2 0`, adds a proof of `t1*t2 R 0`.

This preprocessor is typically run last, after all inputs have been canonized.
-/
unsafe def nlinarith_extras : global_preprocessor
    where
  Name := "nonlinear arithmetic extras"
  transform ls := do
    let s ← ls.mfoldr (fun h s' => infer_type h >>= find_squares s') mk_rb_set
    let new_es ←
      (s.mfold ([] : List expr)) fun ⟨e, is_sq⟩ new_es =>
          (do
              let p ← mk_app (if is_sq then `` sq_nonneg else `` mul_self_nonneg) [e]
              return <| p :: new_es) <|>
            return new_es
    let new_es ← make_comp_with_zero.globalize.transform new_es
    linarith_trace "nlinarith preprocessing found squares"
    linarith_trace s
    linarith_trace_proofs "so we added proofs" new_es
    let with_comps ←
      (new_es ++ ls).mmap fun e => do
          let tp ← infer_type e
          return <| (parse_into_comp_and_expr tp).elim (ineq.lt, e) fun ⟨ine, _⟩ => (ine, e)
    let products ←
      with_comps.mmapUpperTriangle fun ⟨posa, a⟩ ⟨posb, b⟩ =>
          (some <$>
              match posa, posb with
              | ineq.eq, _ => mk_app `` zero_mul_eq [a, b]
              | _, ineq.eq => mk_app `` mul_zero_eq [a, b]
              | ineq.lt, ineq.lt => mk_app `` mul_pos_of_neg_of_neg [a, b]
              | ineq.lt, ineq.le => do
                let a ← mk_app `` le_of_lt [a]
                mk_app `` mul_nonneg_of_nonpos_of_nonpos [a, b]
              | ineq.le, ineq.lt => do
                let b ← mk_app `` le_of_lt [b]
                mk_app `` mul_nonneg_of_nonpos_of_nonpos [a, b]
              | ineq.le, ineq.le => mk_app `` mul_nonneg_of_nonpos_of_nonpos [a, b]) <|>
            return none
    let products ← make_comp_with_zero.globalize.transform products.reduceOption
    return <| new_es ++ ls ++ products
#align linarith.nlinarith_extras linarith.nlinarith_extras

/--
`remove_ne_aux` case splits on any proof `h : a ≠ b` in the input, turning it into `a < b ∨ a > b`.
This produces `2^n` branches when there are `n` such hypotheses in the input.
-/
unsafe def remove_ne_aux : List expr → tactic (List branch) := fun hs =>
  (do
      let e ←
        hs.mfind fun e : expr => do
            let e ← infer_type e
            guard <| e
      let [(_, ng1), (_, ng2)] ← to_expr ``(Or.elim (lt_or_gt_of_ne $(e))) >>= apply
      let do_goal : expr → tactic (List branch) := fun g => do
          set_goals [g]
          let h ← intro1
          let ls ← remove_ne_aux <| hs.removeAll [e]
          return <| ls fun b : branch => (b.1, h :: b.2)
        (· ++ ·) <$> do_goal ng1 <*> do_goal ng2) <|>
    do
    let g ← get_goal
    return [(g, hs)]
#align linarith.remove_ne_aux linarith.remove_ne_aux

/-- `remove_ne` case splits on any proof `h : a ≠ b` in the input, turning it into `a < b ∨ a > b`,
by calling `linarith.remove_ne_aux`.
This produces `2^n` branches when there are `n` such hypotheses in the input.
-/
unsafe def remove_ne : global_branching_preprocessor
    where
  Name := "remove_ne"
  transform := remove_ne_aux
#align linarith.remove_ne linarith.remove_ne

/-- The default list of preprocessors, in the order they should typically run.
-/
unsafe def default_preprocessors : List global_branching_preprocessor :=
  [filter_comparisons, remove_negations, nat_to_int, strengthen_strict_int, make_comp_with_zero,
    cancel_denoms]
#align linarith.default_preprocessors linarith.default_preprocessors

/-- `preprocess pps l` takes a list `l` of proofs of propositions.
It maps each preprocessor `pp ∈ pps` over this list.
The preprocessors are run sequentially: each recieves the output of the previous one.
Note that a preprocessor may produce multiple or no expressions from each input expression,
so the size of the list may change.
-/
unsafe def preprocess (pps : List global_branching_preprocessor) (l : List expr) :
    tactic (List branch) := do
  let g ← get_goal
  pps (fun ls pp => List.join <$> ls fun b => set_goals [b.1] >> pp b.2) [(g, l)]
#align linarith.preprocess linarith.preprocess

end Linarith

