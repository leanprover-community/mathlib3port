/-
Copyright (c) 2022 Mario Carneiro, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Heather Macbeth, Yaël Dillies
-/
import Tactic.NormNum
import Algebra.Order.Field.Power
import Algebra.Order.Hom.Basic
import Data.Nat.Factorial.Basic

#align_import tactic.positivity from "leanprover-community/mathlib"@"e90e0a6119d01e3ef1703b3038b555785a998285"

/-! # `positivity` tactic

The `positivity` tactic in this file solves goals of the form `0 ≤ x`, `0 < x` and `x ≠ 0`.  The
tactic works recursively according to the syntax of the expression `x`.  For example, a goal of the
form `0 ≤ 3 * a ^ 2 + b * c` can be solved either
* by a hypothesis such as `5 ≤ 3 * a ^ 2 + b * c` which directly implies the nonegativity of
  `3 * a ^ 2 + b * c`; or,
* by the application of the lemma `add_nonneg` and the success of the `positivity` tactic on the two
  sub-expressions `3 * a ^ 2` and `b * c`.

For each supported operation, one must write a small tactic, tagged with the attribute
`@[positivity]`, which operates only on goals whose leading function application is that operation.
Typically, this small tactic will run the full `positivity` tactic on one or more of the function's
arguments (which is where the recursion comes in), and if successful will combine this with an
appropriate lemma to give positivity of the full expression.

This file contains the core `positivity` logic and the small tactics handling the basic operations:
`min`, `max`, `+`, `*`, `/`, `⁻¹`, raising to natural powers, and taking absolute values.  Further
extensions, e.g. to handle `real.sqrt` and norms, can be found in the files of the library which
introduce these operations.

## Main declarations

* `tactic.norm_num.positivity` tries to prove positivity of an expression by running `norm_num` on
  it.  This is one of the base cases of the recursion.
* `tactic.positivity.compare_hyp` tries to prove positivity of an expression by comparing with a
  provided hypothesis.  If the hypothesis is of the form `a ≤ b` or similar, with `b` matching the
  expression whose proof of positivity is desired, then it will check whether `a` can be proved
  positive via `tactic.norm_num.positivity` and if so apply a transitivity lemma.  This is the other
  base case of the recursion.
* `tactic.positivity.attr` creates the `positivity` user attribute for tagging the extension
  tactics handling specific operations, and specifies the behaviour for a single step of the
  recursion
* `tactic.positivity.core` collects the list of tactics with the `@[positivity]` attribute and
  calls the first recursion step as specified in `tactic.positivity.attr`.  Its input is `e : expr`
  and its output (if it succeeds) is a term of a custom inductive type
  `tactic.positivity.strictness`, containing an `expr` which is a proof of the
  strict-positivity/nonnegativity of `e` as well as an indication of whether what could be proved
  was strict-positivity or nonnegativity
* `tactic.positivity.order_rel` is a custom inductive type recording whether the goal is
  `0 ≤ e`/`e ≥ 0`, `0 < e`/`e > 0`, `e ≠ 0` or `0 ≠ e`.
* `tactic.interactive.positivity` is the user-facing tactic.  It parses the goal and, if it is of
  one of the forms `0 ≤ e`, `0 < e`, `e > 0`, `e ≥ 0`, `e ≠ 0`, `0 ≠ e`, it sends `e` to
  `tactic.positivity.core`.

## TODO

Implement extensions for other operations (raising to non-numeral powers, `log`).
-/


namespace Tactic

/-- Inductive type recording either `positive` and an expression (typically a proof of a fact
`0 < x`) or `nonnegative` and an expression (typically a proof of a fact `0 ≤ x`). -/
unsafe inductive positivity.strictness : Type
  | positive : expr → positivity.strictness
  | nonnegative : expr → positivity.strictness
  | nonzero : expr → positivity.strictness
  deriving DecidableEq
#align tactic.positivity.strictness tactic.positivity.strictness

export Positivity.Strictness (positive nonnegative nonzero)

unsafe instance : ToString strictness :=
  ⟨fun s =>
    match s with
    | positive p => "strictness.positive (" ++ toString p ++ ")"
    | nonnegative p => "strictness.nonnegative (" ++ toString p ++ ")"
    | nonzero p => "strictness.nonzero (" ++ toString p ++ ")"⟩

unsafe instance : has_to_format strictness :=
  ⟨fun s => toString s⟩

private theorem lt_of_eq_of_lt'' {α} [Preorder α] {b b' a : α} : b = b' → a < b' → a < b :=
  fun h1 h2 => lt_of_lt_of_eq h2 h1.symm

/-- First base case of the `positivity` tactic.  We try `norm_num` to prove directly that an
expression `e` is positive, nonnegative or non-zero. -/
unsafe def norm_num.positivity (e : expr) : tactic strictness := do
  let (e', p) ← norm_num.derive e <|> refl_conv e
  let e'' ← e'.to_rat
  let typ ← infer_type e'
  let ic ← mk_instance_cache typ
  if e'' > 0 then do
      let (ic, p₁) ← norm_num.prove_pos ic e'
      positive <$> mk_app `` lt_of_eq_of_lt'' [p, p₁]
    else
      if e'' = 0 then nonnegative <$> mk_app `` ge_of_eq [p]
      else do
        let (ic, p₁) ← norm_num.prove_ne_zero' ic e'
        nonzero <$> to_expr ``(ne_of_eq_of_ne $(p) $(p₁))
#align tactic.norm_num.positivity tactic.norm_num.positivity

/-- Second base case of the `positivity` tactic: Any element of a canonically ordered additive
monoid is nonnegative. -/
unsafe def positivity_canon : expr → tactic strictness
  | q($(a)) => nonnegative <$> mk_app `` zero_le [a]
#align tactic.positivity_canon tactic.positivity_canon

namespace Positivity

/-- Inductive type recording whether the goal `positivity` is called on is nonnegativity, positivity
or different from `0`. -/
inductive OrderRel : Type
  | le : order_rel-- `0 ≤ a`

  | lt : order_rel-- `0 < a`

  | Ne : order_rel-- `a ≠ 0`

  | ne' : order_rel
  deriving Inhabited
#align tactic.positivity.order_rel Tactic.Positivity.OrderRel

-- `0 ≠ a`
unsafe instance : has_to_format OrderRel :=
  ⟨fun r =>
    match r with
    | order_rel.le => "order_rel.le"
    | order_rel.lt => "order_rel.lt"
    | order_rel.ne => "order_rel.ne"
    | order_rel.ne' => "order_rel.ne'"⟩

/-- Given two tactics whose result is `strictness`, report a `strictness`:
- if at least one gives `positive`, report `positive` and one of the expressions giving a proof of
  positivity
- if one reports `nonnegative` and the other reports `nonzero`, report `positive`
- else if at least one reports `nonnegative`, report `nonnegative` and one of the
  expressions giving a proof of nonnegativity
- else if at least one reports `nonzero`, report `nonzero` and one of the expressions giving a proof
  of nonzeroness
- if both fail, fail -/
protected unsafe def orelse (tac1 tac2 : tactic strictness) : tactic strictness := do
  let res1 ← try_core tac1
  match res1 with
    | none => tac2
    | some p1@(positive _) => pure p1
    | some (nonnegative e1) => do
      let res2 ← try_core tac2
      match res2 with
        | some p2@(positive _) => pure p2
        | some (nonzero e2) => positive <$> mk_app `` lt_of_le_of_ne' [e1, e2]
        | _ => pure (nonnegative e1)
    | some (nonzero e1) => do
      let res2 ← try_core tac2
      match res2 with
        | some p2@(positive _) => pure p2
        | some (nonnegative e2) => positive <$> mk_app `` lt_of_le_of_ne' [e2, e1]
        | _ => pure (nonzero e1)
#align tactic.positivity.orelse tactic.positivity.orelse

scoped[Positivity] infixr:2 " ≤|≥ " => tactic.positivity.orelse

/-- This tactic fails with a message saying that `positivity` couldn't prove anything about `e`
if we only know that `a` and `b` are positive/nonnegative/nonzero (according to `pa` and `pb`). -/
unsafe def positivity_fail {α : Type _} (e a b : expr) (pa pb : strictness) : tactic α := do
  let e' ← pp e
  let a' ← pp a
  let b' ← pp b
  let f : strictness → format → format := fun p c =>
    match p with
    | positive _ => "0 < " ++ c
    | nonnegative _ => "0 ≤ " ++ c
    | nonzero _ => c ++ " ≠ 0"
  fail
      (↑"`positivity` can't say anything about `" ++ e' ++ "` knowing only `" ++ f pa a' ++
            "` and `" ++
          f pb b' ++
        "`")
#align tactic.positivity.positivity_fail tactic.positivity.positivity_fail

/-! ### Core logic of the `positivity` tactic -/


private theorem ne_of_ne_of_eq' {α : Type _} {a b c : α} (ha : a ≠ c) (h : a = b) : b ≠ c := by
  rwa [← h]

/-- Calls `norm_num` on `a` to prove positivity/nonnegativity of `e` assuming `b` is defeq to `e`
and `p₂ : a ≤ b`. -/
unsafe def compare_hyp_le (e a b p₂ : expr) : tactic strictness := do
  is_def_eq e b
  let strict_a ← norm_num.positivity a
  match strict_a with
    | positive p₁ => positive <$> mk_app `` lt_of_lt_of_le [p₁, p₂]
    | nonnegative p₁ => nonnegative <$> mk_app `` le_trans [p₁, p₂]
    | _ => do
      let e' ← pp e
      let p₂' ← pp p₂
      fail (↑"`norm_num` can't prove nonnegativity of " ++ e' ++ " using " ++ p₂')
#align tactic.positivity.compare_hyp_le tactic.positivity.compare_hyp_le

/-- Calls `norm_num` on `a` to prove positivity/nonnegativity of `e` assuming `b` is defeq to `e`
and `p₂ : a < b`. -/
unsafe def compare_hyp_lt (e a b p₂ : expr) : tactic strictness := do
  is_def_eq e b
  let strict_a ← norm_num.positivity a
  match strict_a with
    | positive p₁ => positive <$> mk_app `` lt_trans [p₁, p₂]
    | nonnegative p₁ => positive <$> mk_app `` lt_of_le_of_lt [p₁, p₂]
    | _ => do
      let e' ← pp e
      let p₂' ← pp p₂
      fail (↑"`norm_num` can't prove positivity of " ++ e' ++ " using " ++ p₂')
#align tactic.positivity.compare_hyp_lt tactic.positivity.compare_hyp_lt

/-- Calls `norm_num` on `a` to prove positivity/nonnegativity/nonzeroness of `e` assuming `b` is
defeq to `e` and `p₂ : a = b`. -/
unsafe def compare_hyp_eq (e a b p₂ : expr) : tactic strictness := do
  is_def_eq e b
  let strict_a ← norm_num.positivity a
  match strict_a with
    | positive p₁ => positive <$> mk_app `` lt_of_lt_of_eq [p₁, p₂]
    | nonnegative p₁ => nonnegative <$> mk_app `` le_of_le_of_eq [p₁, p₂]
    | nonzero p₁ => nonzero <$> to_expr ``(ne_of_ne_of_eq' $(p₁) $(p₂))
#align tactic.positivity.compare_hyp_eq tactic.positivity.compare_hyp_eq

/-- Calls `norm_num` on `a` to prove nonzeroness of `e` assuming `b` is defeq to `e` and
`p₂ : b ≠ a`. -/
unsafe def compare_hyp_ne (e a b p₂ : expr) : tactic strictness := do
  is_def_eq e b
  let (a', p₁) ← norm_num.derive a <|> refl_conv a
  let a'' ← a'.to_rat
  if a'' = 0 then nonzero <$> mk_mapp `` ne_of_ne_of_eq [none, none, none, none, p₂, p₁]
    else do
      let e' ← pp e
      let p₂' ← pp p₂
      let a' ← pp a
      fail
          (↑"`norm_num` can't prove non-zeroness of " ++ e' ++ " using " ++ p₂' ++ " because " ++
              a' ++
            " is non-zero")
#align tactic.positivity.compare_hyp_ne tactic.positivity.compare_hyp_ne

-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      Third base case of the `positivity` tactic.  Prove an expression `e` is
      positive/nonnegative/nonzero by finding a hypothesis of the form `a < e`, `a ≤ e` or `a = e` in
      which `a` can be proved positive/nonnegative/nonzero by `norm_num`. -/
    unsafe
  def
    compare_hyp
    ( e p₂ : expr ) : tactic strictness
    :=
      do
        let p_typ ← infer_type p₂
          match
            p_typ
            with
            | q( $ ( lo ) ≤ $ ( hi ) ) => compare_hyp_le e lo hi p₂
              | q( $ ( hi ) ≥ $ ( lo ) ) => compare_hyp_le e lo hi p₂
              | q( $ ( lo ) < $ ( hi ) ) => compare_hyp_lt e lo hi p₂
              | q( $ ( hi ) > $ ( lo ) ) => compare_hyp_lt e lo hi p₂
              |
                q( $ ( lo ) = $ ( hi ) )
                =>
                compare_hyp_eq e lo hi p₂
                  <|>
                  do let p₂' ← mk_app ` ` Eq.symm [ p₂ ] compare_hyp_eq e hi lo p₂'
              |
                q( $ ( hi ) ≠ $ ( lo ) )
                =>
                compare_hyp_ne e lo hi p₂
                  <|>
                  do
                    let p₂' ← mk_mapp ` ` Ne.symm [ none , none , none , p₂ ]
                      compare_hyp_ne e hi lo p₂'
              |
                e
                =>
                do
                  let p₂' ← pp p₂
                    fail ( p₂' ++ "is not of the form `a ≤ b`, `a < b`, `a = b` or `a ≠ b`" )
#align tactic.positivity.compare_hyp tactic.positivity.compare_hyp

/-- Attribute allowing a user to tag a tactic as an extension for `tactic.interactive.positivity`.
The main (recursive) step of this tactic is to try successively all the extensions tagged with this
attribute on the expression at hand, and also to try the two "base case" tactics
`tactic.norm_num.positivity`, `tactic.positivity.compare_hyp` on the expression at hand. -/
@[user_attribute]
unsafe def attr : user_attribute (expr → tactic strictness) Unit
    where
  Name := `positivity
  descr := "extensions handling particular operations for the `positivity` tactic"
  cache_cfg :=
    { mk_cache := fun ns => do
        let t ←
          ns.foldlM
              (fun (t : expr → tactic strictness) n => do
                let t' ← eval_expr (expr → tactic strictness) (expr.const n [])
                pure fun e => t' e ≤|≥ t e)
              fun _ => failed
        pure fun e =>
            -- run all the extensions on `e`
                t
                e ≤|≥-- directly try `norm_num` on `e`
                  norm_num.positivity
                  e ≤|≥-- try showing nonnegativity from canonicity of the order
                    -- loop over hypotheses and try to compare with `e`
                    positivity_canon
                    e ≤|≥
                  local_context >>=
                    List.foldl (fun tac h => tac ≤|≥ compare_hyp e h)
                      (fail "no applicable positivity extension found")
      dependencies := [] }
#align tactic.positivity.attr tactic.positivity.attr

/-- Look for a proof of positivity/nonnegativity of an expression `e`; if found, return the proof
together with a `strictness` stating whether the proof found was for strict positivity
(`positive p`), nonnegativity (`nonnegative p`), or nonzeroness (`nonzero p`). -/
unsafe def core (e : expr) : tactic strictness := do
  let f ← attr.get_cache
  f e <|> fail "failed to prove positivity/nonnegativity/nonzeroness"
#align tactic.positivity.core tactic.positivity.core

end Positivity

open Positivity

open scoped Positivity

namespace Interactive

/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:38:34: unsupported: setup_tactic_parser -/
-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      Tactic solving goals of the form `0 ≤ x`, `0 < x` and `x ≠ 0`.  The tactic works recursively
      according to the syntax of the expression `x`, if the atoms composing the expression all have
      numeric lower bounds which can be proved positive/nonnegative/nonzero by `norm_num`.  This tactic
      either closes the goal or fails.
      
      Examples:
      ```
      example {a : ℤ} (ha : 3 < a) : 0 ≤ a ^ 3 + a := by positivity
      
      example {a : ℤ} (ha : 1 < a) : 0 < |(3:ℤ) + a| := by positivity
      
      example {b : ℤ} : 0 ≤ max (-3) (b ^ 2) := by positivity
      ```
      -/
    unsafe
  def
    positivity
    : tactic Unit
    :=
      focus1
        do
          let t ← target >>= instantiate_mvars
            let
              ( rel_desired , a )
                ←
                match
                  t
                  with
                  | q( 0 ≤ $ ( e ) ) => pure ( OrderRel.le , e )
                    | q( $ ( e ) ≥ 0 ) => pure ( OrderRel.le , e )
                    | q( 0 < $ ( e ) ) => pure ( OrderRel.lt , e )
                    | q( $ ( e ) > 0 ) => pure ( OrderRel.lt , e )
                    |
                      q( $ ( e₁ ) ≠ $ ( e₂ ) )
                      =>
                      do
                        match
                          e₂
                          with
                          | q( Zero.zero ) => pure ( order_rel.ne , e₁ )
                            |
                              _
                              =>
                              match
                                e₁
                                with
                                | q( Zero.zero ) => pure ( order_rel.ne' , e₂ )
                                  | _ => fail "not a positivity/nonnegativity/nonzeroness goal"
                    | _ => fail "not a positivity/nonnegativity/nonzeroness goal"
            let strictness_proved ← tactic.positivity.core a
            (
                match
                  rel_desired , strictness_proved
                  with
                  | order_rel.lt , positive p => pure p
                    |
                      order_rel.lt , nonnegative _
                      =>
                      fail
                        (
                          "failed to prove strict positivity, but it would be "
                            ++
                            "possible to prove nonnegativity if desired"
                          )
                    |
                      order_rel.lt , nonzero _
                      =>
                      fail
                        (
                          "failed to prove strict positivity, but it would be "
                            ++
                            "possible to prove nonzeroness if desired"
                          )
                    | order_rel.le , positive p => mk_app ` ` le_of_lt [ p ]
                    | order_rel.le , nonnegative p => pure p
                    |
                      order_rel.le , nonzero _
                      =>
                      fail
                        (
                          "failed to prove nonnegativity, but it would be "
                            ++
                            "possible to prove nonzeroness if desired"
                          )
                    | order_rel.ne , positive p => to_expr ` `( ne_of_gt $ ( p ) )
                    |
                      order_rel.ne , nonnegative _
                      =>
                      fail
                        (
                          "failed to prove nonzeroness, but it would be "
                            ++
                            "possible to prove nonnegativity if desired"
                          )
                    | order_rel.ne , nonzero p => pure p
                    | order_rel.ne' , positive p => to_expr ` `( ne_of_lt $ ( p ) )
                    |
                      order_rel.ne' , nonnegative _
                      =>
                      fail
                        (
                          "failed to prove nonzeroness, but it would be "
                            ++
                            "possible to prove nonnegativity if desired"
                          )
                    | order_rel.ne' , nonzero p => to_expr ` `( Ne.symm $ ( p ) )
                )
              >>=
              tactic.exact
#align tactic.interactive.positivity tactic.interactive.positivity

add_tactic_doc
  { Name := "positivity"
    category := DocCategory.tactic
    declNames := [`tactic.interactive.positivity]
    tags := ["arithmetic", "monotonicity", "finishing"] }

end Interactive

variable {ι α R : Type _}

/-! ### `positivity` extensions for particular arithmetic operations -/


section ite

variable [Zero α] {p : Prop} [Decidable p] {a b : α}

private theorem ite_pos [LT α] (ha : 0 < a) (hb : 0 < b) : 0 < ite p a b := by
  by_cases p <;> simp [*]

private theorem ite_nonneg [LE α] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ ite p a b := by
  by_cases p <;> simp [*]

private theorem ite_nonneg_of_pos_of_nonneg [Preorder α] (ha : 0 < a) (hb : 0 ≤ b) :
    0 ≤ ite p a b :=
  ite_nonneg ha.le hb

private theorem ite_nonneg_of_nonneg_of_pos [Preorder α] (ha : 0 ≤ a) (hb : 0 < b) :
    0 ≤ ite p a b :=
  ite_nonneg ha hb.le

private theorem ite_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : ite p a b ≠ 0 := by by_cases p <;> simp [*]

private theorem ite_ne_zero_of_pos_of_ne_zero [Preorder α] (ha : 0 < a) (hb : b ≠ 0) :
    ite p a b ≠ 0 :=
  ite_ne_zero ha.ne' hb

private theorem ite_ne_zero_of_ne_zero_of_pos [Preorder α] (ha : a ≠ 0) (hb : 0 < b) :
    ite p a b ≠ 0 :=
  ite_ne_zero ha hb.ne'

end ite

/-- Extension for the `positivity` tactic: the `if then else` of two numbers is
positive/nonnegative/nonzero if both are. -/
@[positivity]
unsafe def positivity_ite : expr → tactic strictness
  | e@q(@ite $(typ) $(p) $(hp) $(a) $(b)) => do
    let strictness_a ← core a
    let strictness_b ← core b
    match strictness_a, strictness_b with
      | positive pa, positive pb => positive <$> mk_app `` ite_pos [pa, pb]
      | positive pa, nonnegative pb =>
        nonnegative <$> mk_app `` ite_nonneg_of_pos_of_nonneg [pa, pb]
      | nonnegative pa, positive pb =>
        nonnegative <$> mk_app `` ite_nonneg_of_nonneg_of_pos [pa, pb]
      | nonnegative pa, nonnegative pb => nonnegative <$> mk_app `` ite_nonneg [pa, pb]
      | positive pa, nonzero pb => nonzero <$> to_expr ``(ite_ne_zero_of_pos_of_ne_zero $(pa) $(pb))
      | nonzero pa, positive pb => nonzero <$> to_expr ``(ite_ne_zero_of_ne_zero_of_pos $(pa) $(pb))
      | nonzero pa, nonzero pb => nonzero <$> to_expr ``(ite_ne_zero $(pa) $(pb))
      | sa@_, sb@_ => positivity_fail e a b sa sb
  | e => pp e >>= fail ∘ format.bracket "The expression `" "` isn't of the form `ite p a b`"
#align tactic.positivity_ite tactic.positivity_ite

section LinearOrder

variable [LinearOrder R] {a b c : R}

private theorem le_min_of_lt_of_le (ha : a < b) (hb : a ≤ c) : a ≤ min b c :=
  le_min ha.le hb

private theorem le_min_of_le_of_lt (ha : a ≤ b) (hb : a < c) : a ≤ min b c :=
  le_min ha hb.le

private theorem min_ne (ha : a ≠ c) (hb : b ≠ c) : min a b ≠ c := by rw [min_def];
  split_ifs <;> assumption

private theorem min_ne_of_ne_of_lt (ha : a ≠ c) (hb : c < b) : min a b ≠ c :=
  min_ne ha hb.ne'

private theorem min_ne_of_lt_of_ne (ha : c < a) (hb : b ≠ c) : min a b ≠ c :=
  min_ne ha.ne' hb

private theorem max_ne (ha : a ≠ c) (hb : b ≠ c) : max a b ≠ c := by rw [max_def];
  split_ifs <;> assumption

end LinearOrder

/-- Extension for the `positivity` tactic: the `min` of two numbers is nonnegative if both are
nonnegative, and strictly positive if both are. -/
@[positivity]
unsafe def positivity_min : expr → tactic strictness
  | e@q(min $(a) $(b)) => do
    let strictness_a ← core a
    let strictness_b ← core b
    match strictness_a, strictness_b with
      | positive pa, positive pb => positive <$> mk_app `` lt_min [pa, pb]
      | positive pa, nonnegative pb => nonnegative <$> mk_app `` le_min_of_lt_of_le [pa, pb]
      | nonnegative pa, positive pb => nonnegative <$> mk_app `` le_min_of_le_of_lt [pa, pb]
      | nonnegative pa, nonnegative pb => nonnegative <$> mk_app `` le_min [pa, pb]
      | positive pa, nonzero pb => nonzero <$> to_expr ``(min_ne_of_lt_of_ne $(pa) $(pb))
      | nonzero pa, positive pb => nonzero <$> to_expr ``(min_ne_of_ne_of_lt $(pa) $(pb))
      | nonzero pa, nonzero pb => nonzero <$> to_expr ``(min_ne $(pa) $(pb))
      | sa@_, sb@_ => positivity_fail e a b sa sb
  | e => pp e >>= fail ∘ format.bracket "The expression `" "` isn't of the form `min a b`"
#align tactic.positivity_min tactic.positivity_min

/-- Extension for the `positivity` tactic: the `max` of two numbers is nonnegative if at least one
is nonnegative, strictly positive if at least one is positive, and nonzero if both are nonzero. -/
@[positivity]
unsafe def positivity_max : expr → tactic strictness
  | q(max $(a) $(b)) => do
    let strictness_a ← try_core (core a)
    (-- If `a ≠ 0`, we might prove `max a b ≠ 0` if `b ≠ 0` but we don't want to evaluate
        -- `b` before having ruled out `0 < a`, for performance. So we do that in the second branch
        -- of the `orelse'`.
        do
          match strictness_a with
            | some (positive pa) =>
              positive <$> mk_mapp `` lt_max_of_lt_left [none, none, none, a, b, pa]
            | some (nonnegative pa) =>
              nonnegative <$> mk_mapp `` le_max_of_le_left [none, none, none, a, b, pa]
            | _ => failed) ≤|≥
        do
        let strictness_b ← core b
        match strictness_b with
          | positive pb => positive <$> mk_mapp `` lt_max_of_lt_right [none, none, none, a, b, pb]
          | nonnegative pb =>
            nonnegative <$> mk_mapp `` le_max_of_le_right [none, none, none, a, b, pb]
          | nonzero pb => do
            let nonzero pa ← strictness_a
            nonzero <$> to_expr ``(max_ne $(pa) $(pb))
  | e => pp e >>= fail ∘ format.bracket "The expression `" "` isn't of the form `max a b`"
#align tactic.positivity_max tactic.positivity_max

-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      Extension for the `positivity` tactic: addition is nonnegative if both summands are nonnegative,
      and strictly positive if at least one summand is. -/
    @[ positivity ]
    unsafe
  def
    positivity_add
    : expr → tactic strictness
    |
        e @ q( $ ( a ) + $ ( b ) )
        =>
        do
          let strictness_a ← core a
            let strictness_b ← core b
            match
              strictness_a , strictness_b
              with
              | positive pa , positive pb => positive <$> mk_app ` ` add_pos [ pa , pb ]
                |
                  positive pa , nonnegative pb
                  =>
                  positive <$> mk_app ` ` lt_add_of_pos_of_le [ pa , pb ]
                |
                  nonnegative pa , positive pb
                  =>
                  positive <$> mk_app ` ` lt_add_of_le_of_pos [ pa , pb ]
                |
                  nonnegative pa , nonnegative pb
                  =>
                  nonnegative <$> mk_app ` ` add_nonneg [ pa , pb ]
                | sa @ _ , sb @ _ => positivity_fail e a b sa sb
      | e => pp e >>= fail ∘ format.bracket "The expression `" "` isn't of the form `a + b`"
#align tactic.positivity_add tactic.positivity_add

section OrderedSemiring

variable [OrderedSemiring R] {a b : R}

private theorem mul_nonneg_of_pos_of_nonneg (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ a * b :=
  mul_nonneg ha.le hb

private theorem mul_nonneg_of_nonneg_of_pos (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a * b :=
  mul_nonneg ha hb.le

private theorem mul_ne_zero_of_pos_of_ne_zero [NoZeroDivisors R] (ha : 0 < a) (hb : b ≠ 0) :
    a * b ≠ 0 :=
  mul_ne_zero ha.ne' hb

private theorem mul_ne_zero_of_ne_zero_of_pos [NoZeroDivisors R] (ha : a ≠ 0) (hb : 0 < b) :
    a * b ≠ 0 :=
  mul_ne_zero ha hb.ne'

end OrderedSemiring

-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      Extension for the `positivity` tactic: multiplication is nonnegative/positive/nonzero if both
      multiplicands are. -/
    @[ positivity ]
    unsafe
  def
    positivity_mul
    : expr → tactic strictness
    |
        e @ q( $ ( a ) * $ ( b ) )
        =>
        do
          let strictness_a ← core a
            let strictness_b ← core b
            match
              strictness_a , strictness_b
              with
              | positive pa , positive pb => positive <$> mk_app ` ` mul_pos [ pa , pb ]
                |
                  positive pa , nonnegative pb
                  =>
                  nonnegative <$> mk_app ` ` mul_nonneg_of_pos_of_nonneg [ pa , pb ]
                |
                  nonnegative pa , positive pb
                  =>
                  nonnegative <$> mk_app ` ` mul_nonneg_of_nonneg_of_pos [ pa , pb ]
                |
                  nonnegative pa , nonnegative pb
                  =>
                  nonnegative <$> mk_app ` ` mul_nonneg [ pa , pb ]
                |
                  positive pa , nonzero pb
                  =>
                  nonzero <$> to_expr ` `( hMul_ne_zero_of_pos_of_ne_zero $ ( pa ) $ ( pb ) )
                |
                  nonzero pa , positive pb
                  =>
                  nonzero <$> to_expr ` `( hMul_ne_zero_of_ne_zero_of_pos $ ( pa ) $ ( pb ) )
                |
                  nonzero pa , nonzero pb
                  =>
                  nonzero <$> to_expr ` `( mul_ne_zero $ ( pa ) $ ( pb ) )
                | sa @ _ , sb @ _ => positivity_fail e a b sa sb
      | e => pp e >>= fail ∘ format.bracket "The expression `" "` isn't of the form `a * b`"
#align tactic.positivity_mul tactic.positivity_mul

section LinearOrderedSemifield

variable [LinearOrderedSemifield R] {a b : R}

private theorem div_nonneg_of_pos_of_nonneg (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ a / b :=
  div_nonneg ha.le hb

private theorem div_nonneg_of_nonneg_of_pos (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b :=
  div_nonneg ha hb.le

private theorem div_ne_zero_of_pos_of_ne_zero (ha : 0 < a) (hb : b ≠ 0) : a / b ≠ 0 :=
  div_ne_zero ha.ne' hb

private theorem div_ne_zero_of_ne_zero_of_pos (ha : a ≠ 0) (hb : 0 < b) : a / b ≠ 0 :=
  div_ne_zero ha hb.ne'

end LinearOrderedSemifield

private theorem int_div_self_pos {a : ℤ} (ha : 0 < a) : 0 < a / a := by rw [Int.ediv_self ha.ne'];
  exact zero_lt_one

private theorem int_div_nonneg_of_pos_of_nonneg {a b : ℤ} (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ a / b :=
  Int.div_nonneg ha.le hb

private theorem int_div_nonneg_of_nonneg_of_pos {a b : ℤ} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b :=
  Int.div_nonneg ha hb.le

private theorem int_div_nonneg_of_pos_of_pos {a b : ℤ} (ha : 0 < a) (hb : 0 < b) : 0 ≤ a / b :=
  Int.div_nonneg ha.le hb.le

-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      Extension for the `positivity` tactic: division is nonnegative if both numerator and denominator
      are nonnegative, and strictly positive if both numerator and denominator are. -/
    @[ positivity ]
    unsafe
  def
    positivity_div
    : expr → tactic strictness
    |
        e @ q( @ Div.div ℤ _ $ ( a ) $ ( b ) )
        =>
        do
          let strictness_a ← core a
            let strictness_b ← core b
            match
              strictness_a , strictness_b
              with
              |
                  positive pa , positive pb
                  =>
                  if
                    a = b
                    then
                    positive <$> mk_app ` ` int_div_self_pos [ pa ]
                    else
                    nonnegative <$> mk_app ` ` int_div_nonneg_of_pos_of_pos [ pa , pb ]
                |
                  positive pa , nonnegative pb
                  =>
                  nonnegative <$> mk_app ` ` int_div_nonneg_of_pos_of_nonneg [ pa , pb ]
                |
                  nonnegative pa , positive pb
                  =>
                  nonnegative <$> mk_app ` ` int_div_nonneg_of_nonneg_of_pos [ pa , pb ]
                |
                  nonnegative pa , nonnegative pb
                  =>
                  nonnegative <$> mk_app ` ` Int.div_nonneg [ pa , pb ]
                | sa @ _ , sb @ _ => positivity_fail e a b sa sb
      |
        e @ q( $ ( a ) / $ ( b ) )
        =>
        do
          let strictness_a ← core a
            let strictness_b ← core b
            match
              strictness_a , strictness_b
              with
              | positive pa , positive pb => positive <$> mk_app ` ` div_pos [ pa , pb ]
                |
                  positive pa , nonnegative pb
                  =>
                  nonnegative <$> mk_app ` ` div_nonneg_of_pos_of_nonneg [ pa , pb ]
                |
                  nonnegative pa , positive pb
                  =>
                  nonnegative <$> mk_app ` ` div_nonneg_of_nonneg_of_pos [ pa , pb ]
                |
                  nonnegative pa , nonnegative pb
                  =>
                  nonnegative <$> mk_app ` ` div_nonneg [ pa , pb ]
                |
                  positive pa , nonzero pb
                  =>
                  nonzero <$> to_expr ` `( div_ne_zero_of_pos_of_ne_zero $ ( pa ) $ ( pb ) )
                |
                  nonzero pa , positive pb
                  =>
                  nonzero <$> to_expr ` `( div_ne_zero_of_ne_zero_of_pos $ ( pa ) $ ( pb ) )
                |
                  nonzero pa , nonzero pb
                  =>
                  nonzero <$> to_expr ` `( div_ne_zero $ ( pa ) $ ( pb ) )
                | sa @ _ , sb @ _ => positivity_fail e a b sa sb
      | e => pp e >>= fail ∘ format.bracket "The expression `" "` isn't of the form `a / b`"
#align tactic.positivity_div tactic.positivity_div

-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      Extension for the `positivity` tactic: an inverse of a positive number is positive, an inverse
      of a nonnegative number is nonnegative. -/
    @[ positivity ]
    unsafe
  def
    positivity_inv
    : expr → tactic strictness
    |
        q( $ ( a ) ⁻¹ )
        =>
        do
          let strictness_a ← core a
            match
              strictness_a
              with
              | positive pa => positive <$> mk_app ` ` inv_pos_of_pos [ pa ]
                | nonnegative pa => nonnegative <$> mk_app ` ` inv_nonneg_of_nonneg [ pa ]
                | nonzero pa => nonzero <$> to_expr ` `( inv_ne_zero $ ( pa ) )
      | e => pp e >>= fail ∘ format.bracket "The expression `" "` isn't of the form `a⁻¹`"
#align tactic.positivity_inv tactic.positivity_inv

private theorem pow_zero_pos [OrderedSemiring R] [Nontrivial R] (a : R) : 0 < a ^ 0 :=
  zero_lt_one.trans_le (pow_zero a).ge

private theorem zpow_zero_pos [LinearOrderedSemifield R] (a : R) : 0 < a ^ (0 : ℤ) :=
  zero_lt_one.trans_le (zpow_zero a).ge

-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      Extension for the `positivity` tactic: raising a number `a` to a natural/integer power `n` is
      positive if `n = 0` (since `a ^ 0 = 1`) or if `0 < a`, and is nonnegative if `n` is even (squares
      are nonnegative) or if `0 ≤ a`. -/
    @[ positivity ]
    unsafe
  def
    positivity_pow
    : expr → tactic strictness
    |
        e @ q( $ ( a ) ^ $ ( n ) )
        =>
        do
          let typ ← infer_type n
            (
                do
                  unify typ q( ℕ )
                    if
                      n = q( 0 )
                      then
                      positive <$> mk_app ` ` pow_zero_pos [ a ]
                      else
                      do
                        (
                            match
                              n
                              with
                              |
                                  q( bit0 $ ( n ) )
                                  =>
                                  nonnegative <$> mk_app ` ` pow_bit0_nonneg [ a , n ]
                                |
                                  _
                                  =>
                                  do
                                    let e' ← pp e
                                      fail
                                        (
                                          e'
                                            ++
                                            "is not an even power so positivity can't prove it's nonnegative"
                                          )
                            )
                          ≤|≥
                          do
                            let strictness_a ← core a
                              match
                                strictness_a
                                with
                                | positive p => positive <$> mk_app ` ` pow_pos [ p , n ]
                                  | nonnegative p => nonnegative <$> mk_app `pow_nonneg [ p , n ]
                                  |
                                    nonzero p
                                    =>
                                    nonzero <$> to_expr ` `( pow_ne_zero $ ( n ) $ ( p ) )
                )
              <|>
              do
                unify typ q( ℤ )
                  if
                    n = q( ( 0 : ℤ ) )
                    then
                    positive <$> mk_app ` ` zpow_zero_pos [ a ]
                    else
                    do
                      (
                          match
                            n
                            with
                            |
                                q( bit0 $ ( n ) )
                                =>
                                nonnegative <$> mk_app ` ` zpow_bit0_nonneg [ a , n ]
                              |
                                _
                                =>
                                do
                                  let e' ← pp e
                                    fail
                                      (
                                        e'
                                          ++
                                          "is not an even power so positivity can't prove it's nonnegative"
                                        )
                          )
                        ≤|≥
                        do
                          let strictness_a ← core a
                            match
                              strictness_a
                              with
                              | positive p => positive <$> mk_app ` ` zpow_pos_of_pos [ p , n ]
                                | nonnegative p => nonnegative <$> mk_app ` ` zpow_nonneg [ p , n ]
                                |
                                  nonzero p
                                  =>
                                  nonzero <$> to_expr ` `( zpow_ne_zero $ ( n ) $ ( p ) )
      | e => pp e >>= fail ∘ format.bracket "The expression `" "` isn't of the form `a ^ n`"
#align tactic.positivity_pow tactic.positivity_pow

-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      Extension for the `positivity` tactic: raising a positive number in a canonically ordered
      semiring gives a positive number. -/
    @[ positivity ]
    unsafe
  def
    positivity_canon_pow
    : expr → tactic strictness
    |
        q( $ ( r ) ^ $ ( n ) )
        =>
        do
          let typ_n ← infer_type n
            unify typ_n q( ℕ )
            let positive p ← core r
            positive <$> mk_app ` ` CanonicallyOrderedCommSemiring.pow_pos [ p , n ]
      |
        e
        =>
        pp e
          >>=
          fail
            ∘
            format.bracket
              "The expression `"
                "` is not of the form `a ^ n` for `a` in a `canonically_ordered_comm_semiring` and `n : ℕ`"
#align tactic.positivity_canon_pow tactic.positivity_canon_pow

/- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:88:10: unsupported modifiers in user command -/
alias ⟨_, abs_pos_of_ne_zero⟩ := abs_pos
#align tactic.abs_pos_of_ne_zero Tactic.abs_pos_of_ne_zero

/-- Extension for the `positivity` tactic: an absolute value is nonnegative, and is strictly
positive if its input is nonzero. -/
@[positivity]
unsafe def positivity_abs : expr → tactic strictness
  | q(|$(a)|) => do
    (-- if can prove `0 < a` or `a ≠ 0`, report positivity
        do
          let strict_a ← core a
          match strict_a with
            | positive p => positive <$> mk_app `` abs_pos_of_pos [p]
            | nonzero p => positive <$> mk_app `` abs_pos_of_ne_zero [p]
            | _ => failed) <|>
        nonnegative <$> mk_app `` abs_nonneg [a]
  |-- else report nonnegativity
    e =>
    pp e >>= fail ∘ format.bracket "The expression `" "` isn't of the form `|a|`"
#align tactic.positivity_abs tactic.positivity_abs

private theorem int_nat_abs_pos {n : ℤ} (hn : 0 < n) : 0 < n.natAbs :=
  Int.natAbs_pos_of_ne_zero hn.ne'

/-- Extension for the `positivity` tactic: `int.nat_abs` is positive when its input is.

Since the output type of `int.nat_abs` is `ℕ`, the nonnegative case is handled by the default
`positivity` tactic.
-/
@[positivity]
unsafe def positivity_nat_abs : expr → tactic strictness
  | q(Int.natAbs $(a)) => do
    let strict_a ← core a
    match strict_a with
      | positive p => positive <$> mk_app `` int_nat_abs_pos [p]
      | nonzero p => positive <$> mk_app `` Int.natAbs_pos_of_ne_zero [p]
      | _ => failed
  | _ => failed
#align tactic.positivity_nat_abs tactic.positivity_nat_abs

private theorem nat_cast_pos [OrderedSemiring α] [Nontrivial α] {n : ℕ} : 0 < n → 0 < (n : α) :=
  Nat.cast_pos.2

private theorem int_coe_nat_nonneg (n : ℕ) : 0 ≤ (n : ℤ) :=
  n.cast_nonneg

private theorem int_coe_nat_pos {n : ℕ} : 0 < n → 0 < (n : ℤ) :=
  Nat.cast_pos.2

private theorem int_cast_ne_zero [AddGroupWithOne α] [CharZero α] {n : ℤ} : n ≠ 0 → (n : α) ≠ 0 :=
  Int.cast_ne_zero.2

private theorem int_cast_nonneg [OrderedRing α] {n : ℤ} (hn : 0 ≤ n) : 0 ≤ (n : α) := by
  rw [← Int.cast_zero]; exact Int.cast_mono hn

private theorem int_cast_pos [OrderedRing α] [Nontrivial α] {n : ℤ} : 0 < n → 0 < (n : α) :=
  Int.cast_pos.2

private theorem rat_cast_ne_zero [DivisionRing α] [CharZero α] {q : ℚ} : q ≠ 0 → (q : α) ≠ 0 :=
  Rat.cast_ne_zero.2

private theorem rat_cast_nonneg [LinearOrderedField α] {q : ℚ} : 0 ≤ q → 0 ≤ (q : α) :=
  Rat.cast_nonneg.2

private theorem rat_cast_pos [LinearOrderedField α] {q : ℚ} : 0 < q → 0 < (q : α) :=
  Rat.cast_pos.2

/-- Extension for the `positivity` tactic: casts from `ℕ`, `ℤ`, `ℚ`. -/
@[positivity]
unsafe def positivity_coe : expr → tactic strictness
  | q(@coe _ $(typ) $(inst) $(a)) => do
    -- TODO: Using `match` here might turn out too strict since we really want the instance to *unify*
      -- with one of the instances below rather than being equal on the nose.
      -- If this turns out to indeed be a problem, we should figure out the right way to pattern match
      -- up to defeq rather than equality of expressions.
      -- See also "Reflexive tactics for algebra, revisited" by Kazuhiko Sakaguchi at ITP 2022.
      match inst with
      | q(@coeToLift _ _ $(inst)) => do
        let strictness_a ← core a
        match inst, strictness_a with
          |-- `mk_mapp` is necessary in some places. Why?
            q(Nat.castCoe),
            positive p => positive <$> mk_mapp `` nat_cast_pos [typ, none, none, none, p]
          | q(Nat.castCoe), _ => nonnegative <$> mk_mapp `` Nat.cast_nonneg [typ, none, a]
          | q(Int.castCoe), positive p =>
            positive <$> mk_mapp `` int_cast_pos [typ, none, none, none, p]
          | q(Int.castCoe), nonnegative p =>
            nonnegative <$> mk_mapp `` int_cast_nonneg [typ, none, none, p]
          | q(Int.castCoe), nonzero p =>
            nonzero <$> mk_mapp `` int_cast_ne_zero [typ, none, none, none, p]
          | q(Rat.castCoe), positive p => positive <$> mk_mapp `` rat_cast_pos [typ, none, none, p]
          | q(Rat.castCoe), nonnegative p =>
            nonnegative <$> mk_mapp `` rat_cast_nonneg [typ, none, none, p]
          | q(Rat.castCoe), nonzero p =>
            nonzero <$> mk_mapp `` rat_cast_ne_zero [typ, none, none, none, p]
          | q(@coeBase _ _ Int.hasCoe), positive p => positive <$> mk_app `` int_coe_nat_pos [p]
          | q(@coeBase _ _ Int.hasCoe), _ => nonnegative <$> mk_app `` int_coe_nat_nonneg [a]
          | _, _ => failed
      | _ => failed
  | _ => failed
#align tactic.positivity_coe tactic.positivity_coe

/-- Extension for the `positivity` tactic: `nat.succ` is always positive. -/
@[positivity]
unsafe def positivity_succ : expr → tactic strictness
  | q(Nat.succ $(a)) => positive <$> mk_app `nat.succ_pos [a]
  | e => pp e >>= fail ∘ format.bracket "The expression `" "` isn't of the form `nat.succ n`"
#align tactic.positivity_succ tactic.positivity_succ

/-- Extension for the `positivity` tactic: `nat.factorial` is always positive. -/
@[positivity]
unsafe def positivity_factorial : expr → tactic strictness
  | q(Nat.factorial $(a)) => positive <$> mk_app `` Nat.factorial_pos [a]
  | e => pp e >>= fail ∘ format.bracket "The expression `" "` isn't of the form `n!`"
#align tactic.positivity_factorial tactic.positivity_factorial

/-- Extension for the `positivity` tactic: `nat.asc_factorial` is always positive. -/
@[positivity]
unsafe def positivity_asc_factorial : expr → tactic strictness
  | q(Nat.ascFactorial $(a) $(b)) => positive <$> mk_app `` Nat.ascFactorial_pos [a, b]
  | e =>
    pp e >>= fail ∘ format.bracket "The expression `" "` isn't of the form `nat.asc_factorial n k`"
#align tactic.positivity_asc_factorial tactic.positivity_asc_factorial

/-- Extension for the `positivity` tactic: nonnegative maps take nonnegative values. -/
@[positivity]
unsafe def positivity_map : expr → tactic strictness
  | expr.app q(⇑$(f)) q($(a)) => nonnegative <$> mk_app `` map_nonneg [f, a]
  | _ => failed
#align tactic.positivity_map tactic.positivity_map

end Tactic

