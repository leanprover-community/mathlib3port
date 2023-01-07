/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module tactic.interval_cases
! leanprover-community/mathlib commit 6afc9b06856ad973f6a2619e3e8a0a8d537a58f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.FinCases
import Mathbin.Data.Fin.Interval
import Mathbin.Data.Int.Interval
import Mathbin.Data.Pnat.Interval
import Mathbin.Data.Pnat.Basic

/-!
# Case bash on variables in finite intervals

This file provides the tactic `interval_cases`. `interval_cases n` will:
1. inspect hypotheses looking for lower and upper bounds of the form `a ≤ n` and `n < b`
   (in `ℕ`, `ℤ`, `ℕ+`, bounds of the form `a < n` and `n ≤ b` are also allowed),
   and also makes use of lower and upper bounds found via `le_top` and `bot_le`
   (so for example if `n : ℕ`, then the bound `0 ≤ n` is automatically found).
2. call `fin_cases` on the synthesised hypothesis `n ∈ set.Ico a b`,
   assuming an appropriate `fintype` instance can be found for the type of `n`.

The variable `n` can belong to any type `α`, with the following restrictions:
* only bounds on which `expr.to_rat` succeeds will be considered "explicit" (TODO: generalise this?)
* an instance of `decidable_eq α` is available,
* an explicit lower bound can be found among the hypotheses, or from `bot_le n`,
* an explicit upper bound can be found among the hypotheses, or from `le_top n`,
* if multiple bounds are located, an instance of `linear_order α` is available, and
* an instance of `fintype set.Ico l u` is available for the relevant bounds.

You can also explicitly specify a lower and upper bound to use, as `interval_cases using hl hu`,
where the hypotheses should be of the form `hl : a ≤ n` and `hu : n < b`. In that case,
`interval_cases` calls `fin_cases` on the resulting hypothesis `h : n ∈ set.Ico a b`.
-/


-- These imports aren't required to compile this file,
-- These imports aren't required to compile this file,
-- but they are needed at the use site for the tactic to work
-- but they are needed at the use site for the tactic to work
-- (on values of type fin/int/pnat)
-- (on values of type fin/int/pnat)
open Set

namespace Tactic

namespace IntervalCases

-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      If `e` easily implies `(%%n < %%b)`
      for some explicit `b`,
      return that proof.
      -/
    unsafe
  def
    gives_upper_bound
    ( n e : expr ) : tactic expr
    :=
      do
        let t ← infer_type e
          match
            t
            with
            | q( $ ( n' ) < $ ( b ) ) => do guard ( n = n' ) let b ← b return e
              | q( $ ( b ) > $ ( n' ) ) => do guard ( n = n' ) let b ← b return e
              |
                q( $ ( n' ) ≤ $ ( b ) )
                =>
                do
                  guard ( n = n' )
                    let b ← b
                    let tn ← infer_type n
                    match
                      tn
                      with
                      | q( ℕ ) => to_expr ` `( Nat.lt_add_one_iff . mpr $ ( e ) )
                        | q( ℕ+ ) => to_expr ` `( PNat.lt_add_one_iff . mpr $ ( e ) )
                        | q( ℤ ) => to_expr ` `( Int.lt_add_one_iff . mpr $ ( e ) )
                        | _ => failed
              |
                q( $ ( b ) ≥ $ ( n' ) )
                =>
                do
                  guard ( n = n' )
                    let b ← b
                    let tn ← infer_type n
                    match
                      tn
                      with
                      | q( ℕ ) => to_expr ` `( Nat.lt_add_one_iff . mpr $ ( e ) )
                        | q( ℕ+ ) => to_expr ` `( PNat.lt_add_one_iff . mpr $ ( e ) )
                        | q( ℤ ) => to_expr ` `( Int.lt_add_one_iff . mpr $ ( e ) )
                        | _ => failed
              | _ => failed
#align tactic.interval_cases.gives_upper_bound tactic.interval_cases.gives_upper_bound

-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      If `e` easily implies `(%%n ≥ %%b)`
      for some explicit `b`,
      return that proof.
      -/
    unsafe
  def
    gives_lower_bound
    ( n e : expr ) : tactic expr
    :=
      do
        let t ← infer_type e
          match
            t
            with
            | q( $ ( n' ) ≥ $ ( b ) ) => do guard ( n = n' ) let b ← b return e
              | q( $ ( b ) ≤ $ ( n' ) ) => do guard ( n = n' ) let b ← b return e
              |
                q( $ ( n' ) > $ ( b ) )
                =>
                do
                  guard ( n = n' )
                    let b ← b
                    let tn ← infer_type n
                    match
                      tn
                      with
                      | q( ℕ ) => to_expr ` `( Nat.add_one_le_iff . mpr $ ( e ) )
                        | q( ℕ+ ) => to_expr ` `( PNat.add_one_le_iff . mpr $ ( e ) )
                        | q( ℤ ) => to_expr ` `( Int.add_one_le_iff . mpr $ ( e ) )
                        | _ => failed
              |
                q( $ ( b ) < $ ( n' ) )
                =>
                do
                  guard ( n = n' )
                    let b ← b
                    let tn ← infer_type n
                    match
                      tn
                      with
                      | q( ℕ ) => to_expr ` `( Nat.add_one_le_iff . mpr $ ( e ) )
                        | q( ℕ+ ) => to_expr ` `( PNat.add_one_le_iff . mpr $ ( e ) )
                        | q( ℤ ) => to_expr ` `( Int.add_one_le_iff . mpr $ ( e ) )
                        | _ => failed
              | _ => failed
#align tactic.interval_cases.gives_lower_bound tactic.interval_cases.gives_lower_bound

/-- Combine two upper bounds. -/
unsafe def combine_upper_bounds : Option expr → Option expr → tactic (Option expr)
  | none, none => return none
  | some prf, none => return <| some prf
  | none, some prf => return <| some prf
  | some prf₁, some prf₂ => do
    Option.some <$> to_expr ``(lt_min $(prf₁) $(prf₂))
#align tactic.interval_cases.combine_upper_bounds tactic.interval_cases.combine_upper_bounds

/-- Combine two lower bounds. -/
unsafe def combine_lower_bounds : Option expr → Option expr → tactic (Option expr)
  | none, none => return <| none
  | some prf, none => return <| some prf
  | none, some prf => return <| some prf
  | some prf₁, some prf₂ => do
    Option.some <$> to_expr ``(max_le $(prf₂) $(prf₁))
#align tactic.interval_cases.combine_lower_bounds tactic.interval_cases.combine_lower_bounds

/-- Inspect a given expression, using it to update a set of upper and lower bounds on `n`. -/
unsafe def update_bounds (n : expr) (bounds : Option expr × Option expr) (e : expr) :
    tactic (Option expr × Option expr) := do
  let nlb ← try_core <| gives_lower_bound n e
  let nub ← try_core <| gives_upper_bound n e
  let clb ← combine_lower_bounds bounds.1 nlb
  let cub ← combine_upper_bounds bounds.2 nub
  return (clb, cub)
#align tactic.interval_cases.update_bounds tactic.interval_cases.update_bounds

-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      Attempt to find a lower bound for the variable `n`, by evaluating `bot_le n`.
      -/
    unsafe
  def
    initial_lower_bound
    ( n : expr ) : tactic expr
    :=
      do
        let e ← to_expr ` `( @ bot_le _ _ _ $ ( n ) )
          let t ← infer_type e
          match t with | q( $ ( b ) ≤ $ ( n ) ) => do return e | _ => failed
#align tactic.interval_cases.initial_lower_bound tactic.interval_cases.initial_lower_bound

-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      Attempt to find an upper bound for the variable `n`, by evaluating `le_top n`.
      -/
    unsafe
  def
    initial_upper_bound
    ( n : expr ) : tactic expr
    :=
      do
        let e ← to_expr ` `( @ le_top _ _ _ $ ( n ) )
          match
            e
            with
            |
                q( $ ( n ) ≤ $ ( b ) )
                =>
                do
                  let tn ← infer_type n
                    let
                      e
                        ←
                        match
                          tn
                          with
                          | q( ℕ ) => to_expr ` `( Nat.add_one_le_iff . mpr $ ( e ) )
                            | q( ℕ+ ) => to_expr ` `( PNat.add_one_le_iff . mpr $ ( e ) )
                            | q( ℤ ) => to_expr ` `( Int.add_one_le_iff . mpr $ ( e ) )
                            | _ => failed
                    return e
              | _ => failed
#align tactic.interval_cases.initial_upper_bound tactic.interval_cases.initial_upper_bound

/-- Inspect the local hypotheses for upper and lower bounds on a variable `n`. -/
unsafe def get_bounds (n : expr) : tactic (expr × expr) := do
  let hl ← try_core (initial_lower_bound n)
  let hu ← try_core (initial_upper_bound n)
  let lc ← local_context
  let r ← lc.mfoldl (update_bounds n) (hl, hu)
  match r with
    | (_, none) => fail "No upper bound located."
    | (none, _) => fail "No lower bound located."
    | (some lb_prf, some ub_prf) => return (lb_prf, ub_prf)
#align tactic.interval_cases.get_bounds tactic.interval_cases.get_bounds

/-- The finset of elements of a set `s` for which we have `fintype s`. -/
def setElems {α} [DecidableEq α] (s : Set α) [Fintype s] : Finset α :=
  (Fintype.elems s).image Subtype.val
#align tactic.interval_cases.set_elems Tactic.IntervalCases.setElems

/-- Each element of `s` is a member of `set_elems s`. -/
theorem mem_set_elems {α} [DecidableEq α] (s : Set α) [Fintype s] {a : α} (h : a ∈ s) :
    a ∈ setElems s :=
  Finset.mem_image.2 ⟨⟨a, h⟩, Fintype.complete _, rfl⟩
#align tactic.interval_cases.mem_set_elems Tactic.IntervalCases.mem_set_elems

end IntervalCases

open IntervalCases

/-- Call `fin_cases` on membership of the finset built from
an `Ico` interval corresponding to a lower and an upper bound.

Here `hl` should be an expression of the form `a ≤ n`, for some explicit `a`, and
`hu` should be of the form `n < b`, for some explicit `b`.

By default `interval_cases_using` automatically generates a name for the new hypothesis. The name
can be specified via the optional argument `n`.
-/
unsafe def interval_cases_using (hl hu : expr) (n : Option Name) : tactic Unit :=
  (to_expr ``(mem_set_elems (Ico _ _) ⟨$(hl), $(hu)⟩) >>=
      if hn : n.isSome then note (Option.get hn) else note_anon none) >>=
    fin_cases_at none none
#align tactic.interval_cases_using tactic.interval_cases_using

/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:38:34: unsupported: setup_tactic_parser -/
namespace Interactive

-- mathport name: parser.optional
local postfix:1024 "?" => optional

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`interval_cases n` searches for upper and lower bounds on a variable `n`,\nand if bounds are found,\nsplits into separate cases for each possible value of `n`.\n\nAs an example, in\n```\nexample (n : ℕ) (w₁ : n ≥ 3) (w₂ : n < 5) : n = 3 ∨ n = 4 :=\nbegin\n  interval_cases n,\n  all_goals {simp}\nend\n```\nafter `interval_cases n`, the goals are `3 = 3 ∨ 3 = 4` and `4 = 3 ∨ 4 = 4`.\n\nYou can also explicitly specify a lower and upper bound to use,\nas `interval_cases using hl hu`.\nThe hypotheses should be in the form `hl : a ≤ n` and `hu : n < b`,\nin which case `interval_cases` calls `fin_cases` on the resulting fact `n ∈ set.Ico a b`.\n\nYou can specify a name `h` for the new hypothesis,\nas `interval_cases n with h` or `interval_cases n using hl hu with h`.\n-/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `interval_cases [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`n]
         [":"
          (Term.app `parse [(Tactic.Interactive.Tactic.IntervalCases.parser.optional `texpr "?")])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`bounds]
         [":"
          (Term.app
           `parse
           [(Tactic.Interactive.Tactic.IntervalCases.parser.optional
             («term_*>_»
              (Term.app `tk [(str "\"using\"")])
              "*>"
              («term_<*>_» («term_<$>_» `Prod.mk "<$>" `ident) "<*>" `ident))
             "?")])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`lname]
         [":"
          (Term.app
           `parse
           [(Tactic.Interactive.Tactic.IntervalCases.parser.optional
             («term_*>_» (Term.app `tk [(str "\"with\"")]) "*>" `ident)
             "?")])]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `tactic [`Unit]))])
      (Command.declValSimple
       ":="
       (Term.do
        "do"
        (Term.doSeqIndent
         [(Term.doSeqItem
           (Term.doExpr
            (termDepIfThenElse
             "if"
             (Lean.binderIdent `h)
             ":"
             `n
             "then"
             (Term.do
              "do"
              (Term.doSeqIndent
               [(Term.doSeqItem
                 (Term.doExpr
                  («term_<|>_»
                   (Term.app `guard [`bounds])
                   "<|>"
                   (Term.app
                    `fail
                    [(str
                      "\"Do not use the `using` keyword if specifying the variable explicitly.\"")])))
                 [])
                (Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doIdDecl
                   `n
                   []
                   "←"
                   (Term.doExpr (Term.app `to_expr [(Term.app `Option.get [`h])]))))
                 [])
                (Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doPatDecl
                   (Term.tuple "(" [`hl "," [`hu]] ")")
                   "←"
                   (Term.doExpr (Term.app `get_bounds [`n]))
                   []))
                 [])
                (Term.doSeqItem
                 (Term.doExpr (Term.app `tactic.interval_cases_using [`hl `hu `lname]))
                 [])]))
             "else"
             (termDepIfThenElse
              "if"
              (Lean.binderIdent `h')
              ":"
              `bounds
              "then"
              (Term.do
               "do"
               (Term.doSeqIndent
                [(Term.doSeqItem
                  (Term.doLetArrow
                   "let"
                   []
                   (Term.doPatDecl
                    («term[_]» "[" [`hl "," `hu] "]")
                    "←"
                    (Term.doExpr
                     (Term.app
                      (Term.proj
                       («term[_]»
                        "["
                        [(Term.proj (Term.app `Option.get [`h']) "." (fieldIdx "1"))
                         ","
                         (Term.proj (Term.app `Option.get [`h']) "." (fieldIdx "2"))]
                        "]")
                       "."
                       `mmap)
                      [`get_local]))
                    []))
                  [])
                 (Term.doSeqItem
                  (Term.doExpr (Term.app `tactic.interval_cases_using [`hl `hu `lname]))
                  [])]))
              "else"
              (Term.app
               `fail
               [(«term_++_»
                 (str
                  "\"Call `interval_cases n` (specifying a variable), or `interval_cases lb ub`\\n\"")
                 "++"
                 (str "\"(specifying a lower bound and upper bound on the same variable).\""))]))))
           [])]))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doExpr
           (termDepIfThenElse
            "if"
            (Lean.binderIdent `h)
            ":"
            `n
            "then"
            (Term.do
             "do"
             (Term.doSeqIndent
              [(Term.doSeqItem
                (Term.doExpr
                 («term_<|>_»
                  (Term.app `guard [`bounds])
                  "<|>"
                  (Term.app
                   `fail
                   [(str
                     "\"Do not use the `using` keyword if specifying the variable explicitly.\"")])))
                [])
               (Term.doSeqItem
                (Term.doLetArrow
                 "let"
                 []
                 (Term.doIdDecl
                  `n
                  []
                  "←"
                  (Term.doExpr (Term.app `to_expr [(Term.app `Option.get [`h])]))))
                [])
               (Term.doSeqItem
                (Term.doLetArrow
                 "let"
                 []
                 (Term.doPatDecl
                  (Term.tuple "(" [`hl "," [`hu]] ")")
                  "←"
                  (Term.doExpr (Term.app `get_bounds [`n]))
                  []))
                [])
               (Term.doSeqItem
                (Term.doExpr (Term.app `tactic.interval_cases_using [`hl `hu `lname]))
                [])]))
            "else"
            (termDepIfThenElse
             "if"
             (Lean.binderIdent `h')
             ":"
             `bounds
             "then"
             (Term.do
              "do"
              (Term.doSeqIndent
               [(Term.doSeqItem
                 (Term.doLetArrow
                  "let"
                  []
                  (Term.doPatDecl
                   («term[_]» "[" [`hl "," `hu] "]")
                   "←"
                   (Term.doExpr
                    (Term.app
                     (Term.proj
                      («term[_]»
                       "["
                       [(Term.proj (Term.app `Option.get [`h']) "." (fieldIdx "1"))
                        ","
                        (Term.proj (Term.app `Option.get [`h']) "." (fieldIdx "2"))]
                       "]")
                      "."
                      `mmap)
                     [`get_local]))
                   []))
                 [])
                (Term.doSeqItem
                 (Term.doExpr (Term.app `tactic.interval_cases_using [`hl `hu `lname]))
                 [])]))
             "else"
             (Term.app
              `fail
              [(«term_++_»
                (str
                 "\"Call `interval_cases n` (specifying a variable), or `interval_cases lb ub`\\n\"")
                "++"
                (str "\"(specifying a lower bound and upper bound on the same variable).\""))]))))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termDepIfThenElse
       "if"
       (Lean.binderIdent `h)
       ":"
       `n
       "then"
       (Term.do
        "do"
        (Term.doSeqIndent
         [(Term.doSeqItem
           (Term.doExpr
            («term_<|>_»
             (Term.app `guard [`bounds])
             "<|>"
             (Term.app
              `fail
              [(str "\"Do not use the `using` keyword if specifying the variable explicitly.\"")])))
           [])
          (Term.doSeqItem
           (Term.doLetArrow
            "let"
            []
            (Term.doIdDecl
             `n
             []
             "←"
             (Term.doExpr (Term.app `to_expr [(Term.app `Option.get [`h])]))))
           [])
          (Term.doSeqItem
           (Term.doLetArrow
            "let"
            []
            (Term.doPatDecl
             (Term.tuple "(" [`hl "," [`hu]] ")")
             "←"
             (Term.doExpr (Term.app `get_bounds [`n]))
             []))
           [])
          (Term.doSeqItem
           (Term.doExpr (Term.app `tactic.interval_cases_using [`hl `hu `lname]))
           [])]))
       "else"
       (termDepIfThenElse
        "if"
        (Lean.binderIdent `h')
        ":"
        `bounds
        "then"
        (Term.do
         "do"
         (Term.doSeqIndent
          [(Term.doSeqItem
            (Term.doLetArrow
             "let"
             []
             (Term.doPatDecl
              («term[_]» "[" [`hl "," `hu] "]")
              "←"
              (Term.doExpr
               (Term.app
                (Term.proj
                 («term[_]»
                  "["
                  [(Term.proj (Term.app `Option.get [`h']) "." (fieldIdx "1"))
                   ","
                   (Term.proj (Term.app `Option.get [`h']) "." (fieldIdx "2"))]
                  "]")
                 "."
                 `mmap)
                [`get_local]))
              []))
            [])
           (Term.doSeqItem
            (Term.doExpr (Term.app `tactic.interval_cases_using [`hl `hu `lname]))
            [])]))
        "else"
        (Term.app
         `fail
         [(«term_++_»
           (str "\"Call `interval_cases n` (specifying a variable), or `interval_cases lb ub`\\n\"")
           "++"
           (str "\"(specifying a lower bound and upper bound on the same variable).\""))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termDepIfThenElse
       "if"
       (Lean.binderIdent `h')
       ":"
       `bounds
       "then"
       (Term.do
        "do"
        (Term.doSeqIndent
         [(Term.doSeqItem
           (Term.doLetArrow
            "let"
            []
            (Term.doPatDecl
             («term[_]» "[" [`hl "," `hu] "]")
             "←"
             (Term.doExpr
              (Term.app
               (Term.proj
                («term[_]»
                 "["
                 [(Term.proj (Term.app `Option.get [`h']) "." (fieldIdx "1"))
                  ","
                  (Term.proj (Term.app `Option.get [`h']) "." (fieldIdx "2"))]
                 "]")
                "."
                `mmap)
               [`get_local]))
             []))
           [])
          (Term.doSeqItem
           (Term.doExpr (Term.app `tactic.interval_cases_using [`hl `hu `lname]))
           [])]))
       "else"
       (Term.app
        `fail
        [(«term_++_»
          (str "\"Call `interval_cases n` (specifying a variable), or `interval_cases lb ub`\\n\"")
          "++"
          (str "\"(specifying a lower bound and upper bound on the same variable).\""))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `fail
       [(«term_++_»
         (str "\"Call `interval_cases n` (specifying a variable), or `interval_cases lb ub`\\n\"")
         "++"
         (str "\"(specifying a lower bound and upper bound on the same variable).\""))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_++_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_++_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_++_»
       (str "\"Call `interval_cases n` (specifying a variable), or `interval_cases lb ub`\\n\"")
       "++"
       (str "\"(specifying a lower bound and upper bound on the same variable).\""))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (str "\"(specifying a lower bound and upper bound on the same variable).\"")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (str "\"Call `interval_cases n` (specifying a variable), or `interval_cases lb ub`\\n\"")
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_++_»
      (str "\"Call `interval_cases n` (specifying a variable), or `interval_cases lb ub`\\n\"")
      "++"
      (str "\"(specifying a lower bound and upper bound on the same variable).\""))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fail
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doPatDecl
            («term[_]» "[" [`hl "," `hu] "]")
            "←"
            (Term.doExpr
             (Term.app
              (Term.proj
               («term[_]»
                "["
                [(Term.proj (Term.app `Option.get [`h']) "." (fieldIdx "1"))
                 ","
                 (Term.proj (Term.app `Option.get [`h']) "." (fieldIdx "2"))]
                "]")
               "."
               `mmap)
              [`get_local]))
            []))
          [])
         (Term.doSeqItem
          (Term.doExpr (Term.app `tactic.interval_cases_using [`hl `hu `lname]))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tactic.interval_cases_using [`hl `hu `lname])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lname
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hu
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic.interval_cases_using
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doPatDecl', expected 'Lean.Parser.Term.doIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app
       (Term.proj
        («term[_]»
         "["
         [(Term.proj (Term.app `Option.get [`h']) "." (fieldIdx "1"))
          ","
          (Term.proj (Term.app `Option.get [`h']) "." (fieldIdx "2"))]
         "]")
        "."
        `mmap)
       [`get_local])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `get_local
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       («term[_]»
        "["
        [(Term.proj (Term.app `Option.get [`h']) "." (fieldIdx "1"))
         ","
         (Term.proj (Term.app `Option.get [`h']) "." (fieldIdx "2"))]
        "]")
       "."
       `mmap)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term[_]»
       "["
       [(Term.proj (Term.app `Option.get [`h']) "." (fieldIdx "1"))
        ","
        (Term.proj (Term.app `Option.get [`h']) "." (fieldIdx "2"))]
       "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `Option.get [`h']) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Option.get [`h'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Option.get
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Option.get [`h']) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `Option.get [`h']) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Option.get [`h'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Option.get
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Option.get [`h']) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [`hl "," `hu] "]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hu
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `bounds
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doExpr
           («term_<|>_»
            (Term.app `guard [`bounds])
            "<|>"
            (Term.app
             `fail
             [(str "\"Do not use the `using` keyword if specifying the variable explicitly.\"")])))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doIdDecl
            `n
            []
            "←"
            (Term.doExpr (Term.app `to_expr [(Term.app `Option.get [`h])]))))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doPatDecl
            (Term.tuple "(" [`hl "," [`hu]] ")")
            "←"
            (Term.doExpr (Term.app `get_bounds [`n]))
            []))
          [])
         (Term.doSeqItem
          (Term.doExpr (Term.app `tactic.interval_cases_using [`hl `hu `lname]))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tactic.interval_cases_using [`hl `hu `lname])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lname
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hu
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tactic.interval_cases_using
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doPatDecl', expected 'Lean.Parser.Term.doIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `get_bounds [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `get_bounds
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`hl "," [`hu]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hu
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `to_expr [(Term.app `Option.get [`h])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Option.get [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Option.get
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Option.get [`h]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_expr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      («term_<|>_»
       (Term.app `guard [`bounds])
       "<|>"
       (Term.app
        `fail
        [(str "\"Do not use the `using` keyword if specifying the variable explicitly.\"")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `fail
       [(str "\"Do not use the `using` keyword if specifying the variable explicitly.\"")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'str', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'str', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (str "\"Do not use the `using` keyword if specifying the variable explicitly.\"")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fail
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 20 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      (Term.app `guard [`bounds])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `bounds
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `guard
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 1022, (some 1023, term) <=? (some 20, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 20, (some 20, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0, term) <=? (none, [anonymous])
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
      (Term.app
       `parse
       [(Tactic.Interactive.Tactic.IntervalCases.parser.optional
         («term_*>_» (Term.app `tk [(str "\"with\"")]) "*>" `ident)
         "?")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Interactive.Tactic.IntervalCases.parser.optional', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Interactive.Tactic.IntervalCases.parser.optional', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.Interactive.Tactic.IntervalCases.parser.optional
       («term_*>_» (Term.app `tk [(str "\"with\"")]) "*>" `ident)
       "?")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Interactive.Tactic.IntervalCases.parser.optional', expected 'Tactic.Interactive.Tactic.IntervalCases.parser.optional._@.Tactic.IntervalCases._hyg.13'
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
      `interval_cases n` searches for upper and lower bounds on a variable `n`,
      and if bounds are found,
      splits into separate cases for each possible value of `n`.
      
      As an example, in
      ```
      example (n : ℕ) (w₁ : n ≥ 3) (w₂ : n < 5) : n = 3 ∨ n = 4 :=
      begin
        interval_cases n,
        all_goals {simp}
      end
      ```
      after `interval_cases n`, the goals are `3 = 3 ∨ 3 = 4` and `4 = 3 ∨ 4 = 4`.
      
      You can also explicitly specify a lower and upper bound to use,
      as `interval_cases using hl hu`.
      The hypotheses should be in the form `hl : a ≤ n` and `hu : n < b`,
      in which case `interval_cases` calls `fin_cases` on the resulting fact `n ∈ set.Ico a b`.
      
      You can specify a name `h` for the new hypothesis,
      as `interval_cases n with h` or `interval_cases n using hl hu with h`.
      -/
    unsafe
  def
    interval_cases
    ( n : parse texpr ? )
        ( bounds : parse tk "using" *> Prod.mk <$> ident <*> ident ? )
        ( lname : parse tk "with" *> ident ? )
      : tactic Unit
    :=
      do
        if
          h
          :
          n
          then
          do
            guard bounds
                <|>
                fail "Do not use the `using` keyword if specifying the variable explicitly."
              let n ← to_expr Option.get h
              let ( hl , hu ) ← get_bounds n
              tactic.interval_cases_using hl hu lname
          else
          if
            h'
            :
            bounds
            then
            do
              let [ hl , hu ] ← [ Option.get h' . 1 , Option.get h' . 2 ] . mmap get_local
                tactic.interval_cases_using hl hu lname
            else
            fail
              "Call `interval_cases n` (specifying a variable), or `interval_cases lb ub`\n"
                ++
                "(specifying a lower bound and upper bound on the same variable)."
#align tactic.interactive.interval_cases tactic.interactive.interval_cases

/-- `interval_cases n` searches for upper and lower bounds on a variable `n`,
and if bounds are found,
splits into separate cases for each possible value of `n`.

As an example, in
```
example (n : ℕ) (w₁ : n ≥ 3) (w₂ : n < 5) : n = 3 ∨ n = 4 :=
begin
  interval_cases n,
  all_goals {simp}
end
```
after `interval_cases n`, the goals are `3 = 3 ∨ 3 = 4` and `4 = 3 ∨ 4 = 4`.

You can also explicitly specify a lower and upper bound to use,
as `interval_cases using hl hu`.
The hypotheses should be in the form `hl : a ≤ n` and `hu : n < b`,
in which case `interval_cases` calls `fin_cases` on the resulting fact `n ∈ set.Ico a b`.

You can also explicitly specify a name to use for the hypothesis added,
as `interval_cases n with hn` or `interval_cases n using hl hu with hn`.

In particular, `interval_cases n`
1) inspects hypotheses looking for lower and upper bounds of the form `a ≤ n` and `n < b`
   (although in `ℕ`, `ℤ`, and `ℕ+` bounds of the form `a < n` and `n ≤ b` are also allowed),
   and also makes use of lower and upper bounds found via `le_top` and `bot_le`
   (so for example if `n : ℕ`, then the bound `0 ≤ n` is found automatically), then
2) calls `fin_cases` on the synthesised hypothesis `n ∈ set.Ico a b`,
   assuming an appropriate `fintype` instance can be found for the type of `n`.

The variable `n` can belong to any type `α`, with the following restrictions:
* only bounds on which `expr.to_rat` succeeds will be considered "explicit" (TODO: generalise this?)
* an instance of `decidable_eq α` is available,
* an explicit lower bound can be found amongst the hypotheses, or from `bot_le n`,
* an explicit upper bound can be found amongst the hypotheses, or from `le_top n`,
* if multiple bounds are located, an instance of `linear_order α` is available, and
* an instance of `fintype set.Ico l u` is available for the relevant bounds.
-/
add_tactic_doc
  { Name := "interval_cases"
    category := DocCategory.tactic
    declNames := [`tactic.interactive.interval_cases]
    tags := ["case bashing"] }

end Interactive

end Tactic

