/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash

! This file was ported from Lean 3 source module algebra.lie.solvable
! leanprover-community/mathlib commit 6d0adfa76594f304b4650d098273d4366edeb61b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Lie.Abelian
import Mathbin.Algebra.Lie.IdealOperations
import Mathbin.Order.Hom.Basic

/-!
# Solvable Lie algebras

Like groups, Lie algebras admit a natural concept of solvability. We define this here via the
derived series and prove some related results. We also define the radical of a Lie algebra and
prove that it is solvable when the Lie algebra is Noetherian.

## Main definitions

  * `lie_algebra.derived_series_of_ideal`
  * `lie_algebra.derived_series`
  * `lie_algebra.is_solvable`
  * `lie_algebra.is_solvable_add`
  * `lie_algebra.radical`
  * `lie_algebra.radical_is_solvable`
  * `lie_algebra.derived_length_of_ideal`
  * `lie_algebra.derived_length`
  * `lie_algebra.derived_abelian_of_ideal`

## Tags

lie algebra, derived series, derived length, solvable, radical
-/


universe u v w w₁ w₂

variable (R : Type u) (L : Type v) (M : Type w) {L' : Type w₁}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

variable (I J : LieIdeal R L) {f : L' →ₗ⁅R⁆ L}

namespace LieAlgebra

/-- A generalisation of the derived series of a Lie algebra, whose zeroth term is a specified ideal.

It can be more convenient to work with this generalisation when considering the derived series of
an ideal since it provides a type-theoretic expression of the fact that the terms of the ideal's
derived series are also ideals of the enclosing algebra.

See also `lie_ideal.derived_series_eq_derived_series_of_ideal_comap` and
`lie_ideal.derived_series_eq_derived_series_of_ideal_map` below. -/
def derivedSeriesOfIdeal (k : ℕ) : LieIdeal R L → LieIdeal R L :=
  (fun I => ⁅I, I⁆)^[k]
#align lie_algebra.derived_series_of_ideal LieAlgebra.derivedSeriesOfIdeal

@[simp]
theorem derived_series_of_ideal_zero : derivedSeriesOfIdeal R L 0 I = I :=
  rfl
#align lie_algebra.derived_series_of_ideal_zero LieAlgebra.derived_series_of_ideal_zero

@[simp]
theorem derived_series_of_ideal_succ (k : ℕ) :
    derivedSeriesOfIdeal R L (k + 1) I =
      ⁅derivedSeriesOfIdeal R L k I, derivedSeriesOfIdeal R L k I⁆ :=
  Function.iterate_succ_apply' (fun I => ⁅I, I⁆) k I
#align lie_algebra.derived_series_of_ideal_succ LieAlgebra.derived_series_of_ideal_succ

/-- The derived series of Lie ideals of a Lie algebra. -/
abbrev derivedSeries (k : ℕ) : LieIdeal R L :=
  derivedSeriesOfIdeal R L k ⊤
#align lie_algebra.derived_series LieAlgebra.derivedSeries

theorem derived_series_def (k : ℕ) : derivedSeries R L k = derivedSeriesOfIdeal R L k ⊤ :=
  rfl
#align lie_algebra.derived_series_def LieAlgebra.derived_series_def

variable {R L}

-- mathport name: exprD
local notation "D" => derivedSeriesOfIdeal R L

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `derived_series_of_ideal_add [])
      (Command.declSig
       [(Term.explicitBinder "(" [`k `l] [":" (termℕ "ℕ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (LieAlgebra.Algebra.Lie.Solvable.termD "D") [(«term_+_» `k "+" `l) `I])
         "="
         (Term.app
          (LieAlgebra.Algebra.Lie.Solvable.termD "D")
          [`k (Term.app (LieAlgebra.Algebra.Lie.Solvable.termD "D") [`l `I])]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.induction'
            "induction'"
            [(Tactic.casesTarget [] `k)]
            []
            ["with" [(Lean.binderIdent `k) (Lean.binderIdent `ih)]]
            [])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `zero_add) "," (Tactic.rwRule [] `derived_series_of_ideal_zero)]
               "]")
              [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] (Term.app `Nat.succ_add [`k `l]))
                ","
                (Tactic.rwRule [] `derived_series_of_ideal_succ)
                ","
                (Tactic.rwRule [] `derived_series_of_ideal_succ)
                ","
                (Tactic.rwRule [] `ih)]
               "]")
              [])])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.induction'
           "induction'"
           [(Tactic.casesTarget [] `k)]
           []
           ["with" [(Lean.binderIdent `k) (Lean.binderIdent `ih)]]
           [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `zero_add) "," (Tactic.rwRule [] `derived_series_of_ideal_zero)]
              "]")
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] (Term.app `Nat.succ_add [`k `l]))
               ","
               (Tactic.rwRule [] `derived_series_of_ideal_succ)
               ","
               (Tactic.rwRule [] `derived_series_of_ideal_succ)
               ","
               (Tactic.rwRule [] `ih)]
              "]")
             [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] (Term.app `Nat.succ_add [`k `l]))
           ","
           (Tactic.rwRule [] `derived_series_of_ideal_succ)
           ","
           (Tactic.rwRule [] `derived_series_of_ideal_succ)
           ","
           (Tactic.rwRule [] `ih)]
          "]")
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] (Term.app `Nat.succ_add [`k `l]))
         ","
         (Tactic.rwRule [] `derived_series_of_ideal_succ)
         ","
         (Tactic.rwRule [] `derived_series_of_ideal_succ)
         ","
         (Tactic.rwRule [] `ih)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ih
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `derived_series_of_ideal_succ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `derived_series_of_ideal_succ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.succ_add [`k `l])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.succ_add
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `zero_add) "," (Tactic.rwRule [] `derived_series_of_ideal_zero)]
          "]")
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `zero_add) "," (Tactic.rwRule [] `derived_series_of_ideal_zero)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `derived_series_of_ideal_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.induction'
       "induction'"
       [(Tactic.casesTarget [] `k)]
       []
       ["with" [(Lean.binderIdent `k) (Lean.binderIdent `ih)]]
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app (LieAlgebra.Algebra.Lie.Solvable.termD "D") [(«term_+_» `k "+" `l) `I])
       "="
       (Term.app
        (LieAlgebra.Algebra.Lie.Solvable.termD "D")
        [`k (Term.app (LieAlgebra.Algebra.Lie.Solvable.termD "D") [`l `I])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (LieAlgebra.Algebra.Lie.Solvable.termD "D")
       [`k (Term.app (LieAlgebra.Algebra.Lie.Solvable.termD "D") [`l `I])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (LieAlgebra.Algebra.Lie.Solvable.termD "D") [`l `I])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `I
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `l
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (LieAlgebra.Algebra.Lie.Solvable.termD "D")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LieAlgebra.Algebra.Lie.Solvable.termD', expected 'LieAlgebra.Algebra.Lie.Solvable.termD._@.Algebra.Lie.Solvable._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  derived_series_of_ideal_add
  ( k l : ℕ ) : D k + l I = D k D l I
  :=
    by
      induction' k with k ih
        · rw [ zero_add , derived_series_of_ideal_zero ]
        · rw [ Nat.succ_add k l , derived_series_of_ideal_succ , derived_series_of_ideal_succ , ih ]
#align lie_algebra.derived_series_of_ideal_add LieAlgebra.derived_series_of_ideal_add

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.mono "mono" []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `derived_series_of_ideal_le [])
      (Command.declSig
       [(Term.implicitBinder "{" [`I `J] [":" (Term.app `LieIdeal [`R `L])] "}")
        (Term.implicitBinder "{" [`k `l] [":" (termℕ "ℕ")] "}")
        (Term.explicitBinder "(" [`h₁] [":" («term_≤_» `I "≤" `J)] [] ")")
        (Term.explicitBinder "(" [`h₂] [":" («term_≤_» `l "≤" `k)] [] ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         (Term.app (LieAlgebra.Algebra.Lie.Solvable.termD "D") [`k `I])
         "≤"
         (Term.app (LieAlgebra.Algebra.Lie.Solvable.termD "D") [`l `J]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.revert "revert" [`l])
           ";"
           (Tactic.«tactic_<;>_»
            (Tactic.induction'
             "induction'"
             [(Tactic.casesTarget [] `k)]
             []
             ["with" [(Lean.binderIdent `k) (Lean.binderIdent `ih)]]
             [])
            "<;>"
            (Tactic.intro "intro" [`l `h₂]))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `le_zero_iff)] "]")
              [(Tactic.location "at" (Tactic.locationHyp [`h₂] []))])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `h₂) "," (Tactic.rwRule [] `derived_series_of_ideal_zero)]
               "]")
              [])
             []
             (Tactic.exact "exact" `h₁)])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`h []]
                [(Term.typeSpec
                  ":"
                  («term_∨_» («term_=_» `l "=" `k.succ) "∨" («term_≤_» `l "≤" `k)))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Std.Tactic.tacticRwa__
                     "rwa"
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] `le_iff_eq_or_lt) "," (Tactic.rwRule [] `Nat.lt_succ_iff)]
                      "]")
                     [(Tactic.location "at" (Tactic.locationHyp [`h₂] []))])]))))))
             []
             (Tactic.cases "cases" [(Tactic.casesTarget [] `h)] [] [])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `h)
                  ","
                  (Tactic.rwRule [] `derived_series_of_ideal_succ)
                  ","
                  (Tactic.rwRule [] `derived_series_of_ideal_succ)]
                 "]")
                [])
               []
               (Tactic.exact
                "exact"
                (Term.app
                 `LieSubmodule.mono_lie
                 [(Term.hole "_")
                  (Term.hole "_")
                  (Term.hole "_")
                  (Term.hole "_")
                  (Term.app `ih [(Term.app `le_refl [`k])])
                  (Term.app `ih [(Term.app `le_refl [`k])])]))])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `derived_series_of_ideal_succ)] "]")
                [])
               []
               (Tactic.exact
                "exact"
                (Term.app
                 `le_trans
                 [(Term.app `LieSubmodule.lie_le_left [(Term.hole "_") (Term.hole "_")])
                  (Term.app `ih [`h])]))])])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.revert "revert" [`l])
          ";"
          (Tactic.«tactic_<;>_»
           (Tactic.induction'
            "induction'"
            [(Tactic.casesTarget [] `k)]
            []
            ["with" [(Lean.binderIdent `k) (Lean.binderIdent `ih)]]
            [])
           "<;>"
           (Tactic.intro "intro" [`l `h₂]))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `le_zero_iff)] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`h₂] []))])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `h₂) "," (Tactic.rwRule [] `derived_series_of_ideal_zero)]
              "]")
             [])
            []
            (Tactic.exact "exact" `h₁)])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`h []]
               [(Term.typeSpec
                 ":"
                 («term_∨_» («term_=_» `l "=" `k.succ) "∨" («term_≤_» `l "≤" `k)))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Std.Tactic.tacticRwa__
                    "rwa"
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] `le_iff_eq_or_lt) "," (Tactic.rwRule [] `Nat.lt_succ_iff)]
                     "]")
                    [(Tactic.location "at" (Tactic.locationHyp [`h₂] []))])]))))))
            []
            (Tactic.cases "cases" [(Tactic.casesTarget [] `h)] [] [])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `h)
                 ","
                 (Tactic.rwRule [] `derived_series_of_ideal_succ)
                 ","
                 (Tactic.rwRule [] `derived_series_of_ideal_succ)]
                "]")
               [])
              []
              (Tactic.exact
               "exact"
               (Term.app
                `LieSubmodule.mono_lie
                [(Term.hole "_")
                 (Term.hole "_")
                 (Term.hole "_")
                 (Term.hole "_")
                 (Term.app `ih [(Term.app `le_refl [`k])])
                 (Term.app `ih [(Term.app `le_refl [`k])])]))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `derived_series_of_ideal_succ)] "]")
               [])
              []
              (Tactic.exact
               "exact"
               (Term.app
                `le_trans
                [(Term.app `LieSubmodule.lie_le_left [(Term.hole "_") (Term.hole "_")])
                 (Term.app `ih [`h])]))])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`h []]
           [(Term.typeSpec ":" («term_∨_» («term_=_» `l "=" `k.succ) "∨" («term_≤_» `l "≤" `k)))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.tacticRwa__
                "rwa"
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `le_iff_eq_or_lt) "," (Tactic.rwRule [] `Nat.lt_succ_iff)]
                 "]")
                [(Tactic.location "at" (Tactic.locationHyp [`h₂] []))])]))))))
        []
        (Tactic.cases "cases" [(Tactic.casesTarget [] `h)] [] [])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `h)
             ","
             (Tactic.rwRule [] `derived_series_of_ideal_succ)
             ","
             (Tactic.rwRule [] `derived_series_of_ideal_succ)]
            "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            `LieSubmodule.mono_lie
            [(Term.hole "_")
             (Term.hole "_")
             (Term.hole "_")
             (Term.hole "_")
             (Term.app `ih [(Term.app `le_refl [`k])])
             (Term.app `ih [(Term.app `le_refl [`k])])]))])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `derived_series_of_ideal_succ)] "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            `le_trans
            [(Term.app `LieSubmodule.lie_le_left [(Term.hole "_") (Term.hole "_")])
             (Term.app `ih [`h])]))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `derived_series_of_ideal_succ)] "]")
         [])
        []
        (Tactic.exact
         "exact"
         (Term.app
          `le_trans
          [(Term.app `LieSubmodule.lie_le_left [(Term.hole "_") (Term.hole "_")])
           (Term.app `ih [`h])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `le_trans
        [(Term.app `LieSubmodule.lie_le_left [(Term.hole "_") (Term.hole "_")])
         (Term.app `ih [`h])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le_trans
       [(Term.app `LieSubmodule.lie_le_left [(Term.hole "_") (Term.hole "_")]) (Term.app `ih [`h])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ih [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ih
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `ih [`h]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `LieSubmodule.lie_le_left [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `LieSubmodule.lie_le_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `LieSubmodule.lie_le_left [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `derived_series_of_ideal_succ)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `derived_series_of_ideal_succ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `h)
           ","
           (Tactic.rwRule [] `derived_series_of_ideal_succ)
           ","
           (Tactic.rwRule [] `derived_series_of_ideal_succ)]
          "]")
         [])
        []
        (Tactic.exact
         "exact"
         (Term.app
          `LieSubmodule.mono_lie
          [(Term.hole "_")
           (Term.hole "_")
           (Term.hole "_")
           (Term.hole "_")
           (Term.app `ih [(Term.app `le_refl [`k])])
           (Term.app `ih [(Term.app `le_refl [`k])])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `LieSubmodule.mono_lie
        [(Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Term.app `ih [(Term.app `le_refl [`k])])
         (Term.app `ih [(Term.app `le_refl [`k])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `LieSubmodule.mono_lie
       [(Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.app `ih [(Term.app `le_refl [`k])])
        (Term.app `ih [(Term.app `le_refl [`k])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ih [(Term.app `le_refl [`k])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `le_refl [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_refl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `le_refl [`k]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ih
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `ih [(Term.paren "(" (Term.app `le_refl [`k]) ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `ih [(Term.app `le_refl [`k])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `le_refl [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_refl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `le_refl [`k]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ih
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `ih [(Term.paren "(" (Term.app `le_refl [`k]) ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `LieSubmodule.mono_lie
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `h)
         ","
         (Tactic.rwRule [] `derived_series_of_ideal_succ)
         ","
         (Tactic.rwRule [] `derived_series_of_ideal_succ)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `derived_series_of_ideal_succ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `derived_series_of_ideal_succ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases "cases" [(Tactic.casesTarget [] `h)] [] [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`h []]
         [(Term.typeSpec ":" («term_∨_» («term_=_» `l "=" `k.succ) "∨" («term_≤_» `l "≤" `k)))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Std.Tactic.tacticRwa__
              "rwa"
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `le_iff_eq_or_lt) "," (Tactic.rwRule [] `Nat.lt_succ_iff)]
               "]")
              [(Tactic.location "at" (Tactic.locationHyp [`h₂] []))])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.tacticRwa__
           "rwa"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `le_iff_eq_or_lt) "," (Tactic.rwRule [] `Nat.lt_succ_iff)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`h₂] []))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `le_iff_eq_or_lt) "," (Tactic.rwRule [] `Nat.lt_succ_iff)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`h₂] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.lt_succ_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `le_iff_eq_or_lt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∨_» («term_=_» `l "=" `k.succ) "∨" («term_≤_» `l "≤" `k))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_» `l "≤" `k)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `l
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 30 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 30, term))
      («term_=_» `l "=" `k.succ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k.succ
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `l
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 31 >? 50, (some 51, term) <=? (some 30, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 30, (some 30, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `le_zero_iff)] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`h₂] []))])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `h₂) "," (Tactic.rwRule [] `derived_series_of_ideal_zero)]
          "]")
         [])
        []
        (Tactic.exact "exact" `h₁)])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `h₁)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `h₂) "," (Tactic.rwRule [] `derived_series_of_ideal_zero)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `derived_series_of_ideal_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `le_zero_iff)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`h₂] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `le_zero_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.induction'
        "induction'"
        [(Tactic.casesTarget [] `k)]
        []
        ["with" [(Lean.binderIdent `k) (Lean.binderIdent `ih)]]
        [])
       "<;>"
       (Tactic.intro "intro" [`l `h₂]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`l `h₂])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `l
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.induction'
       "induction'"
       [(Tactic.casesTarget [] `k)]
       []
       ["with" [(Lean.binderIdent `k) (Lean.binderIdent `ih)]]
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.revert "revert" [`l])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≤_»
       (Term.app (LieAlgebra.Algebra.Lie.Solvable.termD "D") [`k `I])
       "≤"
       (Term.app (LieAlgebra.Algebra.Lie.Solvable.termD "D") [`l `J]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (LieAlgebra.Algebra.Lie.Solvable.termD "D") [`l `J])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `J
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `l
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (LieAlgebra.Algebra.Lie.Solvable.termD "D")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LieAlgebra.Algebra.Lie.Solvable.termD', expected 'LieAlgebra.Algebra.Lie.Solvable.termD._@.Algebra.Lie.Solvable._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ mono ]
  theorem
    derived_series_of_ideal_le
    { I J : LieIdeal R L } { k l : ℕ } ( h₁ : I ≤ J ) ( h₂ : l ≤ k ) : D k I ≤ D l J
    :=
      by
        revert l
          ;
          induction' k with k ih <;> intro l h₂
          · rw [ le_zero_iff ] at h₂ rw [ h₂ , derived_series_of_ideal_zero ] exact h₁
          ·
            have h : l = k.succ ∨ l ≤ k := by rwa [ le_iff_eq_or_lt , Nat.lt_succ_iff ] at h₂
              cases h
              ·
                rw [ h , derived_series_of_ideal_succ , derived_series_of_ideal_succ ]
                  exact LieSubmodule.mono_lie _ _ _ _ ih le_refl k ih le_refl k
              · rw [ derived_series_of_ideal_succ ] exact le_trans LieSubmodule.lie_le_left _ _ ih h
#align lie_algebra.derived_series_of_ideal_le LieAlgebra.derived_series_of_ideal_le

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `derived_series_of_ideal_succ_le [])
      (Command.declSig
       [(Term.explicitBinder "(" [`k] [":" (termℕ "ℕ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         (Term.app (LieAlgebra.Algebra.Lie.Solvable.termD "D") [(«term_+_» `k "+" (num "1")) `I])
         "≤"
         (Term.app (LieAlgebra.Algebra.Lie.Solvable.termD "D") [`k `I]))))
      (Command.declValSimple
       ":="
       (Term.app `derived_series_of_ideal_le [(Term.app `le_refl [`I]) (Term.proj `k "." `le_succ)])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `derived_series_of_ideal_le [(Term.app `le_refl [`I]) (Term.proj `k "." `le_succ)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `k "." `le_succ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `le_refl [`I])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `I
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_refl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `le_refl [`I]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `derived_series_of_ideal_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≤_»
       (Term.app (LieAlgebra.Algebra.Lie.Solvable.termD "D") [(«term_+_» `k "+" (num "1")) `I])
       "≤"
       (Term.app (LieAlgebra.Algebra.Lie.Solvable.termD "D") [`k `I]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (LieAlgebra.Algebra.Lie.Solvable.termD "D") [`k `I])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `I
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (LieAlgebra.Algebra.Lie.Solvable.termD "D")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LieAlgebra.Algebra.Lie.Solvable.termD', expected 'LieAlgebra.Algebra.Lie.Solvable.termD._@.Algebra.Lie.Solvable._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  derived_series_of_ideal_succ_le
  ( k : ℕ ) : D k + 1 I ≤ D k I
  := derived_series_of_ideal_le le_refl I k . le_succ
#align lie_algebra.derived_series_of_ideal_succ_le LieAlgebra.derived_series_of_ideal_succ_le

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `derived_series_of_ideal_le_self [])
      (Command.declSig
       [(Term.explicitBinder "(" [`k] [":" (termℕ "ℕ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_≤_» (Term.app (LieAlgebra.Algebra.Lie.Solvable.termD "D") [`k `I]) "≤" `I)))
      (Command.declValSimple
       ":="
       (Term.app `derived_series_of_ideal_le [(Term.app `le_refl [`I]) (Term.app `zero_le [`k])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `derived_series_of_ideal_le [(Term.app `le_refl [`I]) (Term.app `zero_le [`k])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `zero_le [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `zero_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `zero_le [`k]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `le_refl [`I])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `I
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_refl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `le_refl [`I]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `derived_series_of_ideal_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≤_» (Term.app (LieAlgebra.Algebra.Lie.Solvable.termD "D") [`k `I]) "≤" `I)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `I
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (LieAlgebra.Algebra.Lie.Solvable.termD "D") [`k `I])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `I
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (LieAlgebra.Algebra.Lie.Solvable.termD "D")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LieAlgebra.Algebra.Lie.Solvable.termD', expected 'LieAlgebra.Algebra.Lie.Solvable.termD._@.Algebra.Lie.Solvable._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  derived_series_of_ideal_le_self
  ( k : ℕ ) : D k I ≤ I
  := derived_series_of_ideal_le le_refl I zero_le k
#align lie_algebra.derived_series_of_ideal_le_self LieAlgebra.derived_series_of_ideal_le_self

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `derived_series_of_ideal_mono [])
      (Command.declSig
       [(Term.implicitBinder "{" [`I `J] [":" (Term.app `LieIdeal [`R `L])] "}")
        (Term.explicitBinder "(" [`h] [":" («term_≤_» `I "≤" `J)] [] ")")
        (Term.explicitBinder "(" [`k] [":" (termℕ "ℕ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         (Term.app (LieAlgebra.Algebra.Lie.Solvable.termD "D") [`k `I])
         "≤"
         (Term.app (LieAlgebra.Algebra.Lie.Solvable.termD "D") [`k `J]))))
      (Command.declValSimple
       ":="
       (Term.app `derived_series_of_ideal_le [`h (Term.app `le_refl [`k])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `derived_series_of_ideal_le [`h (Term.app `le_refl [`k])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `le_refl [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_refl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `le_refl [`k]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `derived_series_of_ideal_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≤_»
       (Term.app (LieAlgebra.Algebra.Lie.Solvable.termD "D") [`k `I])
       "≤"
       (Term.app (LieAlgebra.Algebra.Lie.Solvable.termD "D") [`k `J]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (LieAlgebra.Algebra.Lie.Solvable.termD "D") [`k `J])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `J
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (LieAlgebra.Algebra.Lie.Solvable.termD "D")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LieAlgebra.Algebra.Lie.Solvable.termD', expected 'LieAlgebra.Algebra.Lie.Solvable.termD._@.Algebra.Lie.Solvable._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  derived_series_of_ideal_mono
  { I J : LieIdeal R L } ( h : I ≤ J ) ( k : ℕ ) : D k I ≤ D k J
  := derived_series_of_ideal_le h le_refl k
#align lie_algebra.derived_series_of_ideal_mono LieAlgebra.derived_series_of_ideal_mono

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `derived_series_of_ideal_antitone [])
      (Command.declSig
       [(Term.implicitBinder "{" [`k `l] [":" (termℕ "ℕ")] "}")
        (Term.explicitBinder "(" [`h] [":" («term_≤_» `l "≤" `k)] [] ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         (Term.app (LieAlgebra.Algebra.Lie.Solvable.termD "D") [`k `I])
         "≤"
         (Term.app (LieAlgebra.Algebra.Lie.Solvable.termD "D") [`l `I]))))
      (Command.declValSimple
       ":="
       (Term.app `derived_series_of_ideal_le [(Term.app `le_refl [`I]) `h])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `derived_series_of_ideal_le [(Term.app `le_refl [`I]) `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `le_refl [`I])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `I
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_refl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `le_refl [`I]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `derived_series_of_ideal_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≤_»
       (Term.app (LieAlgebra.Algebra.Lie.Solvable.termD "D") [`k `I])
       "≤"
       (Term.app (LieAlgebra.Algebra.Lie.Solvable.termD "D") [`l `I]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (LieAlgebra.Algebra.Lie.Solvable.termD "D") [`l `I])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `I
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `l
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (LieAlgebra.Algebra.Lie.Solvable.termD "D")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LieAlgebra.Algebra.Lie.Solvable.termD', expected 'LieAlgebra.Algebra.Lie.Solvable.termD._@.Algebra.Lie.Solvable._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  derived_series_of_ideal_antitone
  { k l : ℕ } ( h : l ≤ k ) : D k I ≤ D l I
  := derived_series_of_ideal_le le_refl I h
#align lie_algebra.derived_series_of_ideal_antitone LieAlgebra.derived_series_of_ideal_antitone

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `derived_series_of_ideal_add_le_add [])
      (Command.declSig
       [(Term.explicitBinder "(" [`J] [":" (Term.app `LieIdeal [`R `L])] [] ")")
        (Term.explicitBinder "(" [`k `l] [":" (termℕ "ℕ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         (Term.app
          (LieAlgebra.Algebra.Lie.Solvable.termD "D")
          [(«term_+_» `k "+" `l) («term_+_» `I "+" `J)])
         "≤"
         («term_+_»
          (Term.app (LieAlgebra.Algebra.Lie.Solvable.termD "D") [`k `I])
          "+"
          (Term.app (LieAlgebra.Algebra.Lie.Solvable.termD "D") [`l `J])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `D₁
              []
              [(Term.typeSpec
                ":"
                (Order.Hom.Basic.«term_→o_»
                 (Term.app `LieIdeal [`R `L])
                 " →o "
                 (Term.app `LieIdeal [`R `L])))]
              ":="
              (Term.structInst
               "{"
               []
               [(Term.structInstField
                 (Term.structInstLVal `toFun [])
                 ":="
                 (Term.fun
                  "fun"
                  (Term.basicFun [`I] [] "=>" (Data.Bracket.«term⁅_,_⁆» "⁅" `I ", " `I "⁆"))))
                []
                (Term.structInstField
                 (Term.structInstLVal `monotone' [])
                 ":="
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`I `J `h]
                   []
                   "=>"
                   (Term.app `LieSubmodule.mono_lie [`I `J `I `J `h `h]))))]
               (Term.optEllipsis [])
               []
               "}"))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`h₁ []]
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [`I `J]
                 [(Term.typeSpec ":" (Term.app `LieIdeal [`R `L]))]
                 ","
                 («term_≤_»
                  (Term.app `D₁ [(Order.Basic.«term_⊔_» `I " ⊔ " `J)])
                  "≤"
                  (Order.Basic.«term_⊔_» (Term.app `D₁ [`I]) " ⊔ " `J))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.simp
                   "simp"
                   []
                   []
                   []
                   ["["
                    [(Tactic.simpLemma [] [] `LieSubmodule.lie_le_right)
                     ","
                     (Tactic.simpLemma [] [] `LieSubmodule.lie_le_left)
                     ","
                     (Tactic.simpLemma [] [] `le_sup_of_le_right)]
                    "]"]
                   [])]))))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `D₁.iterate_sup_le_sup_iff)]
             "]")
            [(Tactic.location "at" (Tactic.locationHyp [`h₁] []))])
           []
           (Tactic.exact "exact" (Term.app `h₁ [`k `l `I `J]))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `D₁
             []
             [(Term.typeSpec
               ":"
               (Order.Hom.Basic.«term_→o_»
                (Term.app `LieIdeal [`R `L])
                " →o "
                (Term.app `LieIdeal [`R `L])))]
             ":="
             (Term.structInst
              "{"
              []
              [(Term.structInstField
                (Term.structInstLVal `toFun [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun [`I] [] "=>" (Data.Bracket.«term⁅_,_⁆» "⁅" `I ", " `I "⁆"))))
               []
               (Term.structInstField
                (Term.structInstLVal `monotone' [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`I `J `h]
                  []
                  "=>"
                  (Term.app `LieSubmodule.mono_lie [`I `J `I `J `h `h]))))]
              (Term.optEllipsis [])
              []
              "}"))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h₁ []]
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [`I `J]
                [(Term.typeSpec ":" (Term.app `LieIdeal [`R `L]))]
                ","
                («term_≤_»
                 (Term.app `D₁ [(Order.Basic.«term_⊔_» `I " ⊔ " `J)])
                 "≤"
                 (Order.Basic.«term_⊔_» (Term.app `D₁ [`I]) " ⊔ " `J))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.simp
                  "simp"
                  []
                  []
                  []
                  ["["
                   [(Tactic.simpLemma [] [] `LieSubmodule.lie_le_right)
                    ","
                    (Tactic.simpLemma [] [] `LieSubmodule.lie_le_left)
                    ","
                    (Tactic.simpLemma [] [] `le_sup_of_le_right)]
                   "]"]
                  [])]))))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `D₁.iterate_sup_le_sup_iff)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`h₁] []))])
          []
          (Tactic.exact "exact" (Term.app `h₁ [`k `l `I `J]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `h₁ [`k `l `I `J]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h₁ [`k `l `I `J])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `J
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `I
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `l
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `D₁.iterate_sup_le_sup_iff)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`h₁] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `D₁.iterate_sup_le_sup_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`h₁ []]
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            [`I `J]
            [(Term.typeSpec ":" (Term.app `LieIdeal [`R `L]))]
            ","
            («term_≤_»
             (Term.app `D₁ [(Order.Basic.«term_⊔_» `I " ⊔ " `J)])
             "≤"
             (Order.Basic.«term_⊔_» (Term.app `D₁ [`I]) " ⊔ " `J))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.simp
              "simp"
              []
              []
              []
              ["["
               [(Tactic.simpLemma [] [] `LieSubmodule.lie_le_right)
                ","
                (Tactic.simpLemma [] [] `LieSubmodule.lie_le_left)
                ","
                (Tactic.simpLemma [] [] `le_sup_of_le_right)]
               "]"]
              [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp
           "simp"
           []
           []
           []
           ["["
            [(Tactic.simpLemma [] [] `LieSubmodule.lie_le_right)
             ","
             (Tactic.simpLemma [] [] `LieSubmodule.lie_le_left)
             ","
             (Tactic.simpLemma [] [] `le_sup_of_le_right)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpLemma [] [] `LieSubmodule.lie_le_right)
         ","
         (Tactic.simpLemma [] [] `LieSubmodule.lie_le_left)
         ","
         (Tactic.simpLemma [] [] `le_sup_of_le_right)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `le_sup_of_le_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LieSubmodule.lie_le_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LieSubmodule.lie_le_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`I `J]
       [(Term.typeSpec ":" (Term.app `LieIdeal [`R `L]))]
       ","
       («term_≤_»
        (Term.app `D₁ [(Order.Basic.«term_⊔_» `I " ⊔ " `J)])
        "≤"
        (Order.Basic.«term_⊔_» (Term.app `D₁ [`I]) " ⊔ " `J)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Term.app `D₁ [(Order.Basic.«term_⊔_» `I " ⊔ " `J)])
       "≤"
       (Order.Basic.«term_⊔_» (Term.app `D₁ [`I]) " ⊔ " `J))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.Basic.«term_⊔_» (Term.app `D₁ [`I]) " ⊔ " `J)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `J
[PrettyPrinter.parenthesize] ...precedences are 69 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 68, term))
      (Term.app `D₁ [`I])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `I
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `D₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1022, (some 1023, term) <=? (some 68, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 68, (some 69, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `D₁ [(Order.Basic.«term_⊔_» `I " ⊔ " `J)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.Basic.«term_⊔_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.Basic.«term_⊔_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.Basic.«term_⊔_» `I " ⊔ " `J)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `J
[PrettyPrinter.parenthesize] ...precedences are 69 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 68, term))
      `I
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 68, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 68, (some 69, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Order.Basic.«term_⊔_» `I " ⊔ " `J) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `D₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `LieIdeal [`R `L])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `L
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `LieIdeal
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticLet_
       "let"
       (Term.letDecl
        (Term.letIdDecl
         `D₁
         []
         [(Term.typeSpec
           ":"
           (Order.Hom.Basic.«term_→o_»
            (Term.app `LieIdeal [`R `L])
            " →o "
            (Term.app `LieIdeal [`R `L])))]
         ":="
         (Term.structInst
          "{"
          []
          [(Term.structInstField
            (Term.structInstLVal `toFun [])
            ":="
            (Term.fun
             "fun"
             (Term.basicFun [`I] [] "=>" (Data.Bracket.«term⁅_,_⁆» "⁅" `I ", " `I "⁆"))))
           []
           (Term.structInstField
            (Term.structInstLVal `monotone' [])
            ":="
            (Term.fun
             "fun"
             (Term.basicFun
              [`I `J `h]
              []
              "=>"
              (Term.app `LieSubmodule.mono_lie [`I `J `I `J `h `h]))))]
          (Term.optEllipsis [])
          []
          "}"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       []
       [(Term.structInstField
         (Term.structInstLVal `toFun [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun [`I] [] "=>" (Data.Bracket.«term⁅_,_⁆» "⁅" `I ", " `I "⁆"))))
        []
        (Term.structInstField
         (Term.structInstLVal `monotone' [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`I `J `h]
           []
           "=>"
           (Term.app `LieSubmodule.mono_lie [`I `J `I `J `h `h]))))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun [`I `J `h] [] "=>" (Term.app `LieSubmodule.mono_lie [`I `J `I `J `h `h])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `LieSubmodule.mono_lie [`I `J `I `J `h `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `J
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `I
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `J
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `I
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `LieSubmodule.mono_lie
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `J
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `I
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`I] [] "=>" (Data.Bracket.«term⁅_,_⁆» "⁅" `I ", " `I "⁆")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Bracket.«term⁅_,_⁆» "⁅" `I ", " `I "⁆")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `I
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `I
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `I
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.Hom.Basic.«term_→o_» (Term.app `LieIdeal [`R `L]) " →o " (Term.app `LieIdeal [`R `L]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `LieIdeal [`R `L])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `L
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `LieIdeal
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app `LieIdeal [`R `L])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `L
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `LieIdeal
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 26 >? 1022, (some 1023, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≤_»
       (Term.app
        (LieAlgebra.Algebra.Lie.Solvable.termD "D")
        [(«term_+_» `k "+" `l) («term_+_» `I "+" `J)])
       "≤"
       («term_+_»
        (Term.app (LieAlgebra.Algebra.Lie.Solvable.termD "D") [`k `I])
        "+"
        (Term.app (LieAlgebra.Algebra.Lie.Solvable.termD "D") [`l `J])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       (Term.app (LieAlgebra.Algebra.Lie.Solvable.termD "D") [`k `I])
       "+"
       (Term.app (LieAlgebra.Algebra.Lie.Solvable.termD "D") [`l `J]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (LieAlgebra.Algebra.Lie.Solvable.termD "D") [`l `J])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `J
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `l
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (LieAlgebra.Algebra.Lie.Solvable.termD "D")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'LieAlgebra.Algebra.Lie.Solvable.termD', expected 'LieAlgebra.Algebra.Lie.Solvable.termD._@.Algebra.Lie.Solvable._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  derived_series_of_ideal_add_le_add
  ( J : LieIdeal R L ) ( k l : ℕ ) : D k + l I + J ≤ D k I + D l J
  :=
    by
      let
          D₁
            : LieIdeal R L →o LieIdeal R L
            :=
            {
              toFun := fun I => ⁅ I , I ⁆
                monotone' := fun I J h => LieSubmodule.mono_lie I J I J h h
              }
        have
          h₁
            : ∀ I J : LieIdeal R L , D₁ I ⊔ J ≤ D₁ I ⊔ J
            :=
            by simp [ LieSubmodule.lie_le_right , LieSubmodule.lie_le_left , le_sup_of_le_right ]
        rw [ ← D₁.iterate_sup_le_sup_iff ] at h₁
        exact h₁ k l I J
#align lie_algebra.derived_series_of_ideal_add_le_add LieAlgebra.derived_series_of_ideal_add_le_add

theorem derived_series_of_bot_eq_bot (k : ℕ) : derivedSeriesOfIdeal R L k ⊥ = ⊥ :=
  by
  rw [eq_bot_iff]
  exact derived_series_of_ideal_le_self ⊥ k
#align lie_algebra.derived_series_of_bot_eq_bot LieAlgebra.derived_series_of_bot_eq_bot

theorem abelian_iff_derived_one_eq_bot : IsLieAbelian I ↔ derivedSeriesOfIdeal R L 1 I = ⊥ := by
  rw [derived_series_of_ideal_succ, derived_series_of_ideal_zero,
    LieSubmodule.lie_abelian_iff_lie_self_eq_bot]
#align lie_algebra.abelian_iff_derived_one_eq_bot LieAlgebra.abelian_iff_derived_one_eq_bot

theorem abelian_iff_derived_succ_eq_bot (I : LieIdeal R L) (k : ℕ) :
    IsLieAbelian (derivedSeriesOfIdeal R L k I) ↔ derivedSeriesOfIdeal R L (k + 1) I = ⊥ := by
  rw [add_comm, derived_series_of_ideal_add I 1 k, abelian_iff_derived_one_eq_bot]
#align lie_algebra.abelian_iff_derived_succ_eq_bot LieAlgebra.abelian_iff_derived_succ_eq_bot

end LieAlgebra

namespace LieIdeal

open LieAlgebra

variable {R L}

theorem derived_series_eq_derived_series_of_ideal_comap (k : ℕ) :
    derivedSeries R I k = (derivedSeriesOfIdeal R L k I).comap I.incl :=
  by
  induction' k with k ih
  · simp only [derived_series_def, comap_incl_self, derived_series_of_ideal_zero]
  · simp only [derived_series_def, derived_series_of_ideal_succ] at ih⊢
    rw [ih]
    exact
      comap_bracket_incl_of_le I (derived_series_of_ideal_le_self I k)
        (derived_series_of_ideal_le_self I k)
#align
  lie_ideal.derived_series_eq_derived_series_of_ideal_comap LieIdeal.derived_series_eq_derived_series_of_ideal_comap

theorem derived_series_eq_derived_series_of_ideal_map (k : ℕ) :
    (derivedSeries R I k).map I.incl = derivedSeriesOfIdeal R L k I :=
  by
  rw [derived_series_eq_derived_series_of_ideal_comap, map_comap_incl, inf_eq_right]
  apply derived_series_of_ideal_le_self
#align
  lie_ideal.derived_series_eq_derived_series_of_ideal_map LieIdeal.derived_series_eq_derived_series_of_ideal_map

theorem derived_series_eq_bot_iff (k : ℕ) :
    derivedSeries R I k = ⊥ ↔ derivedSeriesOfIdeal R L k I = ⊥ := by
  rw [← derived_series_eq_derived_series_of_ideal_map, map_eq_bot_iff, ker_incl, eq_bot_iff]
#align lie_ideal.derived_series_eq_bot_iff LieIdeal.derived_series_eq_bot_iff

theorem derived_series_add_eq_bot {k l : ℕ} {I J : LieIdeal R L} (hI : derivedSeries R I k = ⊥)
    (hJ : derivedSeries R J l = ⊥) : derivedSeries R (↥(I + J)) (k + l) = ⊥ :=
  by
  rw [LieIdeal.derived_series_eq_bot_iff] at hI hJ⊢
  rw [← le_bot_iff]
  let D := derived_series_of_ideal R L; change D k I = ⊥ at hI; change D l J = ⊥ at hJ
  calc
    D (k + l) (I + J) ≤ D k I + D l J := derived_series_of_ideal_add_le_add I J k l
    _ ≤ ⊥ := by
      rw [hI, hJ]
      simp
    
#align lie_ideal.derived_series_add_eq_bot LieIdeal.derived_series_add_eq_bot

theorem derived_series_map_le (k : ℕ) : (derivedSeries R L' k).map f ≤ derivedSeries R L k :=
  by
  induction' k with k ih
  · simp only [derived_series_def, derived_series_of_ideal_zero, le_top]
  · simp only [derived_series_def, derived_series_of_ideal_succ] at ih⊢
    exact le_trans (map_bracket_le f) (LieSubmodule.mono_lie _ _ _ _ ih ih)
#align lie_ideal.derived_series_map_le LieIdeal.derived_series_map_le

theorem derived_series_map_eq (k : ℕ) (h : Function.Surjective f) :
    (derivedSeries R L' k).map f = derivedSeries R L k :=
  by
  induction' k with k ih
  · change (⊤ : LieIdeal R L').map f = ⊤
    rw [← f.ideal_range_eq_map]
    exact f.ideal_range_eq_top_of_surjective h
  · simp only [derived_series_def, map_bracket_eq f h, ih, derived_series_of_ideal_succ]
#align lie_ideal.derived_series_map_eq LieIdeal.derived_series_map_eq

end LieIdeal

namespace LieAlgebra

/-- A Lie algebra is solvable if its derived series reaches 0 (in a finite number of steps). -/
class IsSolvable : Prop where
  solvable : ∃ k, derivedSeries R L k = ⊥
#align lie_algebra.is_solvable LieAlgebra.IsSolvable

instance isSolvableBot : IsSolvable R ↥(⊥ : LieIdeal R L) :=
  ⟨⟨0, Subsingleton.elim _ ⊥⟩⟩
#align lie_algebra.is_solvable_bot LieAlgebra.isSolvableBot

instance isSolvableAdd {I J : LieIdeal R L} [hI : IsSolvable R I] [hJ : IsSolvable R J] :
    IsSolvable R ↥(I + J) := by
  obtain ⟨k, hk⟩ := id hI; obtain ⟨l, hl⟩ := id hJ
  exact ⟨⟨k + l, LieIdeal.derived_series_add_eq_bot hk hl⟩⟩
#align lie_algebra.is_solvable_add LieAlgebra.isSolvableAdd

end LieAlgebra

variable {R L}

namespace Function

open LieAlgebra

theorem Injective.lieAlgebraIsSolvable [h₁ : IsSolvable R L] (h₂ : Injective f) : IsSolvable R L' :=
  by
  obtain ⟨k, hk⟩ := id h₁
  use k
  apply LieIdeal.bot_of_map_eq_bot h₂; rw [eq_bot_iff, ← hk]
  apply LieIdeal.derived_series_map_le
#align function.injective.lie_algebra_is_solvable Function.Injective.lieAlgebraIsSolvable

theorem Surjective.lieAlgebraIsSolvable [h₁ : IsSolvable R L'] (h₂ : Surjective f) :
    IsSolvable R L := by
  obtain ⟨k, hk⟩ := id h₁
  use k
  rw [← LieIdeal.derived_series_map_eq k h₂, hk]
  simp only [LieIdeal.map_eq_bot_iff, bot_le]
#align function.surjective.lie_algebra_is_solvable Function.Surjective.lieAlgebraIsSolvable

end Function

theorem LieHom.isSolvableRange (f : L' →ₗ⁅R⁆ L) [h : LieAlgebra.IsSolvable R L'] :
    LieAlgebra.IsSolvable R f.range :=
  f.surjective_range_restrict.lieAlgebraIsSolvable
#align lie_hom.is_solvable_range LieHom.isSolvableRange

namespace LieAlgebra

theorem solvable_iff_equiv_solvable (e : L' ≃ₗ⁅R⁆ L) : IsSolvable R L' ↔ IsSolvable R L :=
  by
  constructor <;> intro h
  · exact e.symm.injective.lie_algebra_is_solvable
  · exact e.injective.lie_algebra_is_solvable
#align lie_algebra.solvable_iff_equiv_solvable LieAlgebra.solvable_iff_equiv_solvable

theorem leSolvableIdealSolvable {I J : LieIdeal R L} (h₁ : I ≤ J) (h₂ : IsSolvable R J) :
    IsSolvable R I :=
  (LieIdeal.hom_of_le_injective h₁).lieAlgebraIsSolvable
#align lie_algebra.le_solvable_ideal_solvable LieAlgebra.leSolvableIdealSolvable

variable (R L)

instance (priority := 100) ofAbelianIsSolvable [IsLieAbelian L] : IsSolvable R L :=
  by
  use 1
  rw [← abelian_iff_derived_one_eq_bot, lie_abelian_iff_equiv_lie_abelian LieIdeal.topEquiv]
  infer_instance
#align lie_algebra.of_abelian_is_solvable LieAlgebra.ofAbelianIsSolvable

/-- The (solvable) radical of Lie algebra is the `Sup` of all solvable ideals. -/
def radical :=
  supₛ { I : LieIdeal R L | IsSolvable R I }
#align lie_algebra.radical LieAlgebra.radical

/-- The radical of a Noetherian Lie algebra is solvable. -/
instance radicalIsSolvable [IsNoetherian R L] : IsSolvable R (radical R L) :=
  by
  have hwf := LieSubmodule.well_founded_of_noetherian R L L
  rw [← CompleteLattice.is_sup_closed_compact_iff_well_founded] at hwf
  refine' hwf { I : LieIdeal R L | is_solvable R I } ⟨⊥, _⟩ fun I hI J hJ => _
  · exact LieAlgebra.isSolvableBot R L
  · apply LieAlgebra.isSolvableAdd R L
    exacts[hI, hJ]
#align lie_algebra.radical_is_solvable LieAlgebra.radicalIsSolvable

/-- The `→` direction of this lemma is actually true without the `is_noetherian` assumption. -/
theorem LieIdeal.solvable_iff_le_radical [IsNoetherian R L] (I : LieIdeal R L) :
    IsSolvable R I ↔ I ≤ radical R L :=
  ⟨fun h => le_supₛ h, fun h => leSolvableIdealSolvable h inferInstance⟩
#align lie_algebra.lie_ideal.solvable_iff_le_radical LieAlgebra.LieIdeal.solvable_iff_le_radical

theorem center_le_radical : center R L ≤ radical R L :=
  have h : IsSolvable R (center R L) := by infer_instance
  le_supₛ h
#align lie_algebra.center_le_radical LieAlgebra.center_le_radical

/-- Given a solvable Lie ideal `I` with derived series `I = D₀ ≥ D₁ ≥ ⋯ ≥ Dₖ = ⊥`, this is the
natural number `k` (the number of inclusions).

For a non-solvable ideal, the value is 0. -/
noncomputable def derivedLengthOfIdeal (I : LieIdeal R L) : ℕ :=
  infₛ { k | derivedSeriesOfIdeal R L k I = ⊥ }
#align lie_algebra.derived_length_of_ideal LieAlgebra.derivedLengthOfIdeal

/-- The derived length of a Lie algebra is the derived length of its 'top' Lie ideal.

See also `lie_algebra.derived_length_eq_derived_length_of_ideal`. -/
noncomputable abbrev derivedLength : ℕ :=
  derivedLengthOfIdeal R L ⊤
#align lie_algebra.derived_length LieAlgebra.derivedLength

theorem derived_series_of_derived_length_succ (I : LieIdeal R L) (k : ℕ) :
    derivedLengthOfIdeal R L I = k + 1 ↔
      IsLieAbelian (derivedSeriesOfIdeal R L k I) ∧ derivedSeriesOfIdeal R L k I ≠ ⊥ :=
  by
  rw [abelian_iff_derived_succ_eq_bot]
  let s := { k | derived_series_of_ideal R L k I = ⊥ }
  change Inf s = k + 1 ↔ k + 1 ∈ s ∧ k ∉ s
  have hs : ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ → k₁ ∈ s → k₂ ∈ s :=
    by
    intro k₁ k₂ h₁₂ h₁
    suffices derived_series_of_ideal R L k₂ I ≤ ⊥ by exact eq_bot_iff.mpr this
    change derived_series_of_ideal R L k₁ I = ⊥ at h₁
    rw [← h₁]
    exact derived_series_of_ideal_antitone I h₁₂
  exact Nat.Inf_upward_closed_eq_succ_iff hs k
#align
  lie_algebra.derived_series_of_derived_length_succ LieAlgebra.derived_series_of_derived_length_succ

theorem derived_length_eq_derived_length_of_ideal (I : LieIdeal R L) :
    derivedLength R I = derivedLengthOfIdeal R L I :=
  by
  let s₁ := { k | derived_series R I k = ⊥ }
  let s₂ := { k | derived_series_of_ideal R L k I = ⊥ }
  change Inf s₁ = Inf s₂
  congr ; ext k; exact I.derived_series_eq_bot_iff k
#align
  lie_algebra.derived_length_eq_derived_length_of_ideal LieAlgebra.derived_length_eq_derived_length_of_ideal

variable {R L}

/-- Given a solvable Lie ideal `I` with derived series `I = D₀ ≥ D₁ ≥ ⋯ ≥ Dₖ = ⊥`, this is the
`k-1`th term in the derived series (and is therefore an Abelian ideal contained in `I`).

For a non-solvable ideal, this is the zero ideal, `⊥`. -/
noncomputable def derivedAbelianOfIdeal (I : LieIdeal R L) : LieIdeal R L :=
  match derivedLengthOfIdeal R L I with
  | 0 => ⊥
  | k + 1 => derivedSeriesOfIdeal R L k I
#align lie_algebra.derived_abelian_of_ideal LieAlgebra.derivedAbelianOfIdeal

theorem abelian_derived_abelian_of_ideal (I : LieIdeal R L) :
    IsLieAbelian (derivedAbelianOfIdeal I) :=
  by
  dsimp only [derived_abelian_of_ideal]
  cases' h : derived_length_of_ideal R L I with k
  · exact is_lie_abelian_bot R L
  · rw [derived_series_of_derived_length_succ] at h
    exact h.1
#align lie_algebra.abelian_derived_abelian_of_ideal LieAlgebra.abelian_derived_abelian_of_ideal

theorem derived_length_zero (I : LieIdeal R L) [hI : IsSolvable R I] :
    derivedLengthOfIdeal R L I = 0 ↔ I = ⊥ :=
  by
  let s := { k | derived_series_of_ideal R L k I = ⊥ }
  change Inf s = 0 ↔ _
  have hne : s ≠ ∅ := by
    obtain ⟨k, hk⟩ := id hI
    refine' Set.Nonempty.ne_empty ⟨k, _⟩
    rw [derived_series_def, LieIdeal.derived_series_eq_bot_iff] at hk
    exact hk
  simp [hne]
#align lie_algebra.derived_length_zero LieAlgebra.derived_length_zero

theorem abelian_of_solvable_ideal_eq_bot_iff (I : LieIdeal R L) [h : IsSolvable R I] :
    derivedAbelianOfIdeal I = ⊥ ↔ I = ⊥ :=
  by
  dsimp only [derived_abelian_of_ideal]
  cases' h : derived_length_of_ideal R L I with k
  · rw [derived_length_zero] at h
    rw [h]
    rfl
  · obtain ⟨h₁, h₂⟩ := (derived_series_of_derived_length_succ R L I k).mp h
    have h₃ : I ≠ ⊥ := by
      intro contra
      apply h₂
      rw [contra]
      apply derived_series_of_bot_eq_bot
    change derived_series_of_ideal R L k I = ⊥ ↔ I = ⊥
    constructor <;> contradiction
#align
  lie_algebra.abelian_of_solvable_ideal_eq_bot_iff LieAlgebra.abelian_of_solvable_ideal_eq_bot_iff

end LieAlgebra

