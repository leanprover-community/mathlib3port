/-
Copyright (c) 2020 Patrick Stevens. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Stevens

! This file was ported from Lean 3 source module number_theory.primorial
! leanprover-community/mathlib commit 6afc9b06856ad973f6a2619e3e8a0a8d537a58f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Associated
import Mathbin.Data.Nat.Choose.Sum
import Mathbin.Data.Nat.Parity
import Mathbin.Tactic.RingExp

/-!
# Primorial

This file defines the primorial function (the product of primes less than or equal to some bound),
and proves that `primorial n ≤ 4 ^ n`.

## Notations

We use the local notation `n#` for the primorial of `n`: that is, the product of the primes less
than or equal to `n`.
-/


open Finset

open Nat

open BigOperators Nat

/-- The primorial `n#` of `n` is the product of the primes less than or equal to `n`.
-/
def primorial (n : ℕ) : ℕ :=
  ∏ p in filter Nat.Prime (range (n + 1)), p
#align primorial primorial

-- mathport name: «expr #»
local notation x "#" => primorial x

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `primorial_succ [])
      (Command.declSig
       [(Term.implicitBinder "{" [`n] [":" (termℕ "ℕ")] "}")
        (Term.explicitBinder "(" [`n_big] [":" («term_<_» (num "1") "<" `n)] [] ")")
        (Term.explicitBinder
         "("
         [`r]
         [":" («term_=_» («term_%_» `n "%" (num "2")) "=" (num "1"))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (NumberTheory.Primorial.«term_#» («term_+_» `n "+" (num "1")) "#")
         "="
         (NumberTheory.Primorial.«term_#» `n "#"))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.app
             `prod_congr
             [(Term.hole "_")
              (Term.fun "fun" (Term.basicFun [(Term.hole "_") (Term.hole "_")] [] "=>" `rfl))]))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `range_succ)
              ","
              (Tactic.rwRule [] `filter_insert)
              ","
              (Tactic.rwRule
               []
               (Term.app `if_neg [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))]))]
             "]")
            [])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`two_dvd []]
              [(Term.typeSpec ":" («term_∣_» (num "2") "∣" («term_+_» `n "+" (num "1"))))]
              ":="
              (Term.app
               `dvd_iff_mod_eq_zero.mpr
               [(Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mod_add_mod)
                       ","
                       (Tactic.rwRule [] `r)
                       ","
                       (Tactic.rwRule [] `mod_self)]
                      "]")
                     [])])))]))))
           []
           (linarith
            "linarith"
            []
            (linarithArgsRest
             []
             []
             ["["
              [(Term.app
                (Term.proj
                 (Term.app `h.dvd_iff_eq [(Term.app `Nat.bit0_ne_one [(num "1")])])
                 "."
                 `mp)
                [`two_dvd])]
              "]"]))])))
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
         [(Tactic.refine'
           "refine'"
           (Term.app
            `prod_congr
            [(Term.hole "_")
             (Term.fun "fun" (Term.basicFun [(Term.hole "_") (Term.hole "_")] [] "=>" `rfl))]))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `range_succ)
             ","
             (Tactic.rwRule [] `filter_insert)
             ","
             (Tactic.rwRule
              []
              (Term.app `if_neg [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))]))]
            "]")
           [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`two_dvd []]
             [(Term.typeSpec ":" («term_∣_» (num "2") "∣" («term_+_» `n "+" (num "1"))))]
             ":="
             (Term.app
              `dvd_iff_mod_eq_zero.mpr
              [(Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mod_add_mod)
                      ","
                      (Tactic.rwRule [] `r)
                      ","
                      (Tactic.rwRule [] `mod_self)]
                     "]")
                    [])])))]))))
          []
          (linarith
           "linarith"
           []
           (linarithArgsRest
            []
            []
            ["["
             [(Term.app
               (Term.proj
                (Term.app `h.dvd_iff_eq [(Term.app `Nat.bit0_ne_one [(num "1")])])
                "."
                `mp)
               [`two_dvd])]
             "]"]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (linarith
       "linarith"
       []
       (linarithArgsRest
        []
        []
        ["["
         [(Term.app
           (Term.proj (Term.app `h.dvd_iff_eq [(Term.app `Nat.bit0_ne_one [(num "1")])]) "." `mp)
           [`two_dvd])]
         "]"]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `h.dvd_iff_eq [(Term.app `Nat.bit0_ne_one [(num "1")])]) "." `mp)
       [`two_dvd])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `two_dvd
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `h.dvd_iff_eq [(Term.app `Nat.bit0_ne_one [(num "1")])]) "." `mp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `h.dvd_iff_eq [(Term.app `Nat.bit0_ne_one [(num "1")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.bit0_ne_one [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.bit0_ne_one
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Nat.bit0_ne_one [(num "1")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h.dvd_iff_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `h.dvd_iff_eq [(Term.paren "(" (Term.app `Nat.bit0_ne_one [(num "1")]) ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`two_dvd []]
         [(Term.typeSpec ":" («term_∣_» (num "2") "∣" («term_+_» `n "+" (num "1"))))]
         ":="
         (Term.app
          `dvd_iff_mod_eq_zero.mpr
          [(Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mod_add_mod)
                  ","
                  (Tactic.rwRule [] `r)
                  ","
                  (Tactic.rwRule [] `mod_self)]
                 "]")
                [])])))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `dvd_iff_mod_eq_zero.mpr
       [(Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mod_add_mod)
               ","
               (Tactic.rwRule [] `r)
               ","
               (Tactic.rwRule [] `mod_self)]
              "]")
             [])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mod_add_mod)
             ","
             (Tactic.rwRule [] `r)
             ","
             (Tactic.rwRule [] `mod_self)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mod_add_mod)
         ","
         (Tactic.rwRule [] `r)
         ","
         (Tactic.rwRule [] `mod_self)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mod_self
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mod_add_mod
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mod_add_mod)
            ","
            (Tactic.rwRule [] `r)
            ","
            (Tactic.rwRule [] `mod_self)]
           "]")
          [])])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dvd_iff_mod_eq_zero.mpr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∣_» (num "2") "∣" («term_+_» `n "+" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `range_succ)
         ","
         (Tactic.rwRule [] `filter_insert)
         ","
         (Tactic.rwRule
          []
          (Term.app `if_neg [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `if_neg [(Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `if_neg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `filter_insert
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `range_succ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `prod_congr
        [(Term.hole "_")
         (Term.fun "fun" (Term.basicFun [(Term.hole "_") (Term.hole "_")] [] "=>" `rfl))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `prod_congr
       [(Term.hole "_")
        (Term.fun "fun" (Term.basicFun [(Term.hole "_") (Term.hole "_")] [] "=>" `rfl))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [(Term.hole "_") (Term.hole "_")] [] "=>" `rfl))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `prod_congr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (NumberTheory.Primorial.«term_#» («term_+_» `n "+" (num "1")) "#")
       "="
       (NumberTheory.Primorial.«term_#» `n "#"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.Primorial.«term_#» `n "#")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Primorial.«term_#»', expected 'NumberTheory.Primorial.term_#._@.NumberTheory.Primorial._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  primorial_succ
  { n : ℕ } ( n_big : 1 < n ) ( r : n % 2 = 1 ) : n + 1 # = n #
  :=
    by
      refine' prod_congr _ fun _ _ => rfl
        rw [ range_succ , filter_insert , if_neg fun h => _ ]
        have two_dvd : 2 ∣ n + 1 := dvd_iff_mod_eq_zero.mpr by rw [ ← mod_add_mod , r , mod_self ]
        linarith [ h.dvd_iff_eq Nat.bit0_ne_one 1 . mp two_dvd ]
#align primorial_succ primorial_succ

theorem dvd_choose_of_middling_prime (p : ℕ) (is_prime : Nat.Prime p) (m : ℕ) (p_big : m + 1 < p)
    (p_small : p ≤ 2 * m + 1) : p ∣ choose (2 * m + 1) (m + 1) :=
  by
  have m_size : m + 1 ≤ 2 * m + 1 := le_of_lt (lt_of_lt_of_le p_big p_small)
  have s : ¬p ∣ (m + 1)! := by
    intro p_div_fact
    exact lt_le_antisymm p_big (is_prime.dvd_factorial.mp p_div_fact)
  have t : ¬p ∣ (2 * m + 1 - (m + 1))! := by
    intro p_div_fact
    refine' lt_le_antisymm (lt_of_succ_lt p_big) _
    convert is_prime.dvd_factorial.mp p_div_fact
    rw [two_mul, add_assoc, Nat.add_sub_cancel]
  have expanded : choose (2 * m + 1) (m + 1) * (m + 1)! * (2 * m + 1 - (m + 1))! = (2 * m + 1)! :=
    @choose_mul_factorial_mul_factorial (2 * m + 1) (m + 1) m_size
  have p_div_big_fact : p ∣ (2 * m + 1)! := (prime.dvd_factorial is_prime).mpr p_small
  rw [← expanded, mul_assoc] at p_div_big_fact
  obtain p_div_choose | p_div_facts : p ∣ choose (2 * m + 1) (m + 1) ∨ p ∣ _ ! * _ ! :=
    (prime.dvd_mul is_prime).1 p_div_big_fact
  · exact p_div_choose
  cases (prime.dvd_mul is_prime).1 p_div_facts
  exacts[(s h).elim, (t h).elim]
#align dvd_choose_of_middling_prime dvd_choose_of_middling_prime

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `primorial_le_4_pow [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.forall
         "∀"
         [`n]
         [(Term.typeSpec ":" (termℕ "ℕ"))]
         ","
         («term_≤_» (NumberTheory.Primorial.«term_#» `n "#") "≤" («term_^_» (num "4") "^" `n)))))
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt "|" [[(num "0")]] "=>" `le_rfl)
          (Term.matchAlt "|" [[(num "1")]] "=>" (Term.app `le_of_inf_eq [`rfl]))
          (Term.matchAlt
           "|"
           [[(«term_+_» `n "+" (num "2"))]]
           "=>"
           (Term.match
            "match"
            []
            []
            [(Term.matchDiscr
              []
              (Term.app `Nat.mod_two_eq_zero_or_one [(«term_+_» `n "+" (num "1"))]))]
            "with"
            (Term.matchAlts
             [(Term.matchAlt
               "|"
               [[(Term.app `Or.inl [`n_odd])]]
               "=>"
               (Term.match
                "match"
                []
                []
                [(Term.matchDiscr
                  []
                  (Term.app (Term.proj `Nat.even_iff "." (fieldIdx "2")) [`n_odd]))]
                "with"
                (Term.matchAlts
                 [(Term.matchAlt
                   "|"
                   [[(Term.anonymousCtor "⟨" [`m "," `twice_m] "⟩")]]
                   "=>"
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Tactic.tacticHave_
                        "have"
                        (Term.haveDecl
                         (Term.haveIdDecl
                          [`recurse []]
                          [(Term.typeSpec
                            ":"
                            («term_<_»
                             («term_+_» `m "+" (num "1"))
                             "<"
                             («term_+_» `n "+" (num "2"))))]
                          ":="
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(linarith "linarith" [] (linarithArgsRest [] [] []))]))))))
                       []
                       (calcTactic
                        "calc"
                        (calcStep
                         («term_=_»
                          (NumberTheory.Primorial.«term_#» («term_+_» `n "+" (num "2")) "#")
                          "="
                          (BigOperators.Algebra.BigOperators.Basic.finset.prod
                           "∏"
                           (Std.ExtendedBinder.extBinders
                            (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                           " in "
                           (Term.app
                            `filter
                            [`Nat.Prime
                             (Term.app
                              `range
                              [(«term_+_» («term_*_» (num "2") "*" `m) "+" (num "2"))])])
                           ", "
                           `i))
                         ":="
                         (Term.byTactic
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented
                            [(Std.Tactic.Simpa.simpa
                              "simpa"
                              []
                              []
                              (Std.Tactic.Simpa.simpaArgsRest
                               []
                               []
                               []
                               [(Tactic.simpArgs
                                 "["
                                 [(Tactic.simpLemma [] [] `two_mul)
                                  ","
                                  (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `twice_m)]
                                 "]")]
                               []))]))))
                        [(calcStep
                          («term_=_»
                           (Term.hole "_")
                           "="
                           (BigOperators.Algebra.BigOperators.Basic.finset.prod
                            "∏"
                            (Std.ExtendedBinder.extBinders
                             (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                            " in "
                            (Term.app
                             `filter
                             [`Nat.Prime
                              («term_∪_»
                               (Term.app
                                `Finset.ico
                                [(«term_+_» `m "+" (num "2"))
                                 («term_+_» («term_*_» (num "2") "*" `m) "+" (num "2"))])
                               "∪"
                               (Term.app `range [(«term_+_» `m "+" (num "2"))]))])
                            ", "
                            `i))
                          ":="
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(Tactic.rwSeq
                               "rw"
                               []
                               (Tactic.rwRuleSeq
                                "["
                                [(Tactic.rwRule [] `range_eq_Ico)
                                 ","
                                 (Tactic.rwRule [] `Finset.union_comm)
                                 ","
                                 (Tactic.rwRule [] `Finset.Ico_union_Ico_eq_Ico)]
                                "]")
                               [])
                              []
                              (tactic__
                               (cdotTk (patternIgnore (token.«· » "·")))
                               [(Tactic.exact "exact" `bot_le)])
                              []
                              (tactic__
                               (cdotTk (patternIgnore (token.«· » "·")))
                               [(Std.Tactic.Simpa.simpa
                                 "simpa"
                                 []
                                 []
                                 (Std.Tactic.Simpa.simpaArgsRest
                                  []
                                  []
                                  ["only"]
                                  [(Tactic.simpArgs
                                    "["
                                    [(Tactic.simpLemma [] [] `add_le_add_iff_right)
                                     ","
                                     (Tactic.simpLemma [] [] `two_mul)]
                                    "]")]
                                  ["using" (Term.app `Nat.le_add_left [`m `m])]))])]))))
                         (calcStep
                          («term_=_»
                           (Term.hole "_")
                           "="
                           (BigOperators.Algebra.BigOperators.Basic.finset.prod
                            "∏"
                            (Std.ExtendedBinder.extBinders
                             (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                            " in "
                            («term_∪_»
                             (Term.app
                              `filter
                              [`Nat.Prime
                               (Term.app
                                `Finset.ico
                                [(«term_+_» `m "+" (num "2"))
                                 («term_+_» («term_*_» (num "2") "*" `m) "+" (num "2"))])])
                             "∪"
                             (Term.app
                              `filter
                              [`Nat.Prime (Term.app `range [(«term_+_» `m "+" (num "2"))])]))
                            ", "
                            `i))
                          ":="
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(Tactic.rwSeq
                               "rw"
                               []
                               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `filter_union)] "]")
                               [])]))))
                         (calcStep
                          («term_=_»
                           (Term.hole "_")
                           "="
                           («term_*_»
                            (BigOperators.Algebra.BigOperators.Basic.finset.prod
                             "∏"
                             (Std.ExtendedBinder.extBinders
                              (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                             " in "
                             (Term.app
                              `filter
                              [`Nat.Prime
                               (Term.app
                                `Finset.ico
                                [(«term_+_» `m "+" (num "2"))
                                 («term_+_» («term_*_» (num "2") "*" `m) "+" (num "2"))])])
                             ", "
                             `i)
                            "*"
                            (BigOperators.Algebra.BigOperators.Basic.finset.prod
                             "∏"
                             (Std.ExtendedBinder.extBinders
                              (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                             " in "
                             (Term.app
                              `filter
                              [`Nat.Prime (Term.app `range [(«term_+_» `m "+" (num "2"))])])
                             ", "
                             `i)))
                          ":="
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(Tactic.apply "apply" `Finset.prod_union)
                              []
                              (Tactic.tacticHave_
                               "have"
                               (Term.haveDecl
                                (Term.haveIdDecl
                                 [`disj []]
                                 [(Term.typeSpec
                                   ":"
                                   (Term.app
                                    `Disjoint
                                    [(Term.app
                                      `Finset.ico
                                      [(«term_+_» `m "+" (num "2"))
                                       («term_+_» («term_*_» (num "2") "*" `m) "+" (num "2"))])
                                     (Term.app `range [(«term_+_» `m "+" (num "2"))])]))]
                                 ":="
                                 (Term.byTactic
                                  "by"
                                  (Tactic.tacticSeq
                                   (Tactic.tacticSeq1Indented
                                    [(Tactic.simp
                                      "simp"
                                      []
                                      []
                                      ["only"]
                                      ["["
                                       [(Tactic.simpLemma [] [] `Finset.disjoint_left)
                                        ","
                                        (Tactic.simpLemma [] [] `and_imp)
                                        ","
                                        (Tactic.simpLemma [] [] `Finset.mem_Ico)
                                        ","
                                        (Tactic.simpLemma [] [] `not_lt)
                                        ","
                                        (Tactic.simpLemma [] [] `Finset.mem_range)]
                                       "]"]
                                      [])
                                     []
                                     (Tactic.intro "intro" [(Term.hole "_") `pr (Term.hole "_")])
                                     []
                                     (Tactic.exact "exact" `pr)]))))))
                              []
                              (Tactic.exact
                               "exact"
                               (Term.app `Finset.disjoint_filter_filter [`disj]))]))))
                         (calcStep
                          («term_≤_»
                           (Term.hole "_")
                           "≤"
                           («term_*_»
                            (BigOperators.Algebra.BigOperators.Basic.finset.prod
                             "∏"
                             (Std.ExtendedBinder.extBinders
                              (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                             " in "
                             (Term.app
                              `filter
                              [`Nat.Prime
                               (Term.app
                                `Finset.ico
                                [(«term_+_» `m "+" (num "2"))
                                 («term_+_» («term_*_» (num "2") "*" `m) "+" (num "2"))])])
                             ", "
                             `i)
                            "*"
                            («term_^_» (num "4") "^" («term_+_» `m "+" (num "1")))))
                          ":="
                          (Term.app
                           `Nat.mul_le_mul_left
                           [(Term.hole "_")
                            (Term.app `primorial_le_4_pow [(«term_+_» `m "+" (num "1"))])]))
                         (calcStep
                          («term_≤_»
                           (Term.hole "_")
                           "≤"
                           («term_*_»
                            (Term.app
                             `choose
                             [(«term_+_» («term_*_» (num "2") "*" `m) "+" (num "1"))
                              («term_+_» `m "+" (num "1"))])
                            "*"
                            («term_^_» (num "4") "^" («term_+_» `m "+" (num "1")))))
                          ":="
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(Tactic.tacticHave_
                               "have"
                               (Term.haveDecl
                                (Term.haveIdDecl
                                 [`s []]
                                 [(Term.typeSpec
                                   ":"
                                   («term_∣_»
                                    (BigOperators.Algebra.BigOperators.Basic.finset.prod
                                     "∏"
                                     (Std.ExtendedBinder.extBinders
                                      (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                                     " in "
                                     (Term.app
                                      `filter
                                      [`Nat.Prime
                                       (Term.app
                                        `Finset.ico
                                        [(«term_+_» `m "+" (num "2"))
                                         («term_+_» («term_*_» (num "2") "*" `m) "+" (num "2"))])])
                                     ", "
                                     `i)
                                    "∣"
                                    (Term.app
                                     `choose
                                     [(«term_+_» («term_*_» (num "2") "*" `m) "+" (num "1"))
                                      («term_+_» `m "+" (num "1"))])))]
                                 ":="
                                 (Term.byTactic
                                  "by"
                                  (Tactic.tacticSeq
                                   (Tactic.tacticSeq1Indented
                                    [(Tactic.refine'
                                      "refine'"
                                      (Term.app
                                       `prod_primes_dvd
                                       [(Term.app
                                         `choose
                                         [(«term_+_» («term_*_» (num "2") "*" `m) "+" (num "1"))
                                          («term_+_» `m "+" (num "1"))])
                                        (Term.hole "_")
                                        (Term.hole "_")]))
                                     []
                                     (tactic__
                                      (cdotTk (patternIgnore (token.«· » "·")))
                                      [(Tactic.intro "intro" [`a])
                                       []
                                       (Tactic.rwSeq
                                        "rw"
                                        []
                                        (Tactic.rwRuleSeq
                                         "["
                                         [(Tactic.rwRule [] `Finset.mem_filter)
                                          ","
                                          (Tactic.rwRule [] `Nat.prime_iff)]
                                         "]")
                                        [])
                                       []
                                       (Tactic.apply "apply" `And.right)])
                                     []
                                     (tactic__
                                      (cdotTk (patternIgnore (token.«· » "·")))
                                      [(Tactic.intro "intro" [`a])
                                       []
                                       (Tactic.rwSeq
                                        "rw"
                                        []
                                        (Tactic.rwRuleSeq
                                         "["
                                         [(Tactic.rwRule [] `Finset.mem_filter)]
                                         "]")
                                        [])
                                       []
                                       (Tactic.intro "intro" [`pr])
                                       []
                                       (Std.Tactic.rcases
                                        "rcases"
                                        [(Tactic.casesTarget [] `pr)]
                                        ["with"
                                         (Std.Tactic.RCases.rcasesPatLo
                                          (Std.Tactic.RCases.rcasesPatMed
                                           [(Std.Tactic.RCases.rcasesPat.tuple
                                             "⟨"
                                             [(Std.Tactic.RCases.rcasesPatLo
                                               (Std.Tactic.RCases.rcasesPatMed
                                                [(Std.Tactic.RCases.rcasesPat.one `size)])
                                               [])
                                              ","
                                              (Std.Tactic.RCases.rcasesPatLo
                                               (Std.Tactic.RCases.rcasesPatMed
                                                [(Std.Tactic.RCases.rcasesPat.one `is_prime)])
                                               [])]
                                             "⟩")])
                                          [])])
                                       []
                                       (Tactic.simp
                                        "simp"
                                        []
                                        []
                                        ["only"]
                                        ["[" [(Tactic.simpLemma [] [] `Finset.mem_Ico)] "]"]
                                        [(Tactic.location "at" (Tactic.locationHyp [`size] []))])
                                       []
                                       (Std.Tactic.rcases
                                        "rcases"
                                        [(Tactic.casesTarget [] `size)]
                                        ["with"
                                         (Std.Tactic.RCases.rcasesPatLo
                                          (Std.Tactic.RCases.rcasesPatMed
                                           [(Std.Tactic.RCases.rcasesPat.tuple
                                             "⟨"
                                             [(Std.Tactic.RCases.rcasesPatLo
                                               (Std.Tactic.RCases.rcasesPatMed
                                                [(Std.Tactic.RCases.rcasesPat.one `a_big)])
                                               [])
                                              ","
                                              (Std.Tactic.RCases.rcasesPatLo
                                               (Std.Tactic.RCases.rcasesPatMed
                                                [(Std.Tactic.RCases.rcasesPat.one `a_small)])
                                               [])]
                                             "⟩")])
                                          [])])
                                       []
                                       (Tactic.exact
                                        "exact"
                                        (Term.app
                                         `dvd_choose_of_middling_prime
                                         [`a
                                          `is_prime
                                          `m
                                          `a_big
                                          (Term.app `nat.lt_succ_iff.mp [`a_small])]))])]))))))
                              []
                              (Tactic.tacticHave_
                               "have"
                               (Term.haveDecl
                                (Term.haveIdDecl
                                 [`r []]
                                 [(Term.typeSpec
                                   ":"
                                   («term_≤_»
                                    (BigOperators.Algebra.BigOperators.Basic.finset.prod
                                     "∏"
                                     (Std.ExtendedBinder.extBinders
                                      (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                                     " in "
                                     (Term.app
                                      `filter
                                      [`Nat.Prime
                                       (Term.app
                                        `Finset.ico
                                        [(«term_+_» `m "+" (num "2"))
                                         («term_+_» («term_*_» (num "2") "*" `m) "+" (num "2"))])])
                                     ", "
                                     `i)
                                    "≤"
                                    (Term.app
                                     `choose
                                     [(«term_+_» («term_*_» (num "2") "*" `m) "+" (num "1"))
                                      («term_+_» `m "+" (num "1"))])))]
                                 ":="
                                 (Term.byTactic
                                  "by"
                                  (Tactic.tacticSeq
                                   (Tactic.tacticSeq1Indented
                                    [(Tactic.refine'
                                      "refine'"
                                      (Term.app
                                       (Term.explicit "@" `Nat.le_of_dvd)
                                       [(Term.hole "_") (Term.hole "_") (Term.hole "_") `s]))
                                     []
                                     (Tactic.exact
                                      "exact"
                                      (Term.app
                                       (Term.explicit "@" `choose_pos)
                                       [(«term_+_» («term_*_» (num "2") "*" `m) "+" (num "1"))
                                        («term_+_» `m "+" (num "1"))
                                        (Term.byTactic
                                         "by"
                                         (Tactic.tacticSeq
                                          (Tactic.tacticSeq1Indented
                                           [(linarith
                                             "linarith"
                                             []
                                             (linarithArgsRest [] [] []))])))]))]))))))
                              []
                              (Tactic.exact
                               "exact"
                               (Term.app `Nat.mul_le_mul_right [(Term.hole "_") `r]))]))))
                         (calcStep
                          («term_=_»
                           (Term.hole "_")
                           "="
                           («term_*_»
                            (Term.app
                             `choose
                             [(«term_+_» («term_*_» (num "2") "*" `m) "+" (num "1")) `m])
                            "*"
                            («term_^_» (num "4") "^" («term_+_» `m "+" (num "1")))))
                          ":="
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(Tactic.rwSeq
                               "rw"
                               []
                               (Tactic.rwRuleSeq
                                "["
                                [(Tactic.rwRule [] (Term.app `choose_symm_half [`m]))]
                                "]")
                               [])]))))
                         (calcStep
                          («term_≤_»
                           (Term.hole "_")
                           "≤"
                           («term_*_»
                            («term_^_» (num "4") "^" `m)
                            "*"
                            («term_^_» (num "4") "^" («term_+_» `m "+" (num "1")))))
                          ":="
                          (Term.app
                           `Nat.mul_le_mul_right
                           [(Term.hole "_") (Term.app `choose_middle_le_pow [`m])]))
                         (calcStep
                          («term_=_»
                           (Term.hole "_")
                           "="
                           («term_^_»
                            (num "4")
                            "^"
                            («term_+_» («term_*_» (num "2") "*" `m) "+" (num "1"))))
                          ":="
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented [(Mathlib.Tactic.RingNF.ring "ring")]))))
                         (calcStep
                          («term_=_»
                           (Term.hole "_")
                           "="
                           («term_^_» (num "4") "^" («term_+_» `n "+" (num "2"))))
                          ":="
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(Tactic.rwSeq
                               "rw"
                               []
                               (Tactic.rwRuleSeq
                                "["
                                [(Tactic.rwRule [] `two_mul)
                                 ","
                                 (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `twice_m)]
                                "]")
                               [])]))))])]))))])))
              (Term.matchAlt
               "|"
               [[(Term.app `Or.inr [`n_even])]]
               "=>"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Std.Tactic.obtain
                    "obtain"
                    [(Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.one `one_lt_n)
                       "|"
                       (Std.Tactic.RCases.rcasesPat.one `n_le_one)])]
                    [":"
                     («term_∨_»
                      («term_<_» (num "1") "<" («term_+_» `n "+" (num "1")))
                      "∨"
                      («term_≤_» («term_+_» `n "+" (num "1")) "≤" (num "1")))]
                    [":=" [(Term.app `lt_or_le [(num "1") («term_+_» `n "+" (num "1"))])]])
                   []
                   (tactic__
                    (cdotTk (patternIgnore (token.«· » "·")))
                    [(Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [] (Term.app `primorial_succ [`one_lt_n `n_even]))]
                       "]")
                      [])
                     []
                     (calcTactic
                      "calc"
                      (calcStep
                       («term_≤_»
                        (NumberTheory.Primorial.«term_#» («term_+_» `n "+" (num "1")) "#")
                        "≤"
                        («term_^_» (num "4") "^" `n.succ))
                       ":="
                       (Term.app `primorial_le_4_pow [(«term_+_» `n "+" (num "1"))]))
                      [(calcStep
                        («term_≤_»
                         (Term.hole "_")
                         "≤"
                         («term_^_» (num "4") "^" («term_+_» `n "+" (num "2"))))
                        ":="
                        (Term.app
                         `pow_le_pow
                         [(Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
                          (Term.app `Nat.le_succ [(Term.hole "_")])]))])])
                   []
                   (tactic__
                    (cdotTk (patternIgnore (token.«· » "·")))
                    [(Tactic.tacticHave_
                      "have"
                      (Term.haveDecl
                       (Term.haveIdDecl
                        [`n_zero []]
                        [(Term.typeSpec ":" («term_=_» `n "=" (num "0")))]
                        ":="
                        (Term.app
                         (Term.proj `eq_bot_iff "." (fieldIdx "2"))
                         [(Term.app
                           (Term.proj `succ_le_succ_iff "." (fieldIdx "1"))
                           [`n_le_one])]))))
                     []
                     (Mathlib.Tactic.normNum
                      "norm_num"
                      []
                      [(Tactic.simpArgs
                        "["
                        [(Tactic.simpLemma [] [] `n_zero)
                         ","
                         (Tactic.simpLemma [] [] `primorial)
                         ","
                         (Tactic.simpLemma [] [] `range_succ)
                         ","
                         (Tactic.simpLemma [] [] `prod_filter)
                         ","
                         (Tactic.simpLemma [] [] `Nat.not_prime_zero)
                         ","
                         (Tactic.simpLemma [] [] `Nat.prime_two)]
                        "]")]
                      [])])]))))])))])
        []))
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.match
       "match"
       []
       []
       [(Term.matchDiscr [] (Term.app `Nat.mod_two_eq_zero_or_one [(«term_+_» `n "+" (num "1"))]))]
       "with"
       (Term.matchAlts
        [(Term.matchAlt
          "|"
          [[(Term.app `Or.inl [`n_odd])]]
          "=>"
          (Term.match
           "match"
           []
           []
           [(Term.matchDiscr [] (Term.app (Term.proj `Nat.even_iff "." (fieldIdx "2")) [`n_odd]))]
           "with"
           (Term.matchAlts
            [(Term.matchAlt
              "|"
              [[(Term.anonymousCtor "⟨" [`m "," `twice_m] "⟩")]]
              "=>"
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`recurse []]
                     [(Term.typeSpec
                       ":"
                       («term_<_» («term_+_» `m "+" (num "1")) "<" («term_+_» `n "+" (num "2"))))]
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(linarith "linarith" [] (linarithArgsRest [] [] []))]))))))
                  []
                  (calcTactic
                   "calc"
                   (calcStep
                    («term_=_»
                     (NumberTheory.Primorial.«term_#» («term_+_» `n "+" (num "2")) "#")
                     "="
                     (BigOperators.Algebra.BigOperators.Basic.finset.prod
                      "∏"
                      (Std.ExtendedBinder.extBinders
                       (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                      " in "
                      (Term.app
                       `filter
                       [`Nat.Prime
                        (Term.app `range [(«term_+_» («term_*_» (num "2") "*" `m) "+" (num "2"))])])
                      ", "
                      `i))
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Std.Tactic.Simpa.simpa
                         "simpa"
                         []
                         []
                         (Std.Tactic.Simpa.simpaArgsRest
                          []
                          []
                          []
                          [(Tactic.simpArgs
                            "["
                            [(Tactic.simpLemma [] [] `two_mul)
                             ","
                             (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `twice_m)]
                            "]")]
                          []))]))))
                   [(calcStep
                     («term_=_»
                      (Term.hole "_")
                      "="
                      (BigOperators.Algebra.BigOperators.Basic.finset.prod
                       "∏"
                       (Std.ExtendedBinder.extBinders
                        (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                       " in "
                       (Term.app
                        `filter
                        [`Nat.Prime
                         («term_∪_»
                          (Term.app
                           `Finset.ico
                           [(«term_+_» `m "+" (num "2"))
                            («term_+_» («term_*_» (num "2") "*" `m) "+" (num "2"))])
                          "∪"
                          (Term.app `range [(«term_+_» `m "+" (num "2"))]))])
                       ", "
                       `i))
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.rwSeq
                          "rw"
                          []
                          (Tactic.rwRuleSeq
                           "["
                           [(Tactic.rwRule [] `range_eq_Ico)
                            ","
                            (Tactic.rwRule [] `Finset.union_comm)
                            ","
                            (Tactic.rwRule [] `Finset.Ico_union_Ico_eq_Ico)]
                           "]")
                          [])
                         []
                         (tactic__
                          (cdotTk (patternIgnore (token.«· » "·")))
                          [(Tactic.exact "exact" `bot_le)])
                         []
                         (tactic__
                          (cdotTk (patternIgnore (token.«· » "·")))
                          [(Std.Tactic.Simpa.simpa
                            "simpa"
                            []
                            []
                            (Std.Tactic.Simpa.simpaArgsRest
                             []
                             []
                             ["only"]
                             [(Tactic.simpArgs
                               "["
                               [(Tactic.simpLemma [] [] `add_le_add_iff_right)
                                ","
                                (Tactic.simpLemma [] [] `two_mul)]
                               "]")]
                             ["using" (Term.app `Nat.le_add_left [`m `m])]))])]))))
                    (calcStep
                     («term_=_»
                      (Term.hole "_")
                      "="
                      (BigOperators.Algebra.BigOperators.Basic.finset.prod
                       "∏"
                       (Std.ExtendedBinder.extBinders
                        (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                       " in "
                       («term_∪_»
                        (Term.app
                         `filter
                         [`Nat.Prime
                          (Term.app
                           `Finset.ico
                           [(«term_+_» `m "+" (num "2"))
                            («term_+_» («term_*_» (num "2") "*" `m) "+" (num "2"))])])
                        "∪"
                        (Term.app
                         `filter
                         [`Nat.Prime (Term.app `range [(«term_+_» `m "+" (num "2"))])]))
                       ", "
                       `i))
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.rwSeq
                          "rw"
                          []
                          (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `filter_union)] "]")
                          [])]))))
                    (calcStep
                     («term_=_»
                      (Term.hole "_")
                      "="
                      («term_*_»
                       (BigOperators.Algebra.BigOperators.Basic.finset.prod
                        "∏"
                        (Std.ExtendedBinder.extBinders
                         (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                        " in "
                        (Term.app
                         `filter
                         [`Nat.Prime
                          (Term.app
                           `Finset.ico
                           [(«term_+_» `m "+" (num "2"))
                            («term_+_» («term_*_» (num "2") "*" `m) "+" (num "2"))])])
                        ", "
                        `i)
                       "*"
                       (BigOperators.Algebra.BigOperators.Basic.finset.prod
                        "∏"
                        (Std.ExtendedBinder.extBinders
                         (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                        " in "
                        (Term.app
                         `filter
                         [`Nat.Prime (Term.app `range [(«term_+_» `m "+" (num "2"))])])
                        ", "
                        `i)))
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.apply "apply" `Finset.prod_union)
                         []
                         (Tactic.tacticHave_
                          "have"
                          (Term.haveDecl
                           (Term.haveIdDecl
                            [`disj []]
                            [(Term.typeSpec
                              ":"
                              (Term.app
                               `Disjoint
                               [(Term.app
                                 `Finset.ico
                                 [(«term_+_» `m "+" (num "2"))
                                  («term_+_» («term_*_» (num "2") "*" `m) "+" (num "2"))])
                                (Term.app `range [(«term_+_» `m "+" (num "2"))])]))]
                            ":="
                            (Term.byTactic
                             "by"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(Tactic.simp
                                 "simp"
                                 []
                                 []
                                 ["only"]
                                 ["["
                                  [(Tactic.simpLemma [] [] `Finset.disjoint_left)
                                   ","
                                   (Tactic.simpLemma [] [] `and_imp)
                                   ","
                                   (Tactic.simpLemma [] [] `Finset.mem_Ico)
                                   ","
                                   (Tactic.simpLemma [] [] `not_lt)
                                   ","
                                   (Tactic.simpLemma [] [] `Finset.mem_range)]
                                  "]"]
                                 [])
                                []
                                (Tactic.intro "intro" [(Term.hole "_") `pr (Term.hole "_")])
                                []
                                (Tactic.exact "exact" `pr)]))))))
                         []
                         (Tactic.exact
                          "exact"
                          (Term.app `Finset.disjoint_filter_filter [`disj]))]))))
                    (calcStep
                     («term_≤_»
                      (Term.hole "_")
                      "≤"
                      («term_*_»
                       (BigOperators.Algebra.BigOperators.Basic.finset.prod
                        "∏"
                        (Std.ExtendedBinder.extBinders
                         (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                        " in "
                        (Term.app
                         `filter
                         [`Nat.Prime
                          (Term.app
                           `Finset.ico
                           [(«term_+_» `m "+" (num "2"))
                            («term_+_» («term_*_» (num "2") "*" `m) "+" (num "2"))])])
                        ", "
                        `i)
                       "*"
                       («term_^_» (num "4") "^" («term_+_» `m "+" (num "1")))))
                     ":="
                     (Term.app
                      `Nat.mul_le_mul_left
                      [(Term.hole "_")
                       (Term.app `primorial_le_4_pow [(«term_+_» `m "+" (num "1"))])]))
                    (calcStep
                     («term_≤_»
                      (Term.hole "_")
                      "≤"
                      («term_*_»
                       (Term.app
                        `choose
                        [(«term_+_» («term_*_» (num "2") "*" `m) "+" (num "1"))
                         («term_+_» `m "+" (num "1"))])
                       "*"
                       («term_^_» (num "4") "^" («term_+_» `m "+" (num "1")))))
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.tacticHave_
                          "have"
                          (Term.haveDecl
                           (Term.haveIdDecl
                            [`s []]
                            [(Term.typeSpec
                              ":"
                              («term_∣_»
                               (BigOperators.Algebra.BigOperators.Basic.finset.prod
                                "∏"
                                (Std.ExtendedBinder.extBinders
                                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                                " in "
                                (Term.app
                                 `filter
                                 [`Nat.Prime
                                  (Term.app
                                   `Finset.ico
                                   [(«term_+_» `m "+" (num "2"))
                                    («term_+_» («term_*_» (num "2") "*" `m) "+" (num "2"))])])
                                ", "
                                `i)
                               "∣"
                               (Term.app
                                `choose
                                [(«term_+_» («term_*_» (num "2") "*" `m) "+" (num "1"))
                                 («term_+_» `m "+" (num "1"))])))]
                            ":="
                            (Term.byTactic
                             "by"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(Tactic.refine'
                                 "refine'"
                                 (Term.app
                                  `prod_primes_dvd
                                  [(Term.app
                                    `choose
                                    [(«term_+_» («term_*_» (num "2") "*" `m) "+" (num "1"))
                                     («term_+_» `m "+" (num "1"))])
                                   (Term.hole "_")
                                   (Term.hole "_")]))
                                []
                                (tactic__
                                 (cdotTk (patternIgnore (token.«· » "·")))
                                 [(Tactic.intro "intro" [`a])
                                  []
                                  (Tactic.rwSeq
                                   "rw"
                                   []
                                   (Tactic.rwRuleSeq
                                    "["
                                    [(Tactic.rwRule [] `Finset.mem_filter)
                                     ","
                                     (Tactic.rwRule [] `Nat.prime_iff)]
                                    "]")
                                   [])
                                  []
                                  (Tactic.apply "apply" `And.right)])
                                []
                                (tactic__
                                 (cdotTk (patternIgnore (token.«· » "·")))
                                 [(Tactic.intro "intro" [`a])
                                  []
                                  (Tactic.rwSeq
                                   "rw"
                                   []
                                   (Tactic.rwRuleSeq
                                    "["
                                    [(Tactic.rwRule [] `Finset.mem_filter)]
                                    "]")
                                   [])
                                  []
                                  (Tactic.intro "intro" [`pr])
                                  []
                                  (Std.Tactic.rcases
                                   "rcases"
                                   [(Tactic.casesTarget [] `pr)]
                                   ["with"
                                    (Std.Tactic.RCases.rcasesPatLo
                                     (Std.Tactic.RCases.rcasesPatMed
                                      [(Std.Tactic.RCases.rcasesPat.tuple
                                        "⟨"
                                        [(Std.Tactic.RCases.rcasesPatLo
                                          (Std.Tactic.RCases.rcasesPatMed
                                           [(Std.Tactic.RCases.rcasesPat.one `size)])
                                          [])
                                         ","
                                         (Std.Tactic.RCases.rcasesPatLo
                                          (Std.Tactic.RCases.rcasesPatMed
                                           [(Std.Tactic.RCases.rcasesPat.one `is_prime)])
                                          [])]
                                        "⟩")])
                                     [])])
                                  []
                                  (Tactic.simp
                                   "simp"
                                   []
                                   []
                                   ["only"]
                                   ["[" [(Tactic.simpLemma [] [] `Finset.mem_Ico)] "]"]
                                   [(Tactic.location "at" (Tactic.locationHyp [`size] []))])
                                  []
                                  (Std.Tactic.rcases
                                   "rcases"
                                   [(Tactic.casesTarget [] `size)]
                                   ["with"
                                    (Std.Tactic.RCases.rcasesPatLo
                                     (Std.Tactic.RCases.rcasesPatMed
                                      [(Std.Tactic.RCases.rcasesPat.tuple
                                        "⟨"
                                        [(Std.Tactic.RCases.rcasesPatLo
                                          (Std.Tactic.RCases.rcasesPatMed
                                           [(Std.Tactic.RCases.rcasesPat.one `a_big)])
                                          [])
                                         ","
                                         (Std.Tactic.RCases.rcasesPatLo
                                          (Std.Tactic.RCases.rcasesPatMed
                                           [(Std.Tactic.RCases.rcasesPat.one `a_small)])
                                          [])]
                                        "⟩")])
                                     [])])
                                  []
                                  (Tactic.exact
                                   "exact"
                                   (Term.app
                                    `dvd_choose_of_middling_prime
                                    [`a
                                     `is_prime
                                     `m
                                     `a_big
                                     (Term.app `nat.lt_succ_iff.mp [`a_small])]))])]))))))
                         []
                         (Tactic.tacticHave_
                          "have"
                          (Term.haveDecl
                           (Term.haveIdDecl
                            [`r []]
                            [(Term.typeSpec
                              ":"
                              («term_≤_»
                               (BigOperators.Algebra.BigOperators.Basic.finset.prod
                                "∏"
                                (Std.ExtendedBinder.extBinders
                                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                                " in "
                                (Term.app
                                 `filter
                                 [`Nat.Prime
                                  (Term.app
                                   `Finset.ico
                                   [(«term_+_» `m "+" (num "2"))
                                    («term_+_» («term_*_» (num "2") "*" `m) "+" (num "2"))])])
                                ", "
                                `i)
                               "≤"
                               (Term.app
                                `choose
                                [(«term_+_» («term_*_» (num "2") "*" `m) "+" (num "1"))
                                 («term_+_» `m "+" (num "1"))])))]
                            ":="
                            (Term.byTactic
                             "by"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(Tactic.refine'
                                 "refine'"
                                 (Term.app
                                  (Term.explicit "@" `Nat.le_of_dvd)
                                  [(Term.hole "_") (Term.hole "_") (Term.hole "_") `s]))
                                []
                                (Tactic.exact
                                 "exact"
                                 (Term.app
                                  (Term.explicit "@" `choose_pos)
                                  [(«term_+_» («term_*_» (num "2") "*" `m) "+" (num "1"))
                                   («term_+_» `m "+" (num "1"))
                                   (Term.byTactic
                                    "by"
                                    (Tactic.tacticSeq
                                     (Tactic.tacticSeq1Indented
                                      [(linarith
                                        "linarith"
                                        []
                                        (linarithArgsRest [] [] []))])))]))]))))))
                         []
                         (Tactic.exact
                          "exact"
                          (Term.app `Nat.mul_le_mul_right [(Term.hole "_") `r]))]))))
                    (calcStep
                     («term_=_»
                      (Term.hole "_")
                      "="
                      («term_*_»
                       (Term.app
                        `choose
                        [(«term_+_» («term_*_» (num "2") "*" `m) "+" (num "1")) `m])
                       "*"
                       («term_^_» (num "4") "^" («term_+_» `m "+" (num "1")))))
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.rwSeq
                          "rw"
                          []
                          (Tactic.rwRuleSeq
                           "["
                           [(Tactic.rwRule [] (Term.app `choose_symm_half [`m]))]
                           "]")
                          [])]))))
                    (calcStep
                     («term_≤_»
                      (Term.hole "_")
                      "≤"
                      («term_*_»
                       («term_^_» (num "4") "^" `m)
                       "*"
                       («term_^_» (num "4") "^" («term_+_» `m "+" (num "1")))))
                     ":="
                     (Term.app
                      `Nat.mul_le_mul_right
                      [(Term.hole "_") (Term.app `choose_middle_le_pow [`m])]))
                    (calcStep
                     («term_=_»
                      (Term.hole "_")
                      "="
                      («term_^_»
                       (num "4")
                       "^"
                       («term_+_» («term_*_» (num "2") "*" `m) "+" (num "1"))))
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented [(Mathlib.Tactic.RingNF.ring "ring")]))))
                    (calcStep
                     («term_=_»
                      (Term.hole "_")
                      "="
                      («term_^_» (num "4") "^" («term_+_» `n "+" (num "2"))))
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.rwSeq
                          "rw"
                          []
                          (Tactic.rwRuleSeq
                           "["
                           [(Tactic.rwRule [] `two_mul)
                            ","
                            (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `twice_m)]
                           "]")
                          [])]))))])]))))])))
         (Term.matchAlt
          "|"
          [[(Term.app `Or.inr [`n_even])]]
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Std.Tactic.obtain
               "obtain"
               [(Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.one `one_lt_n)
                  "|"
                  (Std.Tactic.RCases.rcasesPat.one `n_le_one)])]
               [":"
                («term_∨_»
                 («term_<_» (num "1") "<" («term_+_» `n "+" (num "1")))
                 "∨"
                 («term_≤_» («term_+_» `n "+" (num "1")) "≤" (num "1")))]
               [":=" [(Term.app `lt_or_le [(num "1") («term_+_» `n "+" (num "1"))])]])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] (Term.app `primorial_succ [`one_lt_n `n_even]))]
                  "]")
                 [])
                []
                (calcTactic
                 "calc"
                 (calcStep
                  («term_≤_»
                   (NumberTheory.Primorial.«term_#» («term_+_» `n "+" (num "1")) "#")
                   "≤"
                   («term_^_» (num "4") "^" `n.succ))
                  ":="
                  (Term.app `primorial_le_4_pow [(«term_+_» `n "+" (num "1"))]))
                 [(calcStep
                   («term_≤_»
                    (Term.hole "_")
                    "≤"
                    («term_^_» (num "4") "^" («term_+_» `n "+" (num "2"))))
                   ":="
                   (Term.app
                    `pow_le_pow
                    [(Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
                     (Term.app `Nat.le_succ [(Term.hole "_")])]))])])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   [`n_zero []]
                   [(Term.typeSpec ":" («term_=_» `n "=" (num "0")))]
                   ":="
                   (Term.app
                    (Term.proj `eq_bot_iff "." (fieldIdx "2"))
                    [(Term.app (Term.proj `succ_le_succ_iff "." (fieldIdx "1")) [`n_le_one])]))))
                []
                (Mathlib.Tactic.normNum
                 "norm_num"
                 []
                 [(Tactic.simpArgs
                   "["
                   [(Tactic.simpLemma [] [] `n_zero)
                    ","
                    (Tactic.simpLemma [] [] `primorial)
                    ","
                    (Tactic.simpLemma [] [] `range_succ)
                    ","
                    (Tactic.simpLemma [] [] `prod_filter)
                    ","
                    (Tactic.simpLemma [] [] `Nat.not_prime_zero)
                    ","
                    (Tactic.simpLemma [] [] `Nat.prime_two)]
                   "]")]
                 [])])]))))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.one `one_lt_n)
              "|"
              (Std.Tactic.RCases.rcasesPat.one `n_le_one)])]
           [":"
            («term_∨_»
             («term_<_» (num "1") "<" («term_+_» `n "+" (num "1")))
             "∨"
             («term_≤_» («term_+_» `n "+" (num "1")) "≤" (num "1")))]
           [":=" [(Term.app `lt_or_le [(num "1") («term_+_» `n "+" (num "1"))])]])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] (Term.app `primorial_succ [`one_lt_n `n_even]))]
              "]")
             [])
            []
            (calcTactic
             "calc"
             (calcStep
              («term_≤_»
               (NumberTheory.Primorial.«term_#» («term_+_» `n "+" (num "1")) "#")
               "≤"
               («term_^_» (num "4") "^" `n.succ))
              ":="
              (Term.app `primorial_le_4_pow [(«term_+_» `n "+" (num "1"))]))
             [(calcStep
               («term_≤_»
                (Term.hole "_")
                "≤"
                («term_^_» (num "4") "^" («term_+_» `n "+" (num "2"))))
               ":="
               (Term.app
                `pow_le_pow
                [(Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
                 (Term.app `Nat.le_succ [(Term.hole "_")])]))])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`n_zero []]
               [(Term.typeSpec ":" («term_=_» `n "=" (num "0")))]
               ":="
               (Term.app
                (Term.proj `eq_bot_iff "." (fieldIdx "2"))
                [(Term.app (Term.proj `succ_le_succ_iff "." (fieldIdx "1")) [`n_le_one])]))))
            []
            (Mathlib.Tactic.normNum
             "norm_num"
             []
             [(Tactic.simpArgs
               "["
               [(Tactic.simpLemma [] [] `n_zero)
                ","
                (Tactic.simpLemma [] [] `primorial)
                ","
                (Tactic.simpLemma [] [] `range_succ)
                ","
                (Tactic.simpLemma [] [] `prod_filter)
                ","
                (Tactic.simpLemma [] [] `Nat.not_prime_zero)
                ","
                (Tactic.simpLemma [] [] `Nat.prime_two)]
               "]")]
             [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`n_zero []]
           [(Term.typeSpec ":" («term_=_» `n "=" (num "0")))]
           ":="
           (Term.app
            (Term.proj `eq_bot_iff "." (fieldIdx "2"))
            [(Term.app (Term.proj `succ_le_succ_iff "." (fieldIdx "1")) [`n_le_one])]))))
        []
        (Mathlib.Tactic.normNum
         "norm_num"
         []
         [(Tactic.simpArgs
           "["
           [(Tactic.simpLemma [] [] `n_zero)
            ","
            (Tactic.simpLemma [] [] `primorial)
            ","
            (Tactic.simpLemma [] [] `range_succ)
            ","
            (Tactic.simpLemma [] [] `prod_filter)
            ","
            (Tactic.simpLemma [] [] `Nat.not_prime_zero)
            ","
            (Tactic.simpLemma [] [] `Nat.prime_two)]
           "]")]
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.normNum
       "norm_num"
       []
       [(Tactic.simpArgs
         "["
         [(Tactic.simpLemma [] [] `n_zero)
          ","
          (Tactic.simpLemma [] [] `primorial)
          ","
          (Tactic.simpLemma [] [] `range_succ)
          ","
          (Tactic.simpLemma [] [] `prod_filter)
          ","
          (Tactic.simpLemma [] [] `Nat.not_prime_zero)
          ","
          (Tactic.simpLemma [] [] `Nat.prime_two)]
         "]")]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.prime_two
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.not_prime_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `prod_filter
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `range_succ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `primorial
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`n_zero []]
         [(Term.typeSpec ":" («term_=_» `n "=" (num "0")))]
         ":="
         (Term.app
          (Term.proj `eq_bot_iff "." (fieldIdx "2"))
          [(Term.app (Term.proj `succ_le_succ_iff "." (fieldIdx "1")) [`n_le_one])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `eq_bot_iff "." (fieldIdx "2"))
       [(Term.app (Term.proj `succ_le_succ_iff "." (fieldIdx "1")) [`n_le_one])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `succ_le_succ_iff "." (fieldIdx "1")) [`n_le_one])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n_le_one
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `succ_le_succ_iff "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `succ_le_succ_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `succ_le_succ_iff "." (fieldIdx "1")) [`n_le_one])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `eq_bot_iff "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `eq_bot_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `n "=" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
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
          [(Tactic.rwRule [] (Term.app `primorial_succ [`one_lt_n `n_even]))]
          "]")
         [])
        []
        (calcTactic
         "calc"
         (calcStep
          («term_≤_»
           (NumberTheory.Primorial.«term_#» («term_+_» `n "+" (num "1")) "#")
           "≤"
           («term_^_» (num "4") "^" `n.succ))
          ":="
          (Term.app `primorial_le_4_pow [(«term_+_» `n "+" (num "1"))]))
         [(calcStep
           («term_≤_» (Term.hole "_") "≤" («term_^_» (num "4") "^" («term_+_» `n "+" (num "2"))))
           ":="
           (Term.app
            `pow_le_pow
            [(Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
             (Term.app `Nat.le_succ [(Term.hole "_")])]))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_≤_»
         (NumberTheory.Primorial.«term_#» («term_+_» `n "+" (num "1")) "#")
         "≤"
         («term_^_» (num "4") "^" `n.succ))
        ":="
        (Term.app `primorial_le_4_pow [(«term_+_» `n "+" (num "1"))]))
       [(calcStep
         («term_≤_» (Term.hole "_") "≤" («term_^_» (num "4") "^" («term_+_» `n "+" (num "2"))))
         ":="
         (Term.app
          `pow_le_pow
          [(Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
           (Term.app `Nat.le_succ [(Term.hole "_")])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `pow_le_pow
       [(Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
        (Term.app `Nat.le_succ [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.le_succ [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nat.le_succ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Nat.le_succ [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.normNum "norm_num" [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, tactic) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pow_le_pow
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_» (Term.hole "_") "≤" («term_^_» (num "4") "^" («term_+_» `n "+" (num "2"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (num "4") "^" («term_+_» `n "+" (num "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "2")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (num "4")
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.app `primorial_le_4_pow [(«term_+_» `n "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `primorial_le_4_pow
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (NumberTheory.Primorial.«term_#» («term_+_» `n "+" (num "1")) "#")
       "≤"
       («term_^_» (num "4") "^" `n.succ))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (num "4") "^" `n.succ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n.succ
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (num "4")
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (NumberTheory.Primorial.«term_#» («term_+_» `n "+" (num "1")) "#")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.Primorial.«term_#»', expected 'NumberTheory.Primorial.term_#._@.NumberTheory.Primorial._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  primorial_le_4_pow
  : ∀ n : ℕ , n # ≤ 4 ^ n
  | 0 => le_rfl
    | 1 => le_of_inf_eq rfl
    |
      n + 2
      =>
      match
        Nat.mod_two_eq_zero_or_one n + 1
        with
        |
            Or.inl n_odd
            =>
            match
              Nat.even_iff . 2 n_odd
              with
              |
                ⟨ m , twice_m ⟩
                =>
                by
                  have recurse : m + 1 < n + 2 := by linarith
                    calc
                      n + 2 # = ∏ i in filter Nat.Prime range 2 * m + 2 , i
                        :=
                        by simpa [ two_mul , ← twice_m ]
                      _ = ∏ i in filter Nat.Prime Finset.ico m + 2 2 * m + 2 ∪ range m + 2 , i
                          :=
                          by
                            rw [ range_eq_Ico , Finset.union_comm , Finset.Ico_union_Ico_eq_Ico ]
                              · exact bot_le
                              ·
                                simpa
                                  only [ add_le_add_iff_right , two_mul ] using Nat.le_add_left m m
                        _
                            =
                            ∏
                              i
                              in
                              filter Nat.Prime Finset.ico m + 2 2 * m + 2
                                ∪
                                filter Nat.Prime range m + 2
                              ,
                              i
                          :=
                          by rw [ filter_union ]
                        _
                            =
                            ∏ i in filter Nat.Prime Finset.ico m + 2 2 * m + 2 , i
                              *
                              ∏ i in filter Nat.Prime range m + 2 , i
                          :=
                          by
                            apply Finset.prod_union
                              have
                                disj
                                  : Disjoint Finset.ico m + 2 2 * m + 2 range m + 2
                                  :=
                                  by
                                    simp
                                        only
                                        [
                                          Finset.disjoint_left
                                            ,
                                            and_imp
                                            ,
                                            Finset.mem_Ico
                                            ,
                                            not_lt
                                            ,
                                            Finset.mem_range
                                          ]
                                      intro _ pr _
                                      exact pr
                              exact Finset.disjoint_filter_filter disj
                        _ ≤ ∏ i in filter Nat.Prime Finset.ico m + 2 2 * m + 2 , i * 4 ^ m + 1
                          :=
                          Nat.mul_le_mul_left _ primorial_le_4_pow m + 1
                        _ ≤ choose 2 * m + 1 m + 1 * 4 ^ m + 1
                          :=
                          by
                            have
                                s
                                  :
                                    ∏ i in filter Nat.Prime Finset.ico m + 2 2 * m + 2 , i
                                      ∣
                                      choose 2 * m + 1 m + 1
                                  :=
                                  by
                                    refine' prod_primes_dvd choose 2 * m + 1 m + 1 _ _
                                      ·
                                        intro a
                                          rw [ Finset.mem_filter , Nat.prime_iff ]
                                          apply And.right
                                      ·
                                        intro a
                                          rw [ Finset.mem_filter ]
                                          intro pr
                                          rcases pr with ⟨ size , is_prime ⟩
                                          simp only [ Finset.mem_Ico ] at size
                                          rcases size with ⟨ a_big , a_small ⟩
                                          exact
                                            dvd_choose_of_middling_prime
                                              a is_prime m a_big nat.lt_succ_iff.mp a_small
                              have
                                r
                                  :
                                    ∏ i in filter Nat.Prime Finset.ico m + 2 2 * m + 2 , i
                                      ≤
                                      choose 2 * m + 1 m + 1
                                  :=
                                  by
                                    refine' @ Nat.le_of_dvd _ _ _ s
                                      exact @ choose_pos 2 * m + 1 m + 1 by linarith
                              exact Nat.mul_le_mul_right _ r
                        _ = choose 2 * m + 1 m * 4 ^ m + 1 := by rw [ choose_symm_half m ]
                        _ ≤ 4 ^ m * 4 ^ m + 1 := Nat.mul_le_mul_right _ choose_middle_le_pow m
                        _ = 4 ^ 2 * m + 1 := by ring
                        _ = 4 ^ n + 2 := by rw [ two_mul , ← twice_m ]
          |
            Or.inr n_even
            =>
            by
              obtain one_lt_n | n_le_one : 1 < n + 1 ∨ n + 1 ≤ 1 := lt_or_le 1 n + 1
                ·
                  rw [ primorial_succ one_lt_n n_even ]
                    calc
                      n + 1 # ≤ 4 ^ n.succ := primorial_le_4_pow n + 1
                      _ ≤ 4 ^ n + 2 := pow_le_pow by norm_num Nat.le_succ _
                ·
                  have n_zero : n = 0 := eq_bot_iff . 2 succ_le_succ_iff . 1 n_le_one
                    norm_num
                      [
                        n_zero
                          ,
                          primorial
                          ,
                          range_succ
                          ,
                          prod_filter
                          ,
                          Nat.not_prime_zero
                          ,
                          Nat.prime_two
                        ]
#align primorial_le_4_pow primorial_le_4_pow

