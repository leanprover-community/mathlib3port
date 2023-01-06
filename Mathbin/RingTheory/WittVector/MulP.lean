/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module ring_theory.witt_vector.mul_p
! leanprover-community/mathlib commit 26f081a2fb920140ed5bc5cc5344e84bcc7cb2b2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.WittVector.IsPoly

/-!
## Multiplication by `n` in the ring of Witt vectors

In this file we show that multiplication by `n` in the ring of Witt vectors
is a polynomial function. We then use this fact to show that the composition of Frobenius
and Verschiebung is equal to multiplication by `p`.

### Main declarations

* `mul_n_is_poly`: multiplication by `n` is a polynomial function

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/


namespace WittVector

variable {p : ℕ} {R : Type _} [hp : Fact p.Prime] [CommRing R]

-- mathport name: expr𝕎
local notation "𝕎" => WittVector p

-- type as `\bbW`
open MvPolynomial

noncomputable section

include hp

variable (p)

/-- `witt_mul_n p n` is the family of polynomials that computes
the coefficients of `x * n` in terms of the coefficients of the Witt vector `x`. -/
noncomputable def wittMulN : ℕ → ℕ → MvPolynomial ℕ ℤ
  | 0 => 0
  | n + 1 => fun k => bind₁ (Function.uncurry <| ![witt_mul_n n, x]) (wittAdd p k)
#align witt_vector.witt_mul_n WittVector.wittMulN

variable {p}

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mul_n_coeff [])
      (Command.declSig
       [(Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")
        (Term.explicitBinder
         "("
         [`x]
         [":" (Term.app (WittVector.RingTheory.WittVector.MulP.term𝕎 "𝕎") [`R])]
         []
         ")")
        (Term.explicitBinder "(" [`k] [":" (termℕ "ℕ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (Term.proj («term_*_» `x "*" `n) "." `coeff) [`k])
         "="
         (Term.app `aeval [(Term.proj `x "." `coeff) (Term.app `wittMulN [`p `n `k])]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.induction'
            "induction'"
            [(Tactic.casesTarget [] `n)]
            []
            ["with" [(Lean.binderIdent `n) (Lean.binderIdent `ih)]]
            ["generalizing" [`k]])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `Nat.zero_eq)
                ","
                (Tactic.simpLemma [] [] `Nat.cast_zero)
                ","
                (Tactic.simpLemma [] [] `mul_zero)
                ","
                (Tactic.simpLemma [] [] `zero_coeff)
                ","
                (Tactic.simpLemma [] [] `witt_mul_n)
                ","
                (Tactic.simpLemma [] [] `AlgHom.map_zero)
                ","
                (Tactic.simpLemma [] [] `Pi.zero_apply)]
               "]"]
              [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `witt_mul_n)
                ","
                (Tactic.rwRule [] `Nat.succ_eq_add_one)
                ","
                (Tactic.rwRule [] `Nat.cast_add)
                ","
                (Tactic.rwRule [] `Nat.cast_one)
                ","
                (Tactic.rwRule [] `mul_add)
                ","
                (Tactic.rwRule [] `mul_one)
                ","
                (Tactic.rwRule [] `aeval_bind₁)
                ","
                (Tactic.rwRule [] `add_coeff)]
               "]")
              [])
             []
             (Tactic.apply
              "apply"
              (Term.app
               `eval₂_hom_congr
               [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")])
                (Term.hole "_")
                `rfl]))
             []
             (Std.Tactic.Ext.tacticExt1___
              "ext1"
              [(Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i)])
                   [])]
                 "⟩"))])
             []
             (Lean.Elab.Tactic.finCases "fin_cases" [`b] [])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `Function.uncurry)
                  ","
                  (Tactic.simpLemma [] [] `Matrix.cons_val_zero)
                  ","
                  (Tactic.simpLemma [] [] `ih)]
                 "]"]
                [])])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `Function.uncurry)
                  ","
                  (Tactic.simpLemma [] [] `Matrix.cons_val_one)
                  ","
                  (Tactic.simpLemma [] [] `Matrix.head_cons)
                  ","
                  (Tactic.simpLemma [] [] `aeval_X)]
                 "]"]
                [])])])])))
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
           [(Tactic.casesTarget [] `n)]
           []
           ["with" [(Lean.binderIdent `n) (Lean.binderIdent `ih)]]
           ["generalizing" [`k]])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `Nat.zero_eq)
               ","
               (Tactic.simpLemma [] [] `Nat.cast_zero)
               ","
               (Tactic.simpLemma [] [] `mul_zero)
               ","
               (Tactic.simpLemma [] [] `zero_coeff)
               ","
               (Tactic.simpLemma [] [] `witt_mul_n)
               ","
               (Tactic.simpLemma [] [] `AlgHom.map_zero)
               ","
               (Tactic.simpLemma [] [] `Pi.zero_apply)]
              "]"]
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `witt_mul_n)
               ","
               (Tactic.rwRule [] `Nat.succ_eq_add_one)
               ","
               (Tactic.rwRule [] `Nat.cast_add)
               ","
               (Tactic.rwRule [] `Nat.cast_one)
               ","
               (Tactic.rwRule [] `mul_add)
               ","
               (Tactic.rwRule [] `mul_one)
               ","
               (Tactic.rwRule [] `aeval_bind₁)
               ","
               (Tactic.rwRule [] `add_coeff)]
              "]")
             [])
            []
            (Tactic.apply
             "apply"
             (Term.app
              `eval₂_hom_congr
              [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")]) (Term.hole "_") `rfl]))
            []
            (Std.Tactic.Ext.tacticExt1___
             "ext1"
             [(Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i)])
                  [])]
                "⟩"))])
            []
            (Lean.Elab.Tactic.finCases "fin_cases" [`b] [])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `Function.uncurry)
                 ","
                 (Tactic.simpLemma [] [] `Matrix.cons_val_zero)
                 ","
                 (Tactic.simpLemma [] [] `ih)]
                "]"]
               [])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `Function.uncurry)
                 ","
                 (Tactic.simpLemma [] [] `Matrix.cons_val_one)
                 ","
                 (Tactic.simpLemma [] [] `Matrix.head_cons)
                 ","
                 (Tactic.simpLemma [] [] `aeval_X)]
                "]"]
               [])])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `witt_mul_n)
           ","
           (Tactic.rwRule [] `Nat.succ_eq_add_one)
           ","
           (Tactic.rwRule [] `Nat.cast_add)
           ","
           (Tactic.rwRule [] `Nat.cast_one)
           ","
           (Tactic.rwRule [] `mul_add)
           ","
           (Tactic.rwRule [] `mul_one)
           ","
           (Tactic.rwRule [] `aeval_bind₁)
           ","
           (Tactic.rwRule [] `add_coeff)]
          "]")
         [])
        []
        (Tactic.apply
         "apply"
         (Term.app
          `eval₂_hom_congr
          [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")]) (Term.hole "_") `rfl]))
        []
        (Std.Tactic.Ext.tacticExt1___
         "ext1"
         [(Std.Tactic.RCases.rintroPat.one
           (Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i)])
              [])]
            "⟩"))])
        []
        (Lean.Elab.Tactic.finCases "fin_cases" [`b] [])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `Function.uncurry)
             ","
             (Tactic.simpLemma [] [] `Matrix.cons_val_zero)
             ","
             (Tactic.simpLemma [] [] `ih)]
            "]"]
           [])])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `Function.uncurry)
             ","
             (Tactic.simpLemma [] [] `Matrix.cons_val_one)
             ","
             (Tactic.simpLemma [] [] `Matrix.head_cons)
             ","
             (Tactic.simpLemma [] [] `aeval_X)]
            "]"]
           [])])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `Function.uncurry)
           ","
           (Tactic.simpLemma [] [] `Matrix.cons_val_one)
           ","
           (Tactic.simpLemma [] [] `Matrix.head_cons)
           ","
           (Tactic.simpLemma [] [] `aeval_X)]
          "]"]
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `Function.uncurry)
         ","
         (Tactic.simpLemma [] [] `Matrix.cons_val_one)
         ","
         (Tactic.simpLemma [] [] `Matrix.head_cons)
         ","
         (Tactic.simpLemma [] [] `aeval_X)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `aeval_X
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Matrix.head_cons
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Matrix.cons_val_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Function.uncurry
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `Function.uncurry)
           ","
           (Tactic.simpLemma [] [] `Matrix.cons_val_zero)
           ","
           (Tactic.simpLemma [] [] `ih)]
          "]"]
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `Function.uncurry)
         ","
         (Tactic.simpLemma [] [] `Matrix.cons_val_zero)
         ","
         (Tactic.simpLemma [] [] `ih)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ih
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Matrix.cons_val_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Function.uncurry
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Lean.Elab.Tactic.finCases "fin_cases" [`b] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'token.«*»'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.tacticExt1___
       "ext1"
       [(Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `b)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i)])
            [])]
          "⟩"))])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply
       "apply"
       (Term.app
        `eval₂_hom_congr
        [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")]) (Term.hole "_") `rfl]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `eval₂_hom_congr
       [(Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")]) (Term.hole "_") `rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")])
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
      `RingHom.ext_int
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `RingHom.ext_int [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eval₂_hom_congr
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
        [(Tactic.rwRule [] `witt_mul_n)
         ","
         (Tactic.rwRule [] `Nat.succ_eq_add_one)
         ","
         (Tactic.rwRule [] `Nat.cast_add)
         ","
         (Tactic.rwRule [] `Nat.cast_one)
         ","
         (Tactic.rwRule [] `mul_add)
         ","
         (Tactic.rwRule [] `mul_one)
         ","
         (Tactic.rwRule [] `aeval_bind₁)
         ","
         (Tactic.rwRule [] `add_coeff)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_coeff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `aeval_bind₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.cast_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.cast_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.succ_eq_add_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `witt_mul_n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `Nat.zero_eq)
           ","
           (Tactic.simpLemma [] [] `Nat.cast_zero)
           ","
           (Tactic.simpLemma [] [] `mul_zero)
           ","
           (Tactic.simpLemma [] [] `zero_coeff)
           ","
           (Tactic.simpLemma [] [] `witt_mul_n)
           ","
           (Tactic.simpLemma [] [] `AlgHom.map_zero)
           ","
           (Tactic.simpLemma [] [] `Pi.zero_apply)]
          "]"]
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `Nat.zero_eq)
         ","
         (Tactic.simpLemma [] [] `Nat.cast_zero)
         ","
         (Tactic.simpLemma [] [] `mul_zero)
         ","
         (Tactic.simpLemma [] [] `zero_coeff)
         ","
         (Tactic.simpLemma [] [] `witt_mul_n)
         ","
         (Tactic.simpLemma [] [] `AlgHom.map_zero)
         ","
         (Tactic.simpLemma [] [] `Pi.zero_apply)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Pi.zero_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `AlgHom.map_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `witt_mul_n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_coeff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.cast_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.zero_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.induction'
       "induction'"
       [(Tactic.casesTarget [] `n)]
       []
       ["with" [(Lean.binderIdent `n) (Lean.binderIdent `ih)]]
       ["generalizing" [`k]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app (Term.proj («term_*_» `x "*" `n) "." `coeff) [`k])
       "="
       (Term.app `aeval [(Term.proj `x "." `coeff) (Term.app `wittMulN [`p `n `k])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `aeval [(Term.proj `x "." `coeff) (Term.app `wittMulN [`p `n `k])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `wittMulN [`p `n `k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `wittMulN
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `wittMulN [`p `n `k]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `x "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `aeval
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (Term.proj («term_*_» `x "*" `n) "." `coeff) [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj («term_*_» `x "*" `n) "." `coeff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_*_» `x "*" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_*_» `x "*" `n) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℕ "ℕ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (WittVector.RingTheory.WittVector.MulP.term𝕎 "𝕎") [`R])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (WittVector.RingTheory.WittVector.MulP.term𝕎 "𝕎")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'WittVector.RingTheory.WittVector.MulP.term𝕎', expected 'WittVector.RingTheory.WittVector.MulP.term𝕎._@.RingTheory.WittVector.MulP._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  mul_n_coeff
  ( n : ℕ ) ( x : 𝕎 R ) ( k : ℕ ) : x * n . coeff k = aeval x . coeff wittMulN p n k
  :=
    by
      induction' n with n ih generalizing k
        ·
          simp
            only
            [
              Nat.zero_eq
                ,
                Nat.cast_zero
                ,
                mul_zero
                ,
                zero_coeff
                ,
                witt_mul_n
                ,
                AlgHom.map_zero
                ,
                Pi.zero_apply
              ]
        ·
          rw
              [
                witt_mul_n
                  ,
                  Nat.succ_eq_add_one
                  ,
                  Nat.cast_add
                  ,
                  Nat.cast_one
                  ,
                  mul_add
                  ,
                  mul_one
                  ,
                  aeval_bind₁
                  ,
                  add_coeff
                ]
            apply eval₂_hom_congr RingHom.ext_int _ _ _ rfl
            ext1 ⟨ b , i ⟩
            fin_cases b
            · simp only [ Function.uncurry , Matrix.cons_val_zero , ih ]
            · simp only [ Function.uncurry , Matrix.cons_val_one , Matrix.head_cons , aeval_X ]
#align witt_vector.mul_n_coeff WittVector.mul_n_coeff

variable (p)

/-- Multiplication by `n` is a polynomial function. -/
@[is_poly]
theorem mul_n_is_poly (n : ℕ) : IsPoly p fun R _Rcr x => x * n :=
  ⟨⟨wittMulN p n, fun R _Rcr x => by
      funext k
      exact mul_n_coeff n x k⟩⟩
#align witt_vector.mul_n_is_poly WittVector.mul_n_is_poly

@[simp]
theorem bind₁_witt_mul_n_witt_polynomial (n k : ℕ) :
    bind₁ (wittMulN p n) (wittPolynomial p ℤ k) = n * wittPolynomial p ℤ k :=
  by
  induction' n with n ih
  · simp only [witt_mul_n, Nat.cast_zero, zero_mul, bind₁_zero_witt_polynomial]
  · rw [witt_mul_n, ← bind₁_bind₁, witt_add, witt_structure_int_prop]
    simp only [AlgHom.map_add, Nat.cast_succ, bind₁_X_right]
    rw [add_mul, one_mul, bind₁_rename, bind₁_rename]
    simp only [ih, Function.uncurry, Function.comp, bind₁_X_left, AlgHom.id_apply,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one]
#align witt_vector.bind₁_witt_mul_n_witt_polynomial WittVector.bind₁_witt_mul_n_witt_polynomial

end WittVector

