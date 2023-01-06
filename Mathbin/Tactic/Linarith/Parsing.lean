/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis

! This file was ported from Lean 3 source module tactic.linarith.parsing
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Linarith.Datatypes

/-!
# Parsing input expressions into linear form

`linarith` computes the linear form of its input expressions,
assuming (without justification) that the type of these expressions
is a commutative semiring.
It identifies atoms up to ring-equivalence: that is, `(y*3)*x` will be identified `3*(x*y)`,
where the monomial `x*y` is the linear atom.

* Variables are represented by natural numbers.
* Monomials are represented by `monom := rb_map ℕ ℕ`.
  The monomial `1` is represented by the empty map.
* Linear combinations of monomials are represented by `sum := rb_map monom ℤ`.

All input expressions are converted to `sum`s, preserving the map from expressions to variables.
We then discard the monomial information, mapping each distinct monomial to a natural number.
The resulting `rb_map ℕ ℤ` represents the ring-normalized linear form of the expression.
This is ultimately converted into a `linexp` in the obvious way.

`linear_forms_and_vars` is the main entry point into this file. Everything else is contained.
-/


open Native Linarith.Ineq Tactic

namespace Linarith

/-! ### Parsing datatypes -/


/-- Variables (represented by natural numbers) map to their power. -/
@[reducible]
unsafe def monom : Type :=
  rb_map ℕ ℕ
#align linarith.monom linarith.monom

/-- `1` is represented by the empty monomial, the product of no variables. -/
unsafe def monom.one : monom :=
  rb_map.mk _ _
#align linarith.monom.one linarith.monom.one

/-- Compare monomials by first comparing their keys and then their powers. -/
@[reducible]
unsafe def monom.lt : monom → monom → Prop := fun a b =>
  a.keys < b.keys || a.keys = b.keys && a.values < b.values
#align linarith.monom.lt linarith.monom.lt

unsafe instance : LT monom :=
  ⟨monom.lt⟩

/-- Linear combinations of monomials are represented by mapping monomials to coefficients. -/
@[reducible]
unsafe def sum : Type :=
  rb_map monom ℤ
#align linarith.sum linarith.sum

/-- `1` is represented as the singleton sum of the monomial `monom.one` with coefficient 1. -/
unsafe def sum.one : sum :=
  rb_map.of_list [(monom.one, 1)]
#align linarith.sum.one linarith.sum.one

/-- `sum.scale_by_monom s m` multiplies every monomial in `s` by `m`. -/
unsafe def sum.scale_by_monom (s : sum) (m : monom) : sum :=
  (s.fold mk_rb_map) fun m' coeff sm => sm.insert (m.add m') coeff
#align linarith.sum.scale_by_monom linarith.sum.scale_by_monom

/-- `sum.mul s1 s2` distributes the multiplication of two sums.` -/
unsafe def sum.mul (s1 s2 : sum) : sum :=
  (s1.fold mk_rb_map) fun mn coeff sm => sm.add <| (s2.scale_by_monom mn).scale coeff
#align linarith.sum.mul linarith.sum.mul

/-- The `n`th power of `s : sum` is the `n`-fold product of `s`, with `s.pow 0 = sum.one`. -/
unsafe def sum.pow (s : sum) : ℕ → sum
  | 0 => sum.one
  | k + 1 => s.mul (sum.pow k)
#align linarith.sum.pow linarith.sum.pow

/-- `sum_of_monom m` lifts `m` to a sum with coefficient `1`. -/
unsafe def sum_of_monom (m : monom) : sum :=
  mk_rb_map.insert m 1
#align linarith.sum_of_monom linarith.sum_of_monom

/-- The unit monomial `one` is represented by the empty rb map. -/
unsafe def one : monom :=
  mk_rb_map
#align linarith.one linarith.one

/-- A scalar `z` is represented by a `sum` with coefficient `z` and monomial `one` -/
unsafe def scalar (z : ℤ) : sum :=
  mk_rb_map.insert one z
#align linarith.scalar linarith.scalar

/-- A single variable `n` is represented by a sum with coefficient `1` and monomial `n`. -/
unsafe def var (n : ℕ) : sum :=
  mk_rb_map.insert (mk_rb_map.insert n 1) 1
#align linarith.var linarith.var

/-! ### Parsing algorithms -/


-- mathport name: exprexmap
local notation "exmap" => List (expr × ℕ)

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`linear_form_of_atom red map e` is the atomic case for `linear_form_of_expr`.\nIf `e` appears with index `k` in `map`, it returns the singleton sum `var k`.\nOtherwise it updates `map`, adding `e` with index `n`, and returns the singleton sum `var n`.\n-/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `linear_form_of_atom [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`red] [":" `Transparency] [] ")")
        (Term.explicitBinder
         "("
         [`m]
         [":" (Linarith.Tactic.Linarith.Parsing.termexmap "exmap")]
         []
         ")")
        (Term.explicitBinder "(" [`e] [":" `expr] [] ")")]
       [(Term.typeSpec
         ":"
         (Term.app
          `tactic
          [(«term_×_» (Linarith.Tactic.Linarith.Parsing.termexmap "exmap") "×" `Sum)]))])
      (Command.declValSimple
       ":="
       («term_<|>_»
        (Term.do
         "do"
         (Term.doSeqIndent
          [(Term.doSeqItem
            (Term.doLetArrow
             "let"
             []
             (Term.doPatDecl
              (Term.tuple "(" [(Term.hole "_") "," [`k]] ")")
              "←"
              (Term.doExpr (Term.app (Term.proj `m "." `find_defeq) [`red `e]))
              []))
            [])
           (Term.doSeqItem
            (Term.doExpr (Term.app `return [(Term.tuple "(" [`m "," [(Term.app `var [`k])]] ")")]))
            [])]))
        "<|>"
        (Term.let
         "let"
         (Term.letDecl
          (Term.letIdDecl `n [] [] ":=" («term_+_» (Term.proj `m "." `length) "+" (num "1"))))
         []
         (Term.app
          `return
          [(Term.tuple
            "("
            [(«term_::_» (Term.tuple "(" [`e "," [`n]] ")") "::" `m) "," [(Term.app `var [`n])]]
            ")")])))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|>_»
       (Term.do
        "do"
        (Term.doSeqIndent
         [(Term.doSeqItem
           (Term.doLetArrow
            "let"
            []
            (Term.doPatDecl
             (Term.tuple "(" [(Term.hole "_") "," [`k]] ")")
             "←"
             (Term.doExpr (Term.app (Term.proj `m "." `find_defeq) [`red `e]))
             []))
           [])
          (Term.doSeqItem
           (Term.doExpr (Term.app `return [(Term.tuple "(" [`m "," [(Term.app `var [`k])]] ")")]))
           [])]))
       "<|>"
       (Term.let
        "let"
        (Term.letDecl
         (Term.letIdDecl `n [] [] ":=" («term_+_» (Term.proj `m "." `length) "+" (num "1"))))
        []
        (Term.app
         `return
         [(Term.tuple
           "("
           [(«term_::_» (Term.tuple "(" [`e "," [`n]] ")") "::" `m) "," [(Term.app `var [`n])]]
           ")")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.let
       "let"
       (Term.letDecl
        (Term.letIdDecl `n [] [] ":=" («term_+_» (Term.proj `m "." `length) "+" (num "1"))))
       []
       (Term.app
        `return
        [(Term.tuple
          "("
          [(«term_::_» (Term.tuple "(" [`e "," [`n]] ")") "::" `m) "," [(Term.app `var [`n])]]
          ")")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `return
       [(Term.tuple
         "("
         [(«term_::_» (Term.tuple "(" [`e "," [`n]] ")") "::" `m) "," [(Term.app `var [`n])]]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple
       "("
       [(«term_::_» (Term.tuple "(" [`e "," [`n]] ")") "::" `m) "," [(Term.app `var [`n])]]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `var [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `var
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_::_» (Term.tuple "(" [`e "," [`n]] ")") "::" `m)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 67 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
      (Term.tuple "(" [`e "," [`n]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 67, (some 67, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `return
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» (Term.proj `m "." `length) "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.proj `m "." `length)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 20 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doPatDecl
            (Term.tuple "(" [(Term.hole "_") "," [`k]] ")")
            "←"
            (Term.doExpr (Term.app (Term.proj `m "." `find_defeq) [`red `e]))
            []))
          [])
         (Term.doSeqItem
          (Term.doExpr (Term.app `return [(Term.tuple "(" [`m "," [(Term.app `var [`k])]] ")")]))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `return [(Term.tuple "(" [`m "," [(Term.app `var [`k])]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`m "," [(Term.app `var [`k])]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `var [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `var
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `return
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doPatDecl', expected 'Lean.Parser.Term.doIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app (Term.proj `m "." `find_defeq) [`red `e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `red
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `m "." `find_defeq)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [(Term.hole "_") "," [`k]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 21 >? 1023, (some 0, term) <=? (some 20, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.do
      "do"
      (Term.doSeqIndent
       [(Term.doSeqItem
         (Term.doLetArrow
          "let"
          []
          (Term.doPatDecl
           (Term.tuple "(" [(Term.hole "_") "," [`k]] ")")
           "←"
           (Term.doExpr (Term.app (Term.proj `m "." `find_defeq) [`red `e]))
           []))
         [])
        (Term.doSeqItem
         (Term.doExpr (Term.app `return [(Term.tuple "(" [`m "," [(Term.app `var [`k])]] ")")]))
         [])]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 20, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `tactic [(«term_×_» (Linarith.Tactic.Linarith.Parsing.termexmap "exmap") "×" `Sum)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_×_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_×_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_×_» (Linarith.Tactic.Linarith.Parsing.termexmap "exmap") "×" `Sum)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Sum
[PrettyPrinter.parenthesize] ...precedences are 35 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      (Linarith.Tactic.Linarith.Parsing.termexmap "exmap")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Linarith.Tactic.Linarith.Parsing.termexmap', expected 'Linarith.Tactic.Linarith.Parsing.termexmap._@.Tactic.Linarith.Parsing._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      `linear_form_of_atom red map e` is the atomic case for `linear_form_of_expr`.
      If `e` appears with index `k` in `map`, it returns the singleton sum `var k`.
      Otherwise it updates `map`, adding `e` with index `n`, and returns the singleton sum `var n`.
      -/
    unsafe
  def
    linear_form_of_atom
    ( red : Transparency ) ( m : exmap ) ( e : expr ) : tactic exmap × Sum
    :=
      do let ( _ , k ) ← m . find_defeq red e return ( m , var k )
        <|>
        let n := m . length + 1 return ( ( e , n ) :: m , var n )
#align linarith.linear_form_of_atom linarith.linear_form_of_atom

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`linear_form_of_expr red map e` computes the linear form of `e`.\n\n`map` is a lookup map from atomic expressions to variable numbers.\nIf a new atomic expression is encountered, it is added to the map with a new number.\nIt matches atomic expressions up to reducibility given by `red`.\n\nBecause it matches up to definitional equality, this function must be in the `tactic` monad,\nand forces some functions that call it into `tactic` as well.\n-/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `linear_form_of_expr [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`red] [":" `Transparency] [] ")")]
       [(Term.typeSpec
         ":"
         (Term.arrow
          (Linarith.Tactic.Linarith.Parsing.termexmap "exmap")
          "→"
          (Term.arrow
           `expr
           "→"
           (Term.app
            `tactic
            [(«term_×_» (Linarith.Tactic.Linarith.Parsing.termexmap "exmap") "×" `Sum)]))))])
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[`m
             ","
             (Term.namedPattern
              `e
              "@"
              []
              (Qq.«termQ(__)»
               "q("
               («term_*_»
                (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e1 ")") [])
                "*"
                (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e2 ")") []))
               []
               ")"))]]
           "=>"
           (Term.do
            "do"
            (Term.doSeqIndent
             [(Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doPatDecl
                 (Term.tuple "(" [`m' "," [`comp1]] ")")
                 "←"
                 (Term.doExpr (Term.app `linear_form_of_expr [`m `e1]))
                 []))
               [])
              (Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doPatDecl
                 (Term.tuple "(" [`m' "," [`comp2]] ")")
                 "←"
                 (Term.doExpr (Term.app `linear_form_of_expr [`m' `e2]))
                 []))
               [])
              (Term.doSeqItem
               (Term.doExpr
                (Term.app `return [(Term.tuple "(" [`m' "," [(Term.app `comp1 [`comp2])]] ")")]))
               [])])))
          (Term.matchAlt
           "|"
           [[`m
             ","
             (Qq.«termQ(__)»
              "q("
              («term_+_»
               (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e1 ")") [])
               "+"
               (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e2 ")") []))
              []
              ")")]]
           "=>"
           (Term.do
            "do"
            (Term.doSeqIndent
             [(Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doPatDecl
                 (Term.tuple "(" [`m' "," [`comp1]] ")")
                 "←"
                 (Term.doExpr (Term.app `linear_form_of_expr [`m `e1]))
                 []))
               [])
              (Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doPatDecl
                 (Term.tuple "(" [`m' "," [`comp2]] ")")
                 "←"
                 (Term.doExpr (Term.app `linear_form_of_expr [`m' `e2]))
                 []))
               [])
              (Term.doSeqItem
               (Term.doExpr
                (Term.app `return [(Term.tuple "(" [`m' "," [(Term.app `comp1 [`comp2])]] ")")]))
               [])])))
          (Term.matchAlt
           "|"
           [[`m
             ","
             (Qq.«termQ(__)»
              "q("
              («term_-_»
               (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e1 ")") [])
               "-"
               (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e2 ")") []))
              []
              ")")]]
           "=>"
           (Term.do
            "do"
            (Term.doSeqIndent
             [(Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doPatDecl
                 (Term.tuple "(" [`m' "," [`comp1]] ")")
                 "←"
                 (Term.doExpr (Term.app `linear_form_of_expr [`m `e1]))
                 []))
               [])
              (Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doPatDecl
                 (Term.tuple "(" [`m' "," [`comp2]] ")")
                 "←"
                 (Term.doExpr (Term.app `linear_form_of_expr [`m' `e2]))
                 []))
               [])
              (Term.doSeqItem
               (Term.doExpr
                (Term.app
                 `return
                 [(Term.tuple
                   "("
                   [`m' "," [(Term.app `comp1 [(Term.app `comp2 [(«term-_» "-" (num "1"))])])]]
                   ")")]))
               [])])))
          (Term.matchAlt
           "|"
           [[`m
             ","
             (Qq.«termQ(__)»
              "q("
              («term-_» "-" (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") []))
              []
              ")")]]
           "=>"
           (Term.do
            "do"
            (Term.doSeqIndent
             [(Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doPatDecl
                 (Term.tuple "(" [`m' "," [`comp]] ")")
                 "←"
                 (Term.doExpr (Term.app `linear_form_of_expr [`m `e]))
                 []))
               [])
              (Term.doSeqItem
               (Term.doExpr
                (Term.app
                 `return
                 [(Term.tuple "(" [`m' "," [(Term.app `comp [(«term-_» "-" (num "1"))])]] ")")]))
               [])])))
          (Term.matchAlt
           "|"
           [[`m
             ","
             (Term.namedPattern
              `p
              "@"
              []
              (Qq.«termQ(__)»
               "q("
               (Term.app
                (Term.explicit "@" `Pow.pow)
                [(Term.hole "_")
                 (termℕ "ℕ")
                 (Term.hole "_")
                 (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
                 (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `n ")") [])])
               []
               ")"))]]
           "=>"
           (Term.match
            "match"
            []
            []
            [(Term.matchDiscr [] (Term.proj `n "." `toNat))]
            "with"
            (Term.matchAlts
             [(Term.matchAlt
               "|"
               [[(Term.app `some [`k])]]
               "=>"
               (Term.do
                "do"
                (Term.doSeqIndent
                 [(Term.doSeqItem
                   (Term.doLetArrow
                    "let"
                    []
                    (Term.doPatDecl
                     (Term.tuple "(" [`m' "," [`comp]] ")")
                     "←"
                     (Term.doExpr (Term.app `linear_form_of_expr [`m `e]))
                     []))
                   [])
                  (Term.doSeqItem
                   (Term.doExpr
                    (Term.app `return [(Term.tuple "(" [`m' "," [(Term.app `comp [`k])]] ")")]))
                   [])])))
              (Term.matchAlt "|" [[`none]] "=>" (Term.app `linear_form_of_atom [`red `m `p]))])))
          (Term.matchAlt
           "|"
           [[`m "," `e]]
           "=>"
           (Term.match
            "match"
            []
            []
            [(Term.matchDiscr [] (Term.proj `e "." `to_int))]
            "with"
            (Term.matchAlts
             [(Term.matchAlt
               "|"
               [[(Term.app `some [(num "0")])]]
               "=>"
               (Term.app `return [(Term.anonymousCtor "⟨" [`m "," `mk_rb_map] "⟩")]))
              (Term.matchAlt
               "|"
               [[(Term.app `some [`z])]]
               "=>"
               (Term.app `return [(Term.anonymousCtor "⟨" [`m "," (Term.app `scalar [`z])] "⟩")]))
              (Term.matchAlt "|" [[`none]] "=>" (Term.app `linear_form_of_atom [`red `m `e]))])))])
        []))
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.match
       "match"
       []
       []
       [(Term.matchDiscr [] (Term.proj `e "." `to_int))]
       "with"
       (Term.matchAlts
        [(Term.matchAlt
          "|"
          [[(Term.app `some [(num "0")])]]
          "=>"
          (Term.app `return [(Term.anonymousCtor "⟨" [`m "," `mk_rb_map] "⟩")]))
         (Term.matchAlt
          "|"
          [[(Term.app `some [`z])]]
          "=>"
          (Term.app `return [(Term.anonymousCtor "⟨" [`m "," (Term.app `scalar [`z])] "⟩")]))
         (Term.matchAlt "|" [[`none]] "=>" (Term.app `linear_form_of_atom [`red `m `e]))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `linear_form_of_atom [`red `m `e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `red
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `linear_form_of_atom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `return [(Term.anonymousCtor "⟨" [`m "," (Term.app `scalar [`z])] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`m "," (Term.app `scalar [`z])] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `scalar [`z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `scalar
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `return
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some [`z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `return [(Term.anonymousCtor "⟨" [`m "," `mk_rb_map] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`m "," `mk_rb_map] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mk_rb_map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `return
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `e "." `to_int)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `e
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.match
       "match"
       []
       []
       [(Term.matchDiscr [] (Term.proj `n "." `toNat))]
       "with"
       (Term.matchAlts
        [(Term.matchAlt
          "|"
          [[(Term.app `some [`k])]]
          "=>"
          (Term.do
           "do"
           (Term.doSeqIndent
            [(Term.doSeqItem
              (Term.doLetArrow
               "let"
               []
               (Term.doPatDecl
                (Term.tuple "(" [`m' "," [`comp]] ")")
                "←"
                (Term.doExpr (Term.app `linear_form_of_expr [`m `e]))
                []))
              [])
             (Term.doSeqItem
              (Term.doExpr
               (Term.app `return [(Term.tuple "(" [`m' "," [(Term.app `comp [`k])]] ")")]))
              [])])))
         (Term.matchAlt "|" [[`none]] "=>" (Term.app `linear_form_of_atom [`red `m `p]))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `linear_form_of_atom [`red `m `p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `red
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `linear_form_of_atom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doPatDecl
            (Term.tuple "(" [`m' "," [`comp]] ")")
            "←"
            (Term.doExpr (Term.app `linear_form_of_expr [`m `e]))
            []))
          [])
         (Term.doSeqItem
          (Term.doExpr (Term.app `return [(Term.tuple "(" [`m' "," [(Term.app `comp [`k])]] ")")]))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `return [(Term.tuple "(" [`m' "," [(Term.app `comp [`k])]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`m' "," [(Term.app `comp [`k])]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `comp [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `comp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `return
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doPatDecl', expected 'Lean.Parser.Term.doIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `linear_form_of_expr [`m `e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `linear_form_of_expr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`m' "," [`comp]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `comp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `n "." `toNat)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.namedPattern
       `p
       "@"
       []
       (Qq.«termQ(__)»
        "q("
        (Term.app
         (Term.explicit "@" `Pow.pow)
         [(Term.hole "_")
          (termℕ "ℕ")
          (Term.hole "_")
          (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
          (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `n ")") [])])
        []
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Qq.«termQ(__)»
       "q("
       (Term.app
        (Term.explicit "@" `Pow.pow)
        [(Term.hole "_")
         (termℕ "ℕ")
         (Term.hole "_")
         (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
         (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `n ")") [])])
       []
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicit "@" `Pow.pow)
       [(Term.hole "_")
        (termℕ "ℕ")
        (Term.hole "_")
        (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
        (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `n ")") [])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'term.pseudo.antiquot', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'term.pseudo.antiquot', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'term.pseudo.antiquot', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'term.pseudo.antiquot', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'term.pseudo.antiquot', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `n ")") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'antiquotName'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'antiquotNestedExpr', expected 'ident'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'term.pseudo.antiquot', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'term.pseudo.antiquot', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'term.pseudo.antiquot', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'term.pseudo.antiquot', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'term.pseudo.antiquot', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'antiquotName'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'antiquotNestedExpr', expected 'ident'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (termℕ "ℕ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `Pow.pow)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Pow.pow
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doPatDecl
            (Term.tuple "(" [`m' "," [`comp]] ")")
            "←"
            (Term.doExpr (Term.app `linear_form_of_expr [`m `e]))
            []))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (Term.app
            `return
            [(Term.tuple "(" [`m' "," [(Term.app `comp [(«term-_» "-" (num "1"))])]] ")")]))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `return
       [(Term.tuple "(" [`m' "," [(Term.app `comp [(«term-_» "-" (num "1"))])]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`m' "," [(Term.app `comp [(«term-_» "-" (num "1"))])]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `comp [(«term-_» "-" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term-_» "-" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `comp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `return
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doPatDecl', expected 'Lean.Parser.Term.doIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `linear_form_of_expr [`m `e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `linear_form_of_expr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`m' "," [`comp]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `comp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Qq.«termQ(__)»
       "q("
       («term-_» "-" (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") []))
       []
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e ")") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'antiquotName'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'antiquotNestedExpr', expected 'ident'
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doPatDecl
            (Term.tuple "(" [`m' "," [`comp1]] ")")
            "←"
            (Term.doExpr (Term.app `linear_form_of_expr [`m `e1]))
            []))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doPatDecl
            (Term.tuple "(" [`m' "," [`comp2]] ")")
            "←"
            (Term.doExpr (Term.app `linear_form_of_expr [`m' `e2]))
            []))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (Term.app
            `return
            [(Term.tuple
              "("
              [`m' "," [(Term.app `comp1 [(Term.app `comp2 [(«term-_» "-" (num "1"))])])]]
              ")")]))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `return
       [(Term.tuple
         "("
         [`m' "," [(Term.app `comp1 [(Term.app `comp2 [(«term-_» "-" (num "1"))])])]]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple
       "("
       [`m' "," [(Term.app `comp1 [(Term.app `comp2 [(«term-_» "-" (num "1"))])])]]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `comp1 [(Term.app `comp2 [(«term-_» "-" (num "1"))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `comp2 [(«term-_» "-" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term-_» "-" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `comp2
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `comp2 [(Term.paren "(" («term-_» "-" (num "1")) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `comp1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `return
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doPatDecl', expected 'Lean.Parser.Term.doIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `linear_form_of_expr [`m' `e2])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e2
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `m'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `linear_form_of_expr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`m' "," [`comp2]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `comp2
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doPatDecl', expected 'Lean.Parser.Term.doIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `linear_form_of_expr [`m `e1])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `linear_form_of_expr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`m' "," [`comp1]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `comp1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Qq.«termQ(__)»
       "q("
       («term_-_»
        (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e1 ")") [])
        "-"
        (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e2 ")") []))
       []
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_»
       (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e1 ")") [])
       "-"
       (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e2 ")") []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e2 ")") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'antiquotName'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'antiquotNestedExpr', expected 'ident'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e1 ")") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'antiquotName'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'antiquotNestedExpr', expected 'ident'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doPatDecl
            (Term.tuple "(" [`m' "," [`comp1]] ")")
            "←"
            (Term.doExpr (Term.app `linear_form_of_expr [`m `e1]))
            []))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doPatDecl
            (Term.tuple "(" [`m' "," [`comp2]] ")")
            "←"
            (Term.doExpr (Term.app `linear_form_of_expr [`m' `e2]))
            []))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (Term.app `return [(Term.tuple "(" [`m' "," [(Term.app `comp1 [`comp2])]] ")")]))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `return [(Term.tuple "(" [`m' "," [(Term.app `comp1 [`comp2])]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`m' "," [(Term.app `comp1 [`comp2])]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `comp1 [`comp2])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `comp2
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `comp1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `return
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doPatDecl', expected 'Lean.Parser.Term.doIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `linear_form_of_expr [`m' `e2])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e2
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `m'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `linear_form_of_expr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`m' "," [`comp2]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `comp2
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doPatDecl', expected 'Lean.Parser.Term.doIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `linear_form_of_expr [`m `e1])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `linear_form_of_expr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`m' "," [`comp1]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `comp1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Qq.«termQ(__)»
       "q("
       («term_+_»
        (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e1 ")") [])
        "+"
        (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e2 ")") []))
       []
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e1 ")") [])
       "+"
       (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e2 ")") []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e2 ")") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'antiquotName'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'antiquotNestedExpr', expected 'ident'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e1 ")") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'antiquotName'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'antiquotNestedExpr', expected 'ident'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doPatDecl
            (Term.tuple "(" [`m' "," [`comp1]] ")")
            "←"
            (Term.doExpr (Term.app `linear_form_of_expr [`m `e1]))
            []))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doPatDecl
            (Term.tuple "(" [`m' "," [`comp2]] ")")
            "←"
            (Term.doExpr (Term.app `linear_form_of_expr [`m' `e2]))
            []))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (Term.app `return [(Term.tuple "(" [`m' "," [(Term.app `comp1 [`comp2])]] ")")]))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `return [(Term.tuple "(" [`m' "," [(Term.app `comp1 [`comp2])]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`m' "," [(Term.app `comp1 [`comp2])]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `comp1 [`comp2])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `comp2
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `comp1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `return
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doPatDecl', expected 'Lean.Parser.Term.doIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `linear_form_of_expr [`m' `e2])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e2
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `m'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `linear_form_of_expr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`m' "," [`comp2]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `comp2
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doPatDecl', expected 'Lean.Parser.Term.doIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `linear_form_of_expr [`m `e1])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `linear_form_of_expr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`m' "," [`comp1]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `comp1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.namedPattern
       `e
       "@"
       []
       (Qq.«termQ(__)»
        "q("
        («term_*_»
         (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e1 ")") [])
         "*"
         (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e2 ")") []))
        []
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Qq.«termQ(__)»
       "q("
       («term_*_»
        (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e1 ")") [])
        "*"
        (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e2 ")") []))
       []
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e1 ")") [])
       "*"
       (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e2 ")") []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e2 ")") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'antiquotName'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'antiquotNestedExpr', expected 'ident'
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (term.pseudo.antiquot "$" [] (antiquotNestedExpr "(" `e1 ")") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'antiquotName'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'antiquotNestedExpr', expected 'ident'
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `e
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Linarith.Tactic.Linarith.Parsing.termexmap "exmap")
       "→"
       (Term.arrow
        `expr
        "→"
        (Term.app
         `tactic
         [(«term_×_» (Linarith.Tactic.Linarith.Parsing.termexmap "exmap") "×" `Sum)])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       `expr
       "→"
       (Term.app
        `tactic
        [(«term_×_» (Linarith.Tactic.Linarith.Parsing.termexmap "exmap") "×" `Sum)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tactic [(«term_×_» (Linarith.Tactic.Linarith.Parsing.termexmap "exmap") "×" `Sum)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_×_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_×_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_×_» (Linarith.Tactic.Linarith.Parsing.termexmap "exmap") "×" `Sum)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Sum
[PrettyPrinter.parenthesize] ...precedences are 35 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      (Linarith.Tactic.Linarith.Parsing.termexmap "exmap")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Linarith.Tactic.Linarith.Parsing.termexmap', expected 'Linarith.Tactic.Linarith.Parsing.termexmap._@.Tactic.Linarith.Parsing._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      `linear_form_of_expr red map e` computes the linear form of `e`.
      
      `map` is a lookup map from atomic expressions to variable numbers.
      If a new atomic expression is encountered, it is added to the map with a new number.
      It matches atomic expressions up to reducibility given by `red`.
      
      Because it matches up to definitional equality, this function must be in the `tactic` monad,
      and forces some functions that call it into `tactic` as well.
      -/
    unsafe
  def
    linear_form_of_expr
    ( red : Transparency ) : exmap → expr → tactic exmap × Sum
    |
        m , e @ q( $ ( e1 ) * $ ( e2 ) )
        =>
        do
          let ( m' , comp1 ) ← linear_form_of_expr m e1
            let ( m' , comp2 ) ← linear_form_of_expr m' e2
            return ( m' , comp1 comp2 )
      |
        m , q( $ ( e1 ) + $ ( e2 ) )
        =>
        do
          let ( m' , comp1 ) ← linear_form_of_expr m e1
            let ( m' , comp2 ) ← linear_form_of_expr m' e2
            return ( m' , comp1 comp2 )
      |
        m , q( $ ( e1 ) - $ ( e2 ) )
        =>
        do
          let ( m' , comp1 ) ← linear_form_of_expr m e1
            let ( m' , comp2 ) ← linear_form_of_expr m' e2
            return ( m' , comp1 comp2 - 1 )
      |
        m , q( - $ ( e ) )
        =>
        do let ( m' , comp ) ← linear_form_of_expr m e return ( m' , comp - 1 )
      |
        m , p @ q( @ Pow.pow _ ℕ _ $ ( e ) $ ( n ) )
        =>
        match
          n . toNat
          with
          | some k => do let ( m' , comp ) ← linear_form_of_expr m e return ( m' , comp k )
            | none => linear_form_of_atom red m p
      |
        m , e
        =>
        match
          e . to_int
          with
          | some 0 => return ⟨ m , mk_rb_map ⟩
            | some z => return ⟨ m , scalar z ⟩
            | none => linear_form_of_atom red m e
#align linarith.linear_form_of_expr linarith.linear_form_of_expr

/-- `sum_to_lf s map` eliminates the monomial level of the `sum` `s`.

`map` is a lookup map from monomials to variable numbers.
The output `rb_map ℕ ℤ` has the same structure as `sum`,
but each monomial key is replaced with its index according to `map`.
If any new monomials are encountered, they are assigned variable numbers and `map` is updated.
 -/
unsafe def sum_to_lf (s : sum) (m : rb_map monom ℕ) : rb_map monom ℕ × rb_map ℕ ℤ :=
  (s.fold (m, mk_rb_map)) fun mn coeff ⟨map, out⟩ =>
    match map.find mn with
    | some n => ⟨map, out.insert n coeff⟩
    | none =>
      let n := map.size
      ⟨map.insert mn n, out.insert n coeff⟩
#align linarith.sum_to_lf linarith.sum_to_lf

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`to_comp red e e_map monom_map` converts an expression of the form `t < 0`, `t ≤ 0`, or `t = 0`\ninto a `comp` object.\n\n`e_map` maps atomic expressions to indices; `monom_map` maps monomials to indices.\nBoth of these are updated during processing and returned.\n-/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `to_comp [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`red] [":" `Transparency] [] ")")
        (Term.explicitBinder "(" [`e] [":" `expr] [] ")")
        (Term.explicitBinder
         "("
         [`e_map]
         [":" (Linarith.Tactic.Linarith.Parsing.termexmap "exmap")]
         []
         ")")
        (Term.explicitBinder "(" [`monom_map] [":" (Term.app `rb_map [`monom (termℕ "ℕ")])] [] ")")]
       [(Term.typeSpec
         ":"
         (Term.app
          `tactic
          [(«term_×_»
            `comp
            "×"
            («term_×_»
             (Linarith.Tactic.Linarith.Parsing.termexmap "exmap")
             "×"
             (Term.app `rb_map [`monom (termℕ "ℕ")])))]))])
      (Command.declValSimple
       ":="
       (Term.do
        "do"
        (Term.doSeqIndent
         [(Term.doSeqItem
           (Term.doLetArrow
            "let"
            []
            (Term.doPatDecl
             (Term.tuple "(" [`iq "," [`e]] ")")
             "←"
             (Term.doExpr (Term.app `parse_into_comp_and_expr [`e]))
             []))
           [])
          (Term.doSeqItem
           (Term.doLetArrow
            "let"
            []
            (Term.doPatDecl
             (Term.tuple "(" [`m' "," [`comp']] ")")
             "←"
             (Term.doExpr (Term.app `linear_form_of_expr [`red `e_map `e]))
             []))
           [])
          (Term.doSeqItem
           (Term.doLet
            "let"
            []
            (Term.letDecl
             (Term.letPatDecl
              (Term.anonymousCtor "⟨" [`nm "," `mm'] "⟩")
              []
              []
              ":="
              (Term.app `sum_to_lf [`comp' `monom_map]))))
           [])
          (Term.doSeqItem
           (Term.doExpr
            (Term.app
             `return
             [(Term.anonymousCtor
               "⟨"
               [(Term.anonymousCtor "⟨" [`iq "," `mm'] "⟩") "," `m' "," `nm]
               "⟩")]))
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
          (Term.doLetArrow
           "let"
           []
           (Term.doPatDecl
            (Term.tuple "(" [`iq "," [`e]] ")")
            "←"
            (Term.doExpr (Term.app `parse_into_comp_and_expr [`e]))
            []))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doPatDecl
            (Term.tuple "(" [`m' "," [`comp']] ")")
            "←"
            (Term.doExpr (Term.app `linear_form_of_expr [`red `e_map `e]))
            []))
          [])
         (Term.doSeqItem
          (Term.doLet
           "let"
           []
           (Term.letDecl
            (Term.letPatDecl
             (Term.anonymousCtor "⟨" [`nm "," `mm'] "⟩")
             []
             []
             ":="
             (Term.app `sum_to_lf [`comp' `monom_map]))))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (Term.app
            `return
            [(Term.anonymousCtor
              "⟨"
              [(Term.anonymousCtor "⟨" [`iq "," `mm'] "⟩") "," `m' "," `nm]
              "⟩")]))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `return
       [(Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`iq "," `mm'] "⟩") "," `m' "," `nm] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`iq "," `mm'] "⟩") "," `m' "," `nm] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`iq "," `mm'] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mm'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `iq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `return
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, doElem))
      (Term.app `sum_to_lf [`comp' `monom_map])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `monom_map
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `comp'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sum_to_lf
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`nm "," `mm'] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mm'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doPatDecl', expected 'Lean.Parser.Term.doIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `linear_form_of_expr [`red `e_map `e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `e_map
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `red
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `linear_form_of_expr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`m' "," [`comp']] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `comp'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doPatDecl', expected 'Lean.Parser.Term.doIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `parse_into_comp_and_expr [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `parse_into_comp_and_expr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`iq "," [`e]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `iq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `tactic
       [(«term_×_»
         `comp
         "×"
         («term_×_»
          (Linarith.Tactic.Linarith.Parsing.termexmap "exmap")
          "×"
          (Term.app `rb_map [`monom (termℕ "ℕ")])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_×_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_×_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_×_»
       `comp
       "×"
       («term_×_»
        (Linarith.Tactic.Linarith.Parsing.termexmap "exmap")
        "×"
        (Term.app `rb_map [`monom (termℕ "ℕ")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_×_»
       (Linarith.Tactic.Linarith.Parsing.termexmap "exmap")
       "×"
       (Term.app `rb_map [`monom (termℕ "ℕ")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `rb_map [`monom (termℕ "ℕ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℕ "ℕ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `monom
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `rb_map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 35 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      (Linarith.Tactic.Linarith.Parsing.termexmap "exmap")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Linarith.Tactic.Linarith.Parsing.termexmap', expected 'Linarith.Tactic.Linarith.Parsing.termexmap._@.Tactic.Linarith.Parsing._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      `to_comp red e e_map monom_map` converts an expression of the form `t < 0`, `t ≤ 0`, or `t = 0`
      into a `comp` object.
      
      `e_map` maps atomic expressions to indices; `monom_map` maps monomials to indices.
      Both of these are updated during processing and returned.
      -/
    unsafe
  def
    to_comp
    ( red : Transparency ) ( e : expr ) ( e_map : exmap ) ( monom_map : rb_map monom ℕ )
      : tactic comp × exmap × rb_map monom ℕ
    :=
      do
        let ( iq , e ) ← parse_into_comp_and_expr e
          let ( m' , comp' ) ← linear_form_of_expr red e_map e
          let ⟨ nm , mm' ⟩ := sum_to_lf comp' monom_map
          return ⟨ ⟨ iq , mm' ⟩ , m' , nm ⟩
#align linarith.to_comp linarith.to_comp

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`to_comp_fold red e_map exprs monom_map` folds `to_comp` over `exprs`,\nupdating `e_map` and `monom_map` as it goes.\n -/")]
      []
      []
      []
      [(Command.unsafe "unsafe")]
      [])
     (Command.def
      "def"
      (Command.declId `to_comp_fold [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`red] [":" `Transparency] [] ")")]
       [(Term.typeSpec
         ":"
         (Term.arrow
          (Linarith.Tactic.Linarith.Parsing.termexmap "exmap")
          "→"
          (Term.arrow
           (Term.app `List [`expr])
           "→"
           (Term.arrow
            (Term.app `rb_map [`monom (termℕ "ℕ")])
            "→"
            (Term.app
             `tactic
             [(«term_×_»
               (Term.app `List [`Comp])
               "×"
               («term_×_»
                (Linarith.Tactic.Linarith.Parsing.termexmap "exmap")
                "×"
                (Term.app `rb_map [`monom (termℕ "ℕ")])))])))))])
      (Command.declValEqns
       (Term.matchAltsWhereDecls
        (Term.matchAlts
         [(Term.matchAlt
           "|"
           [[`m "," («term[_]» "[" [] "]") "," `mm]]
           "=>"
           (Term.app `return [(Term.tuple "(" [(«term[_]» "[" [] "]") "," [`m "," `mm]] ")")]))
          (Term.matchAlt
           "|"
           [[`m "," («term_::_» `h "::" `t) "," `mm]]
           "=>"
           (Term.do
            "do"
            (Term.doSeqIndent
             [(Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doPatDecl
                 (Term.tuple "(" [`c "," [`m' "," `mm']] ")")
                 "←"
                 (Term.doExpr (Term.app `to_comp [`red `h `m `mm]))
                 []))
               [])
              (Term.doSeqItem
               (Term.doLetArrow
                "let"
                []
                (Term.doPatDecl
                 (Term.tuple "(" [`l "," [`mp "," `mm']] ")")
                 "←"
                 (Term.doExpr (Term.app `to_comp_fold [`m' `t `mm']))
                 []))
               [])
              (Term.doSeqItem
               (Term.doExpr
                (Term.app
                 `return
                 [(Term.tuple "(" [(«term_::_» `c "::" `l) "," [`mp "," `mm']] ")")]))
               [])])))])
        []))
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.do
       "do"
       (Term.doSeqIndent
        [(Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doPatDecl
            (Term.tuple "(" [`c "," [`m' "," `mm']] ")")
            "←"
            (Term.doExpr (Term.app `to_comp [`red `h `m `mm]))
            []))
          [])
         (Term.doSeqItem
          (Term.doLetArrow
           "let"
           []
           (Term.doPatDecl
            (Term.tuple "(" [`l "," [`mp "," `mm']] ")")
            "←"
            (Term.doExpr (Term.app `to_comp_fold [`m' `t `mm']))
            []))
          [])
         (Term.doSeqItem
          (Term.doExpr
           (Term.app `return [(Term.tuple "(" [(«term_::_» `c "::" `l) "," [`mp "," `mm']] ")")]))
          [])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doSeqIndent', expected 'Lean.Parser.Term.doSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `return [(Term.tuple "(" [(«term_::_» `c "::" `l) "," [`mp "," `mm']] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [(«term_::_» `c "::" `l) "," [`mp "," `mm']] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mm'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_::_» `c "::" `l)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 67 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 67, (some 67, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `return
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doPatDecl', expected 'Lean.Parser.Term.doIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `to_comp_fold [`m' `t `mm'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mm'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `m'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_comp_fold
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`l "," [`mp "," `mm']] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mm'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `l
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.doPatDecl', expected 'Lean.Parser.Term.doIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, doElem))
      (Term.app `to_comp [`red `h `m `mm])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mm
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `red
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_comp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, doElem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`c "," [`m' "," `mm']] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mm'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1023, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_::_» `h "::" `t)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `t
[PrettyPrinter.parenthesize] ...precedences are 67 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 67, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 67, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 67, (some 67, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `return [(Term.tuple "(" [(«term[_]» "[" [] "]") "," [`m "," `mm]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [(«term[_]» "[" [] "]") "," [`m "," `mm]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `return
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term[_]» "[" [] "]")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Linarith.Tactic.Linarith.Parsing.termexmap "exmap")
       "→"
       (Term.arrow
        (Term.app `List [`expr])
        "→"
        (Term.arrow
         (Term.app `rb_map [`monom (termℕ "ℕ")])
         "→"
         (Term.app
          `tactic
          [(«term_×_»
            (Term.app `List [`Comp])
            "×"
            («term_×_»
             (Linarith.Tactic.Linarith.Parsing.termexmap "exmap")
             "×"
             (Term.app `rb_map [`monom (termℕ "ℕ")])))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       (Term.app `List [`expr])
       "→"
       (Term.arrow
        (Term.app `rb_map [`monom (termℕ "ℕ")])
        "→"
        (Term.app
         `tactic
         [(«term_×_»
           (Term.app `List [`Comp])
           "×"
           («term_×_»
            (Linarith.Tactic.Linarith.Parsing.termexmap "exmap")
            "×"
            (Term.app `rb_map [`monom (termℕ "ℕ")])))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       (Term.app `rb_map [`monom (termℕ "ℕ")])
       "→"
       (Term.app
        `tactic
        [(«term_×_»
          (Term.app `List [`Comp])
          "×"
          («term_×_»
           (Linarith.Tactic.Linarith.Parsing.termexmap "exmap")
           "×"
           (Term.app `rb_map [`monom (termℕ "ℕ")])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `tactic
       [(«term_×_»
         (Term.app `List [`Comp])
         "×"
         («term_×_»
          (Linarith.Tactic.Linarith.Parsing.termexmap "exmap")
          "×"
          (Term.app `rb_map [`monom (termℕ "ℕ")])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_×_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_×_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_×_»
       (Term.app `List [`Comp])
       "×"
       («term_×_»
        (Linarith.Tactic.Linarith.Parsing.termexmap "exmap")
        "×"
        (Term.app `rb_map [`monom (termℕ "ℕ")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_×_»
       (Linarith.Tactic.Linarith.Parsing.termexmap "exmap")
       "×"
       (Term.app `rb_map [`monom (termℕ "ℕ")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `rb_map [`monom (termℕ "ℕ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℕ "ℕ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `monom
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `rb_map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 35 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      (Linarith.Tactic.Linarith.Parsing.termexmap "exmap")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Linarith.Tactic.Linarith.Parsing.termexmap', expected 'Linarith.Tactic.Linarith.Parsing.termexmap._@.Tactic.Linarith.Parsing._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      `to_comp_fold red e_map exprs monom_map` folds `to_comp` over `exprs`,
      updating `e_map` and `monom_map` as it goes.
       -/
    unsafe
  def
    to_comp_fold
    ( red : Transparency )
      : exmap → List expr → rb_map monom ℕ → tactic List Comp × exmap × rb_map monom ℕ
    | m , [ ] , mm => return ( [ ] , m , mm )
      |
        m , h :: t , mm
        =>
        do
          let ( c , m' , mm' ) ← to_comp red h m mm
            let ( l , mp , mm' ) ← to_comp_fold m' t mm'
            return ( c :: l , mp , mm' )
#align linarith.to_comp_fold linarith.to_comp_fold

/-- `linear_forms_and_vars red pfs` is the main interface for computing the linear forms of a list
of expressions. Given a list `pfs` of proofs of comparisons, it produces a list `c` of `comps` of
the same length, such that `c[i]` represents the linear form of the type of `pfs[i]`.

It also returns the largest variable index that appears in comparisons in `c`.
-/
unsafe def linear_forms_and_max_var (red : Transparency) (pfs : List expr) :
    tactic (List Comp × ℕ) := do
  let pftps ← pfs.mmap infer_type
  let (l, _, map) ← to_comp_fold red [] pftps mk_rb_map
  return (l, map - 1)
#align linarith.linear_forms_and_max_var linarith.linear_forms_and_max_var

end Linarith

