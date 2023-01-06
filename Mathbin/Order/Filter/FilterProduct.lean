/-
Copyright (c) 2019 Abhimanyu Pallavi Sudhir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhimanyu Pallavi Sudhir, Yury Kudryashov

! This file was ported from Lean 3 source module order.filter.filter_product
! leanprover-community/mathlib commit 26f081a2fb920140ed5bc5cc5344e84bcc7cb2b2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Filter.Ultrafilter
import Mathbin.Order.Filter.Germ

/-!
# Ultraproducts

If `φ` is an ultrafilter, then the space of germs of functions `f : α → β` at `φ` is called
the *ultraproduct*. In this file we prove properties of ultraproducts that rely on `φ` being an
ultrafilter. Definitions and properties that work for any filter should go to `order.filter.germ`.

## Tags

ultrafilter, ultraproduct
-/


universe u v

variable {α : Type u} {β : Type v} {φ : Ultrafilter α}

open Classical

namespace Filter

-- mathport name: «expr∀* , »
local notation3"∀* "(...)", "r:(scoped p => Filter.Eventually p φ) => r

namespace Germ

open Ultrafilter

-- mathport name: «exprβ*»
local notation "β*" => Germ (φ : Filter α) β

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `DivisionSemiring [`β]) "]")]
       (Term.typeSpec
        ":"
        (Term.app `DivisionSemiring [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])))
      (Command.declValSimple
       ":="
       (Term.structInst
        "{"
        [[`Germ.semiring "," `Germ.divInvMonoid "," `Germ.nontrivial] "with"]
        [(Term.structInstField
          (Term.structInstLVal `mul_inv_cancel [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`f]
            []
            "=>"
            (Term.app
             (Term.app `induction_on [`f])
             [(Term.fun
               "fun"
               (Term.basicFun
                [`f `hf]
                []
                "=>"
                («term_<|_»
                 (Term.proj `coe_eq "." (fieldIdx "2"))
                 "<|"
                 (Term.app
                  (Term.proj
                   (Term.app
                    (Term.proj `φ "." `em)
                    [(Term.fun
                      "fun"
                      (Term.basicFun [`y] [] "=>" («term_=_» (Term.app `f [`y]) "=" (num "0"))))])
                   "."
                   `elim)
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [`H]
                     []
                     "=>"
                     (Term.proj
                      («term_<|_» `hf "<|" (Term.app (Term.proj `coe_eq "." (fieldIdx "2")) [`H]))
                      "."
                      `elim)))
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [`H]
                     []
                     "=>"
                     (Term.app
                      (Term.proj `H "." `mono)
                      [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `mul_inv_cancel))])))]))))]))))
         []
         (Term.structInstField
          (Term.structInstLVal `inv_zero [])
          ":="
          («term_<|_»
           (Term.proj `coe_eq "." (fieldIdx "2"))
           "<|"
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
                 [(Tactic.simpLemma
                   []
                   []
                   (Term.paren "(" («term_∘_» (Term.cdot "·") "∘" (Term.cdot "·")) ")"))
                  ","
                  (Tactic.simpLemma [] [] `inv_zero)]
                 "]"]
                [])])))))]
        (Term.optEllipsis [])
        []
        "}")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       [[`Germ.semiring "," `Germ.divInvMonoid "," `Germ.nontrivial] "with"]
       [(Term.structInstField
         (Term.structInstLVal `mul_inv_cancel [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`f]
           []
           "=>"
           (Term.app
            (Term.app `induction_on [`f])
            [(Term.fun
              "fun"
              (Term.basicFun
               [`f `hf]
               []
               "=>"
               («term_<|_»
                (Term.proj `coe_eq "." (fieldIdx "2"))
                "<|"
                (Term.app
                 (Term.proj
                  (Term.app
                   (Term.proj `φ "." `em)
                   [(Term.fun
                     "fun"
                     (Term.basicFun [`y] [] "=>" («term_=_» (Term.app `f [`y]) "=" (num "0"))))])
                  "."
                  `elim)
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [`H]
                    []
                    "=>"
                    (Term.proj
                     («term_<|_» `hf "<|" (Term.app (Term.proj `coe_eq "." (fieldIdx "2")) [`H]))
                     "."
                     `elim)))
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [`H]
                    []
                    "=>"
                    (Term.app
                     (Term.proj `H "." `mono)
                     [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `mul_inv_cancel))])))]))))]))))
        []
        (Term.structInstField
         (Term.structInstLVal `inv_zero [])
         ":="
         («term_<|_»
          (Term.proj `coe_eq "." (fieldIdx "2"))
          "<|"
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
                [(Tactic.simpLemma
                  []
                  []
                  (Term.paren "(" («term_∘_» (Term.cdot "·") "∘" (Term.cdot "·")) ")"))
                 ","
                 (Tactic.simpLemma [] [] `inv_zero)]
                "]"]
               [])])))))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj `coe_eq "." (fieldIdx "2"))
       "<|"
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
             [(Tactic.simpLemma
               []
               []
               (Term.paren "(" («term_∘_» (Term.cdot "·") "∘" (Term.cdot "·")) ")"))
              ","
              (Tactic.simpLemma [] [] `inv_zero)]
             "]"]
            [])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
            [(Tactic.simpLemma
              []
              []
              (Term.paren "(" («term_∘_» (Term.cdot "·") "∘" (Term.cdot "·")) ")"))
             ","
             (Tactic.simpLemma [] [] `inv_zero)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma
          []
          []
          (Term.paren "(" («term_∘_» (Term.cdot "·") "∘" (Term.cdot "·")) ")"))
         ","
         (Tactic.simpLemma [] [] `inv_zero)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inv_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.paren "(" («term_∘_» (Term.cdot "·") "∘" (Term.cdot "·")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∘_» (Term.cdot "·") "∘" (Term.cdot "·"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.cdot "·")
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      (Term.cdot "·")
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1024, (none, [anonymous]) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 90, (some 90, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `coe_eq "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `coe_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f]
        []
        "=>"
        (Term.app
         (Term.app `induction_on [`f])
         [(Term.fun
           "fun"
           (Term.basicFun
            [`f `hf]
            []
            "=>"
            («term_<|_»
             (Term.proj `coe_eq "." (fieldIdx "2"))
             "<|"
             (Term.app
              (Term.proj
               (Term.app
                (Term.proj `φ "." `em)
                [(Term.fun
                  "fun"
                  (Term.basicFun [`y] [] "=>" («term_=_» (Term.app `f [`y]) "=" (num "0"))))])
               "."
               `elim)
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`H]
                 []
                 "=>"
                 (Term.proj
                  («term_<|_» `hf "<|" (Term.app (Term.proj `coe_eq "." (fieldIdx "2")) [`H]))
                  "."
                  `elim)))
               (Term.fun
                "fun"
                (Term.basicFun
                 [`H]
                 []
                 "=>"
                 (Term.app
                  (Term.proj `H "." `mono)
                  [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `mul_inv_cancel))])))]))))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app `induction_on [`f])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`f `hf]
          []
          "=>"
          («term_<|_»
           (Term.proj `coe_eq "." (fieldIdx "2"))
           "<|"
           (Term.app
            (Term.proj
             (Term.app
              (Term.proj `φ "." `em)
              [(Term.fun
                "fun"
                (Term.basicFun [`y] [] "=>" («term_=_» (Term.app `f [`y]) "=" (num "0"))))])
             "."
             `elim)
            [(Term.fun
              "fun"
              (Term.basicFun
               [`H]
               []
               "=>"
               (Term.proj
                («term_<|_» `hf "<|" (Term.app (Term.proj `coe_eq "." (fieldIdx "2")) [`H]))
                "."
                `elim)))
             (Term.fun
              "fun"
              (Term.basicFun
               [`H]
               []
               "=>"
               (Term.app
                (Term.proj `H "." `mono)
                [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `mul_inv_cancel))])))]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f `hf]
        []
        "=>"
        («term_<|_»
         (Term.proj `coe_eq "." (fieldIdx "2"))
         "<|"
         (Term.app
          (Term.proj
           (Term.app
            (Term.proj `φ "." `em)
            [(Term.fun
              "fun"
              (Term.basicFun [`y] [] "=>" («term_=_» (Term.app `f [`y]) "=" (num "0"))))])
           "."
           `elim)
          [(Term.fun
            "fun"
            (Term.basicFun
             [`H]
             []
             "=>"
             (Term.proj
              («term_<|_» `hf "<|" (Term.app (Term.proj `coe_eq "." (fieldIdx "2")) [`H]))
              "."
              `elim)))
           (Term.fun
            "fun"
            (Term.basicFun
             [`H]
             []
             "=>"
             (Term.app
              (Term.proj `H "." `mono)
              [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `mul_inv_cancel))])))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj `coe_eq "." (fieldIdx "2"))
       "<|"
       (Term.app
        (Term.proj
         (Term.app
          (Term.proj `φ "." `em)
          [(Term.fun
            "fun"
            (Term.basicFun [`y] [] "=>" («term_=_» (Term.app `f [`y]) "=" (num "0"))))])
         "."
         `elim)
        [(Term.fun
          "fun"
          (Term.basicFun
           [`H]
           []
           "=>"
           (Term.proj
            («term_<|_» `hf "<|" (Term.app (Term.proj `coe_eq "." (fieldIdx "2")) [`H]))
            "."
            `elim)))
         (Term.fun
          "fun"
          (Term.basicFun
           [`H]
           []
           "=>"
           (Term.app
            (Term.proj `H "." `mono)
            [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `mul_inv_cancel))])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app
         (Term.proj `φ "." `em)
         [(Term.fun
           "fun"
           (Term.basicFun [`y] [] "=>" («term_=_» (Term.app `f [`y]) "=" (num "0"))))])
        "."
        `elim)
       [(Term.fun
         "fun"
         (Term.basicFun
          [`H]
          []
          "=>"
          (Term.proj
           («term_<|_» `hf "<|" (Term.app (Term.proj `coe_eq "." (fieldIdx "2")) [`H]))
           "."
           `elim)))
        (Term.fun
         "fun"
         (Term.basicFun
          [`H]
          []
          "=>"
          (Term.app
           (Term.proj `H "." `mono)
           [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `mul_inv_cancel))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`H]
        []
        "=>"
        (Term.app
         (Term.proj `H "." `mono)
         [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `mul_inv_cancel))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `H "." `mono)
       [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `mul_inv_cancel))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`x] [] "=>" `mul_inv_cancel))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_inv_cancel
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `H "." `mono)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `H
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`H]
        []
        "=>"
        (Term.proj
         («term_<|_» `hf "<|" (Term.app (Term.proj `coe_eq "." (fieldIdx "2")) [`H]))
         "."
         `elim)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       («term_<|_» `hf "<|" (Term.app (Term.proj `coe_eq "." (fieldIdx "2")) [`H]))
       "."
       `elim)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_<|_» `hf "<|" (Term.app (Term.proj `coe_eq "." (fieldIdx "2")) [`H]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `coe_eq "." (fieldIdx "2")) [`H])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `coe_eq "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `coe_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_» `hf "<|" (Term.app (Term.proj `coe_eq "." (fieldIdx "2")) [`H]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`H]
       []
       "=>"
       (Term.proj
        (Term.paren
         "("
         («term_<|_» `hf "<|" (Term.app (Term.proj `coe_eq "." (fieldIdx "2")) [`H]))
         ")")
        "."
        `elim)))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        (Term.proj `φ "." `em)
        [(Term.fun
          "fun"
          (Term.basicFun [`y] [] "=>" («term_=_» (Term.app `f [`y]) "=" (num "0"))))])
       "."
       `elim)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj `φ "." `em)
       [(Term.fun "fun" (Term.basicFun [`y] [] "=>" («term_=_» (Term.app `f [`y]) "=" (num "0"))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`y] [] "=>" («term_=_» (Term.app `f [`y]) "=" (num "0"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.app `f [`y]) "=" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `f [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `φ "." `em)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `φ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj `φ "." `em)
      [(Term.fun "fun" (Term.basicFun [`y] [] "=>" («term_=_» (Term.app `f [`y]) "=" (num "0"))))])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `coe_eq "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `coe_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app `induction_on [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `induction_on
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `induction_on [`f]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.nontrivial
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.divInvMonoid
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.semiring
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `DivisionSemiring [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  [ DivisionSemiring β ] : DivisionSemiring β*
  :=
    {
      Germ.semiring , Germ.divInvMonoid , Germ.nontrivial with
      mul_inv_cancel
          :=
          fun
            f
              =>
              induction_on f
                fun
                  f hf
                    =>
                    coe_eq . 2
                      <|
                      φ . em fun y => f y = 0 . elim
                        fun H => hf <| coe_eq . 2 H . elim fun H => H . mono fun x => mul_inv_cancel
        inv_zero := coe_eq . 2 <| by simp only [ ( · ∘ · ) , inv_zero ]
      }

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `DivisionRing [`β]) "]")]
       (Term.typeSpec
        ":"
        (Term.app `DivisionRing [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])))
      (Command.declValSimple
       ":="
       (Term.structInst
        "{"
        [[`Germ.ring "," `Germ.divisionSemiring] "with"]
        []
        (Term.optEllipsis [])
        []
        "}")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       [[`Germ.ring "," `Germ.divisionSemiring] "with"]
       []
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.divisionSemiring
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.ring
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `DivisionRing [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance [ DivisionRing β ] : DivisionRing β* := { Germ.ring , Germ.divisionSemiring with }

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `Semifield [`β]) "]")]
       (Term.typeSpec
        ":"
        (Term.app `Semifield [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])))
      (Command.declValSimple
       ":="
       (Term.structInst
        "{"
        [[`Germ.commSemiring "," `Germ.divisionSemiring] "with"]
        []
        (Term.optEllipsis [])
        []
        "}")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       [[`Germ.commSemiring "," `Germ.divisionSemiring] "with"]
       []
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.divisionSemiring
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.commSemiring
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `Semifield [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance [ Semifield β ] : Semifield β* := { Germ.commSemiring , Germ.divisionSemiring with }

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `Field [`β]) "]")]
       (Term.typeSpec
        ":"
        (Term.app `Field [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])))
      (Command.declValSimple
       ":="
       (Term.structInst
        "{"
        [[`Germ.commRing "," `Germ.divisionRing] "with"]
        []
        (Term.optEllipsis [])
        []
        "}")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       [[`Germ.commRing "," `Germ.divisionRing] "with"]
       []
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.divisionRing
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.commRing
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `Field [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance [ Field β ] : Field β* := { Germ.commRing , Germ.divisionRing with }

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `coe_lt [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `Preorder [`β]) "]")
        (Term.implicitBinder "{" [`f `g] [":" (Term.arrow `α "→" `β)] "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_<_»
          (Term.typeAscription
           "("
           `f
           ":"
           [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
           ")")
          "<"
          `g)
         "↔"
         (Filter.Order.Filter.FilterProduct.«term∀*_,_»
          "∀*"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
          ", "
          («term_<_» (Term.app `f [`x]) "<" (Term.app `g [`x]))))))
      (Command.declValSimple
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
             [(Tactic.simpLemma [] [] `lt_iff_le_not_le)
              ","
              (Tactic.simpLemma [] [] `eventually_and)
              ","
              (Tactic.simpLemma [] [] `coe_le)
              ","
              (Tactic.simpLemma [] [] `eventually_not)
              ","
              (Tactic.simpLemma [] [] `eventually_le)]
             "]"]
            [])])))
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
         [(Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `lt_iff_le_not_le)
             ","
             (Tactic.simpLemma [] [] `eventually_and)
             ","
             (Tactic.simpLemma [] [] `coe_le)
             ","
             (Tactic.simpLemma [] [] `eventually_not)
             ","
             (Tactic.simpLemma [] [] `eventually_le)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `lt_iff_le_not_le)
         ","
         (Tactic.simpLemma [] [] `eventually_and)
         ","
         (Tactic.simpLemma [] [] `coe_le)
         ","
         (Tactic.simpLemma [] [] `eventually_not)
         ","
         (Tactic.simpLemma [] [] `eventually_le)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eventually_le
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eventually_not
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_le
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eventually_and
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lt_iff_le_not_le
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_<_»
        (Term.typeAscription
         "("
         `f
         ":"
         [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
         ")")
        "<"
        `g)
       "↔"
       (Filter.Order.Filter.FilterProduct.«term∀*_,_»
        "∀*"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
        ", "
        («term_<_» (Term.app `f [`x]) "<" (Term.app `g [`x]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Order.Filter.FilterProduct.«term∀*_,_»
       "∀*"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
       ", "
       («term_<_» (Term.app `f [`x]) "<" (Term.app `g [`x])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Order.Filter.FilterProduct.«term∀*_,_»', expected 'Filter.Order.Filter.FilterProduct.term∀*_,_._@.Order.Filter.FilterProduct._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  coe_lt
  [ Preorder β ] { f g : α → β } : ( f : β* ) < g ↔ ∀* x , f x < g x
  := by simp only [ lt_iff_le_not_le , eventually_and , coe_le , eventually_not , eventually_le ]
#align filter.germ.coe_lt Filter.Germ.coe_lt

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `coe_pos [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `Preorder [`β]) "]")
        (Term.instBinder "[" [] (Term.app `Zero [`β]) "]")
        (Term.implicitBinder "{" [`f] [":" (Term.arrow `α "→" `β)] "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_<_»
          (num "0")
          "<"
          (Term.typeAscription
           "("
           `f
           ":"
           [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
           ")"))
         "↔"
         (Filter.Order.Filter.FilterProduct.«term∀*_,_»
          "∀*"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
          ", "
          («term_<_» (num "0") "<" (Term.app `f [`x]))))))
      (Command.declValSimple ":=" `coe_lt [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_lt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_<_»
        (num "0")
        "<"
        (Term.typeAscription
         "("
         `f
         ":"
         [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
         ")"))
       "↔"
       (Filter.Order.Filter.FilterProduct.«term∀*_,_»
        "∀*"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
        ", "
        («term_<_» (num "0") "<" (Term.app `f [`x]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Order.Filter.FilterProduct.«term∀*_,_»
       "∀*"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
       ", "
       («term_<_» (num "0") "<" (Term.app `f [`x])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Order.Filter.FilterProduct.«term∀*_,_»', expected 'Filter.Order.Filter.FilterProduct.term∀*_,_._@.Order.Filter.FilterProduct._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem coe_pos [ Preorder β ] [ Zero β ] { f : α → β } : 0 < ( f : β* ) ↔ ∀* x , 0 < f x := coe_lt
#align filter.germ.coe_pos Filter.Germ.coe_pos

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `const_lt [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `Preorder [`β]) "]")
        (Term.implicitBinder "{" [`x `y] [":" `β] "}")]
       (Term.typeSpec
        ":"
        (Term.arrow
         («term_≤_» `x "≤" `y)
         "→"
         («term_≤_»
          (Term.typeAscription
           "("
           (coeNotation "↑" `x)
           ":"
           [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
           ")")
          "≤"
          (coeNotation "↑" `y)))))
      (Command.declValSimple ":=" `lift_rel_const [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lift_rel_const
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       («term_≤_» `x "≤" `y)
       "→"
       («term_≤_»
        (Term.typeAscription
         "("
         (coeNotation "↑" `x)
         ":"
         [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
         ")")
        "≤"
        (coeNotation "↑" `y)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Term.typeAscription
        "("
        (coeNotation "↑" `x)
        ":"
        [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
        ")")
       "≤"
       (coeNotation "↑" `y))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (coeNotation "↑" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (some 1024,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription
       "("
       (coeNotation "↑" `x)
       ":"
       [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem const_lt [ Preorder β ] { x y : β } : x ≤ y → ( ↑ x : β* ) ≤ ↑ y := lift_rel_const
#align filter.germ.const_lt Filter.Germ.const_lt

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `const_lt_iff [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `Preorder [`β]) "]")
        (Term.implicitBinder "{" [`x `y] [":" `β] "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_<_»
          (Term.typeAscription
           "("
           (coeNotation "↑" `x)
           ":"
           [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
           ")")
          "<"
          (coeNotation "↑" `y))
         "↔"
         («term_<_» `x "<" `y))))
      (Command.declValSimple
       ":="
       (Term.app (Term.proj `coe_lt "." `trans) [`lift_rel_const_iff])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `coe_lt "." `trans) [`lift_rel_const_iff])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lift_rel_const_iff
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `coe_lt "." `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `coe_lt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_<_»
        (Term.typeAscription
         "("
         (coeNotation "↑" `x)
         ":"
         [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
         ")")
        "<"
        (coeNotation "↑" `y))
       "↔"
       («term_<_» `x "<" `y))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» `x "<" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      («term_<_»
       (Term.typeAscription
        "("
        (coeNotation "↑" `x)
        ":"
        [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
        ")")
       "<"
       (coeNotation "↑" `y))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (coeNotation "↑" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (some 1024,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription
       "("
       (coeNotation "↑" `x)
       ":"
       [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  const_lt_iff
  [ Preorder β ] { x y : β } : ( ↑ x : β* ) < ↑ y ↔ x < y
  := coe_lt . trans lift_rel_const_iff
#align filter.germ.const_lt_iff Filter.Germ.const_lt_iff

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `lt_def [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `Preorder [`β]) "]")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.typeAscription
          "("
          (Term.paren "(" («term_<_» (Term.cdot "·") "<" (Term.cdot "·")) ")")
          ":"
          [(Term.arrow
            (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
            "→"
            (Term.arrow
             (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
             "→"
             (Term.prop "Prop")))]
          ")")
         "="
         (Term.app
          `LiftRel
          [(Term.paren "(" («term_<_» (Term.cdot "·") "<" (Term.cdot "·")) ")")]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.Ext.«tacticExt___:_»
            "ext"
            [(Std.Tactic.RCases.rintroPat.binder
              "("
              [(Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `f)])
                   [])]
                 "⟩"))
               (Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g)])
                   [])]
                 "⟩"))]
              []
              ")")]
            [])
           []
           (Tactic.exact "exact" `coe_lt)])))
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
         [(Std.Tactic.Ext.«tacticExt___:_»
           "ext"
           [(Std.Tactic.RCases.rintroPat.binder
             "("
             [(Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `f)])
                  [])]
                "⟩"))
              (Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g)])
                  [])]
                "⟩"))]
             []
             ")")]
           [])
          []
          (Tactic.exact "exact" `coe_lt)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `coe_lt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_lt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_»
       "ext"
       [(Std.Tactic.RCases.rintroPat.binder
         "("
         [(Std.Tactic.RCases.rintroPat.one
           (Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `f)])
              [])]
            "⟩"))
          (Std.Tactic.RCases.rintroPat.one
           (Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `g)])
              [])]
            "⟩"))]
         []
         ")")]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.typeAscription
        "("
        (Term.paren "(" («term_<_» (Term.cdot "·") "<" (Term.cdot "·")) ")")
        ":"
        [(Term.arrow
          (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
          "→"
          (Term.arrow
           (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
           "→"
           (Term.prop "Prop")))]
        ")")
       "="
       (Term.app `LiftRel [(Term.paren "(" («term_<_» (Term.cdot "·") "<" (Term.cdot "·")) ")")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `LiftRel [(Term.paren "(" («term_<_» (Term.cdot "·") "<" (Term.cdot "·")) ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.paren "(" («term_<_» (Term.cdot "·") "<" (Term.cdot "·")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» (Term.cdot "·") "<" (Term.cdot "·"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.cdot "·")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.cdot "·")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `LiftRel
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription
       "("
       (Term.paren "(" («term_<_» (Term.cdot "·") "<" (Term.cdot "·")) ")")
       ":"
       [(Term.arrow
         (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
         "→"
         (Term.arrow
          (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
          "→"
          (Term.prop "Prop")))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
       "→"
       (Term.arrow (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*") "→" (Term.prop "Prop")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*") "→" (Term.prop "Prop"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.prop "Prop")
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  lt_def
  [ Preorder β ] : ( ( · < · ) : β* → β* → Prop ) = LiftRel ( · < · )
  := by ext ( ⟨ f ⟩ ⟨ g ⟩ ) exact coe_lt
#align filter.germ.lt_def Filter.Germ.lt_def

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `HasSup [`β]) "]")]
       (Term.typeSpec
        ":"
        (Term.app `HasSup [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.app
          `map₂
          [(Term.paren "(" (Order.Basic.«term_⊔_» (Term.cdot "·") " ⊔ " (Term.cdot "·")) ")")])]
        "⟩")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app
         `map₂
         [(Term.paren "(" (Order.Basic.«term_⊔_» (Term.cdot "·") " ⊔ " (Term.cdot "·")) ")")])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `map₂
       [(Term.paren "(" (Order.Basic.«term_⊔_» (Term.cdot "·") " ⊔ " (Term.cdot "·")) ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.paren "(" (Order.Basic.«term_⊔_» (Term.cdot "·") " ⊔ " (Term.cdot "·")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.Basic.«term_⊔_» (Term.cdot "·") " ⊔ " (Term.cdot "·"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.cdot "·")
[PrettyPrinter.parenthesize] ...precedences are 69 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 68, term))
      (Term.cdot "·")
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 68, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 68, (some 69, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `map₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `HasSup [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance [ HasSup β ] : HasSup β* := ⟨ map₂ ( · ⊔ · ) ⟩

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `HasInf [`β]) "]")]
       (Term.typeSpec
        ":"
        (Term.app `HasInf [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.app
          `map₂
          [(Term.paren "(" (Order.Basic.«term_⊓_» (Term.cdot "·") " ⊓ " (Term.cdot "·")) ")")])]
        "⟩")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app
         `map₂
         [(Term.paren "(" (Order.Basic.«term_⊓_» (Term.cdot "·") " ⊓ " (Term.cdot "·")) ")")])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `map₂
       [(Term.paren "(" (Order.Basic.«term_⊓_» (Term.cdot "·") " ⊓ " (Term.cdot "·")) ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.paren "(" (Order.Basic.«term_⊓_» (Term.cdot "·") " ⊓ " (Term.cdot "·")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.Basic.«term_⊓_» (Term.cdot "·") " ⊓ " (Term.cdot "·"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.cdot "·")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 69, term))
      (Term.cdot "·")
[PrettyPrinter.parenthesize] ...precedences are 69 >? 1024, (none, [anonymous]) <=? (some 69, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 69, (some 70, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `map₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `HasInf [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance [ HasInf β ] : HasInf β* := ⟨ map₂ ( · ⊓ · ) ⟩

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes
        "@["
        [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))
         ","
         (Term.attrInstance
          (Term.attrKind [])
          (Std.Tactic.NormCast.Attr.norm_cast "norm_cast" [] []))]
        "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `const_sup [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `HasSup [`β]) "]")
        (Term.explicitBinder "(" [`a `b] [":" `β] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (coeNotation "↑" (Order.Basic.«term_⊔_» `a " ⊔ " `b))
         "="
         (Term.typeAscription
          "("
          (Order.Basic.«term_⊔_» (coeNotation "↑" `a) " ⊔ " (coeNotation "↑" `b))
          ":"
          [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
          ")"))))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (coeNotation "↑" (Order.Basic.«term_⊔_» `a " ⊔ " `b))
       "="
       (Term.typeAscription
        "("
        (Order.Basic.«term_⊔_» (coeNotation "↑" `a) " ⊔ " (coeNotation "↑" `b))
        ":"
        [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Order.Basic.«term_⊔_» (coeNotation "↑" `a) " ⊔ " (coeNotation "↑" `b))
       ":"
       [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp , norm_cast ]
  theorem const_sup [ HasSup β ] ( a b : β ) : ↑ a ⊔ b = ( ↑ a ⊔ ↑ b : β* ) := rfl
#align filter.germ.const_sup Filter.Germ.const_sup

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes
        "@["
        [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))
         ","
         (Term.attrInstance
          (Term.attrKind [])
          (Std.Tactic.NormCast.Attr.norm_cast "norm_cast" [] []))]
        "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `const_inf [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `HasInf [`β]) "]")
        (Term.explicitBinder "(" [`a `b] [":" `β] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (coeNotation "↑" (Order.Basic.«term_⊓_» `a " ⊓ " `b))
         "="
         (Term.typeAscription
          "("
          (Order.Basic.«term_⊓_» (coeNotation "↑" `a) " ⊓ " (coeNotation "↑" `b))
          ":"
          [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
          ")"))))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (coeNotation "↑" (Order.Basic.«term_⊓_» `a " ⊓ " `b))
       "="
       (Term.typeAscription
        "("
        (Order.Basic.«term_⊓_» (coeNotation "↑" `a) " ⊓ " (coeNotation "↑" `b))
        ":"
        [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Order.Basic.«term_⊓_» (coeNotation "↑" `a) " ⊓ " (coeNotation "↑" `b))
       ":"
       [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp , norm_cast ]
  theorem const_inf [ HasInf β ] ( a b : β ) : ↑ a ⊓ b = ( ↑ a ⊓ ↑ b : β* ) := rfl
#align filter.germ.const_inf Filter.Germ.const_inf

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `SemilatticeSup [`β]) "]")]
       (Term.typeSpec
        ":"
        (Term.app `SemilatticeSup [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])))
      (Command.declValSimple
       ":="
       (Term.structInst
        "{"
        [[`Germ.partialOrder] "with"]
        [(Term.structInstField
          (Term.structInstLVal `sup [])
          ":="
          (Term.paren "(" (Order.Basic.«term_⊔_» (Term.cdot "·") " ⊔ " (Term.cdot "·")) ")"))
         []
         (Term.structInstField
          (Term.structInstLVal `le_sup_left [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`f `g]
            []
            "=>"
            (Term.app
             (Term.app `induction_on₂ [`f `g])
             [(Term.fun
               "fun"
               (Term.basicFun
                [`f `g]
                []
                "=>"
                (Term.app
                 `eventually_of_forall
                 [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `le_sup_left))])))]))))
         []
         (Term.structInstField
          (Term.structInstLVal `le_sup_right [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`f `g]
            []
            "=>"
            (Term.app
             (Term.app `induction_on₂ [`f `g])
             [(Term.fun
               "fun"
               (Term.basicFun
                [`f `g]
                []
                "=>"
                (Term.app
                 `eventually_of_forall
                 [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `le_sup_right))])))]))))
         []
         (Term.structInstField
          (Term.structInstLVal `sup_le [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`f₁ `f₂ `g]
            []
            "=>"
            (Term.app
             (Term.app `induction_on₃ [`f₁ `f₂ `g])
             [(Term.fun
               "fun"
               (Term.basicFun
                [`f₁ `f₂ `g `h₁ `h₂]
                []
                "=>"
                («term_<|_»
                 (Term.proj `h₂ "." `mp)
                 "<|"
                 (Term.app
                  (Term.proj `h₁ "." `mono)
                  [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `sup_le))]))))]))))]
        (Term.optEllipsis [])
        []
        "}")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       [[`Germ.partialOrder] "with"]
       [(Term.structInstField
         (Term.structInstLVal `sup [])
         ":="
         (Term.paren "(" (Order.Basic.«term_⊔_» (Term.cdot "·") " ⊔ " (Term.cdot "·")) ")"))
        []
        (Term.structInstField
         (Term.structInstLVal `le_sup_left [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`f `g]
           []
           "=>"
           (Term.app
            (Term.app `induction_on₂ [`f `g])
            [(Term.fun
              "fun"
              (Term.basicFun
               [`f `g]
               []
               "=>"
               (Term.app
                `eventually_of_forall
                [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `le_sup_left))])))]))))
        []
        (Term.structInstField
         (Term.structInstLVal `le_sup_right [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`f `g]
           []
           "=>"
           (Term.app
            (Term.app `induction_on₂ [`f `g])
            [(Term.fun
              "fun"
              (Term.basicFun
               [`f `g]
               []
               "=>"
               (Term.app
                `eventually_of_forall
                [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `le_sup_right))])))]))))
        []
        (Term.structInstField
         (Term.structInstLVal `sup_le [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`f₁ `f₂ `g]
           []
           "=>"
           (Term.app
            (Term.app `induction_on₃ [`f₁ `f₂ `g])
            [(Term.fun
              "fun"
              (Term.basicFun
               [`f₁ `f₂ `g `h₁ `h₂]
               []
               "=>"
               («term_<|_»
                (Term.proj `h₂ "." `mp)
                "<|"
                (Term.app
                 (Term.proj `h₁ "." `mono)
                 [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `sup_le))]))))]))))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f₁ `f₂ `g]
        []
        "=>"
        (Term.app
         (Term.app `induction_on₃ [`f₁ `f₂ `g])
         [(Term.fun
           "fun"
           (Term.basicFun
            [`f₁ `f₂ `g `h₁ `h₂]
            []
            "=>"
            («term_<|_»
             (Term.proj `h₂ "." `mp)
             "<|"
             (Term.app
              (Term.proj `h₁ "." `mono)
              [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `sup_le))]))))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app `induction_on₃ [`f₁ `f₂ `g])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`f₁ `f₂ `g `h₁ `h₂]
          []
          "=>"
          («term_<|_»
           (Term.proj `h₂ "." `mp)
           "<|"
           (Term.app
            (Term.proj `h₁ "." `mono)
            [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `sup_le))]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f₁ `f₂ `g `h₁ `h₂]
        []
        "=>"
        («term_<|_»
         (Term.proj `h₂ "." `mp)
         "<|"
         (Term.app
          (Term.proj `h₁ "." `mono)
          [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `sup_le))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj `h₂ "." `mp)
       "<|"
       (Term.app (Term.proj `h₁ "." `mono) [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `sup_le))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `h₁ "." `mono) [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `sup_le))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`x] [] "=>" `sup_le))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sup_le
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `h₁ "." `mono)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `h₂ "." `mp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app `induction_on₃ [`f₁ `f₂ `g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `induction_on₃
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `induction_on₃ [`f₁ `f₂ `g])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f `g]
        []
        "=>"
        (Term.app
         (Term.app `induction_on₂ [`f `g])
         [(Term.fun
           "fun"
           (Term.basicFun
            [`f `g]
            []
            "=>"
            (Term.app
             `eventually_of_forall
             [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `le_sup_right))])))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app `induction_on₂ [`f `g])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`f `g]
          []
          "=>"
          (Term.app
           `eventually_of_forall
           [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `le_sup_right))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f `g]
        []
        "=>"
        (Term.app
         `eventually_of_forall
         [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `le_sup_right))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `eventually_of_forall [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `le_sup_right))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`x] [] "=>" `le_sup_right))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `le_sup_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eventually_of_forall
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app `induction_on₂ [`f `g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `induction_on₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `induction_on₂ [`f `g]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f `g]
        []
        "=>"
        (Term.app
         (Term.app `induction_on₂ [`f `g])
         [(Term.fun
           "fun"
           (Term.basicFun
            [`f `g]
            []
            "=>"
            (Term.app
             `eventually_of_forall
             [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `le_sup_left))])))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app `induction_on₂ [`f `g])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`f `g]
          []
          "=>"
          (Term.app
           `eventually_of_forall
           [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `le_sup_left))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f `g]
        []
        "=>"
        (Term.app
         `eventually_of_forall
         [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `le_sup_left))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `eventually_of_forall [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `le_sup_left))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`x] [] "=>" `le_sup_left))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `le_sup_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eventually_of_forall
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app `induction_on₂ [`f `g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `induction_on₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `induction_on₂ [`f `g]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.paren "(" (Order.Basic.«term_⊔_» (Term.cdot "·") " ⊔ " (Term.cdot "·")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.Basic.«term_⊔_» (Term.cdot "·") " ⊔ " (Term.cdot "·"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.cdot "·")
[PrettyPrinter.parenthesize] ...precedences are 69 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 68, term))
      (Term.cdot "·")
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1024, (none, [anonymous]) <=? (some 68, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 68, (some 69, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.partialOrder
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `SemilatticeSup [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  [ SemilatticeSup β ] : SemilatticeSup β*
  :=
    {
      Germ.partialOrder with
      sup := ( · ⊔ · )
        le_sup_left
          :=
          fun f g => induction_on₂ f g fun f g => eventually_of_forall fun x => le_sup_left
        le_sup_right
          :=
          fun f g => induction_on₂ f g fun f g => eventually_of_forall fun x => le_sup_right
        sup_le
          :=
          fun
            f₁ f₂ g
              =>
              induction_on₃ f₁ f₂ g fun f₁ f₂ g h₁ h₂ => h₂ . mp <| h₁ . mono fun x => sup_le
      }

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `SemilatticeInf [`β]) "]")]
       (Term.typeSpec
        ":"
        (Term.app `SemilatticeInf [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])))
      (Command.declValSimple
       ":="
       (Term.structInst
        "{"
        [[`Germ.partialOrder] "with"]
        [(Term.structInstField
          (Term.structInstLVal `inf [])
          ":="
          (Term.paren "(" (Order.Basic.«term_⊓_» (Term.cdot "·") " ⊓ " (Term.cdot "·")) ")"))
         []
         (Term.structInstField
          (Term.structInstLVal `inf_le_left [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`f `g]
            []
            "=>"
            (Term.app
             (Term.app `induction_on₂ [`f `g])
             [(Term.fun
               "fun"
               (Term.basicFun
                [`f `g]
                []
                "=>"
                (Term.app
                 `eventually_of_forall
                 [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `inf_le_left))])))]))))
         []
         (Term.structInstField
          (Term.structInstLVal `inf_le_right [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`f `g]
            []
            "=>"
            (Term.app
             (Term.app `induction_on₂ [`f `g])
             [(Term.fun
               "fun"
               (Term.basicFun
                [`f `g]
                []
                "=>"
                (Term.app
                 `eventually_of_forall
                 [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `inf_le_right))])))]))))
         []
         (Term.structInstField
          (Term.structInstLVal `le_inf [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`f₁ `f₂ `g]
            []
            "=>"
            (Term.app
             (Term.app `induction_on₃ [`f₁ `f₂ `g])
             [(Term.fun
               "fun"
               (Term.basicFun
                [`f₁ `f₂ `g `h₁ `h₂]
                []
                "=>"
                («term_<|_»
                 (Term.proj `h₂ "." `mp)
                 "<|"
                 (Term.app
                  (Term.proj `h₁ "." `mono)
                  [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `le_inf))]))))]))))]
        (Term.optEllipsis [])
        []
        "}")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       [[`Germ.partialOrder] "with"]
       [(Term.structInstField
         (Term.structInstLVal `inf [])
         ":="
         (Term.paren "(" (Order.Basic.«term_⊓_» (Term.cdot "·") " ⊓ " (Term.cdot "·")) ")"))
        []
        (Term.structInstField
         (Term.structInstLVal `inf_le_left [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`f `g]
           []
           "=>"
           (Term.app
            (Term.app `induction_on₂ [`f `g])
            [(Term.fun
              "fun"
              (Term.basicFun
               [`f `g]
               []
               "=>"
               (Term.app
                `eventually_of_forall
                [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `inf_le_left))])))]))))
        []
        (Term.structInstField
         (Term.structInstLVal `inf_le_right [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`f `g]
           []
           "=>"
           (Term.app
            (Term.app `induction_on₂ [`f `g])
            [(Term.fun
              "fun"
              (Term.basicFun
               [`f `g]
               []
               "=>"
               (Term.app
                `eventually_of_forall
                [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `inf_le_right))])))]))))
        []
        (Term.structInstField
         (Term.structInstLVal `le_inf [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`f₁ `f₂ `g]
           []
           "=>"
           (Term.app
            (Term.app `induction_on₃ [`f₁ `f₂ `g])
            [(Term.fun
              "fun"
              (Term.basicFun
               [`f₁ `f₂ `g `h₁ `h₂]
               []
               "=>"
               («term_<|_»
                (Term.proj `h₂ "." `mp)
                "<|"
                (Term.app
                 (Term.proj `h₁ "." `mono)
                 [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `le_inf))]))))]))))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f₁ `f₂ `g]
        []
        "=>"
        (Term.app
         (Term.app `induction_on₃ [`f₁ `f₂ `g])
         [(Term.fun
           "fun"
           (Term.basicFun
            [`f₁ `f₂ `g `h₁ `h₂]
            []
            "=>"
            («term_<|_»
             (Term.proj `h₂ "." `mp)
             "<|"
             (Term.app
              (Term.proj `h₁ "." `mono)
              [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `le_inf))]))))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app `induction_on₃ [`f₁ `f₂ `g])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`f₁ `f₂ `g `h₁ `h₂]
          []
          "=>"
          («term_<|_»
           (Term.proj `h₂ "." `mp)
           "<|"
           (Term.app
            (Term.proj `h₁ "." `mono)
            [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `le_inf))]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f₁ `f₂ `g `h₁ `h₂]
        []
        "=>"
        («term_<|_»
         (Term.proj `h₂ "." `mp)
         "<|"
         (Term.app
          (Term.proj `h₁ "." `mono)
          [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `le_inf))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj `h₂ "." `mp)
       "<|"
       (Term.app (Term.proj `h₁ "." `mono) [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `le_inf))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `h₁ "." `mono) [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `le_inf))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`x] [] "=>" `le_inf))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `le_inf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `h₁ "." `mono)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `h₂ "." `mp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app `induction_on₃ [`f₁ `f₂ `g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `induction_on₃
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `induction_on₃ [`f₁ `f₂ `g])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f `g]
        []
        "=>"
        (Term.app
         (Term.app `induction_on₂ [`f `g])
         [(Term.fun
           "fun"
           (Term.basicFun
            [`f `g]
            []
            "=>"
            (Term.app
             `eventually_of_forall
             [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `inf_le_right))])))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app `induction_on₂ [`f `g])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`f `g]
          []
          "=>"
          (Term.app
           `eventually_of_forall
           [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `inf_le_right))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f `g]
        []
        "=>"
        (Term.app
         `eventually_of_forall
         [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `inf_le_right))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `eventually_of_forall [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `inf_le_right))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`x] [] "=>" `inf_le_right))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inf_le_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eventually_of_forall
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app `induction_on₂ [`f `g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `induction_on₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `induction_on₂ [`f `g]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f `g]
        []
        "=>"
        (Term.app
         (Term.app `induction_on₂ [`f `g])
         [(Term.fun
           "fun"
           (Term.basicFun
            [`f `g]
            []
            "=>"
            (Term.app
             `eventually_of_forall
             [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `inf_le_left))])))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app `induction_on₂ [`f `g])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`f `g]
          []
          "=>"
          (Term.app
           `eventually_of_forall
           [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `inf_le_left))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f `g]
        []
        "=>"
        (Term.app
         `eventually_of_forall
         [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `inf_le_left))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `eventually_of_forall [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `inf_le_left))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`x] [] "=>" `inf_le_left))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inf_le_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eventually_of_forall
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app `induction_on₂ [`f `g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `induction_on₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `induction_on₂ [`f `g]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.paren "(" (Order.Basic.«term_⊓_» (Term.cdot "·") " ⊓ " (Term.cdot "·")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.Basic.«term_⊓_» (Term.cdot "·") " ⊓ " (Term.cdot "·"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.cdot "·")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 69, term))
      (Term.cdot "·")
[PrettyPrinter.parenthesize] ...precedences are 69 >? 1024, (none, [anonymous]) <=? (some 69, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 69, (some 70, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.partialOrder
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `SemilatticeInf [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  [ SemilatticeInf β ] : SemilatticeInf β*
  :=
    {
      Germ.partialOrder with
      inf := ( · ⊓ · )
        inf_le_left
          :=
          fun f g => induction_on₂ f g fun f g => eventually_of_forall fun x => inf_le_left
        inf_le_right
          :=
          fun f g => induction_on₂ f g fun f g => eventually_of_forall fun x => inf_le_right
        le_inf
          :=
          fun
            f₁ f₂ g
              =>
              induction_on₃ f₁ f₂ g fun f₁ f₂ g h₁ h₂ => h₂ . mp <| h₁ . mono fun x => le_inf
      }

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `Lattice [`β]) "]")]
       (Term.typeSpec
        ":"
        (Term.app `Lattice [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])))
      (Command.declValSimple
       ":="
       (Term.structInst
        "{"
        [[`Germ.semilatticeSup "," `Germ.semilatticeInf] "with"]
        []
        (Term.optEllipsis [])
        []
        "}")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       [[`Germ.semilatticeSup "," `Germ.semilatticeInf] "with"]
       []
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.semilatticeInf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.semilatticeSup
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `Lattice [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance [ Lattice β ] : Lattice β* := { Germ.semilatticeSup , Germ.semilatticeInf with }

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `DistribLattice [`β]) "]")]
       (Term.typeSpec
        ":"
        (Term.app `DistribLattice [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])))
      (Command.declValSimple
       ":="
       (Term.structInst
        "{"
        [[`Germ.semilatticeSup "," `Germ.semilatticeInf] "with"]
        [(Term.structInstField
          (Term.structInstLVal `le_sup_inf [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`f `g `h]
            []
            "=>"
            (Term.app
             (Term.app `induction_on₃ [`f `g `h])
             [(Term.fun
               "fun"
               (Term.basicFun
                [`f `g `h]
                []
                "=>"
                (Term.app
                 `eventually_of_forall
                 [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `le_sup_inf))])))]))))]
        (Term.optEllipsis [])
        []
        "}")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       [[`Germ.semilatticeSup "," `Germ.semilatticeInf] "with"]
       [(Term.structInstField
         (Term.structInstLVal `le_sup_inf [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`f `g `h]
           []
           "=>"
           (Term.app
            (Term.app `induction_on₃ [`f `g `h])
            [(Term.fun
              "fun"
              (Term.basicFun
               [`f `g `h]
               []
               "=>"
               (Term.app
                `eventually_of_forall
                [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `le_sup_inf))])))]))))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f `g `h]
        []
        "=>"
        (Term.app
         (Term.app `induction_on₃ [`f `g `h])
         [(Term.fun
           "fun"
           (Term.basicFun
            [`f `g `h]
            []
            "=>"
            (Term.app
             `eventually_of_forall
             [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `le_sup_inf))])))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app `induction_on₃ [`f `g `h])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`f `g `h]
          []
          "=>"
          (Term.app
           `eventually_of_forall
           [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `le_sup_inf))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f `g `h]
        []
        "=>"
        (Term.app
         `eventually_of_forall
         [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `le_sup_inf))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `eventually_of_forall
       [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `le_sup_inf))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `le_sup_inf))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `le_sup_inf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eventually_of_forall
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
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
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app `induction_on₃ [`f `g `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `induction_on₃
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `induction_on₃ [`f `g `h])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
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
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.semilatticeInf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.semilatticeSup
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `DistribLattice [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  [ DistribLattice β ] : DistribLattice β*
  :=
    {
      Germ.semilatticeSup , Germ.semilatticeInf with
      le_sup_inf
        :=
        fun f g h => induction_on₃ f g h fun f g h => eventually_of_forall fun _ => le_sup_inf
      }

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `LE [`β]) "]")
        (Term.instBinder
         "["
         []
         (Term.app
          `IsTotal
          [`β (Term.paren "(" («term_≤_» (Term.cdot "·") "≤" (Term.cdot "·")) ")")])
         "]")]
       (Term.typeSpec
        ":"
        (Term.app
         `IsTotal
         [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
          (Term.paren "(" («term_≤_» (Term.cdot "·") "≤" (Term.cdot "·")) ")")])))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.fun
          "fun"
          (Term.basicFun
           [`f `g]
           []
           "=>"
           (Term.app
            (Term.app `induction_on₂ [`f `g])
            [(Term.fun
              "fun"
              (Term.basicFun
               [`f `g]
               []
               "=>"
               («term_<|_»
                (Term.proj `eventually_or "." (fieldIdx "1"))
                "<|"
                (Term.app
                 `eventually_of_forall
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [`x]
                    []
                    "=>"
                    (Term.app
                     `total_of
                     [(Term.hole "_") (Term.hole "_") (Term.hole "_")])))]))))])))]
        "⟩")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [`f `g]
          []
          "=>"
          (Term.app
           (Term.app `induction_on₂ [`f `g])
           [(Term.fun
             "fun"
             (Term.basicFun
              [`f `g]
              []
              "=>"
              («term_<|_»
               (Term.proj `eventually_or "." (fieldIdx "1"))
               "<|"
               (Term.app
                `eventually_of_forall
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [`x]
                   []
                   "=>"
                   (Term.app
                    `total_of
                    [(Term.hole "_") (Term.hole "_") (Term.hole "_")])))]))))])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f `g]
        []
        "=>"
        (Term.app
         (Term.app `induction_on₂ [`f `g])
         [(Term.fun
           "fun"
           (Term.basicFun
            [`f `g]
            []
            "=>"
            («term_<|_»
             (Term.proj `eventually_or "." (fieldIdx "1"))
             "<|"
             (Term.app
              `eventually_of_forall
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`x]
                 []
                 "=>"
                 (Term.app `total_of [(Term.hole "_") (Term.hole "_") (Term.hole "_")])))]))))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app `induction_on₂ [`f `g])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`f `g]
          []
          "=>"
          («term_<|_»
           (Term.proj `eventually_or "." (fieldIdx "1"))
           "<|"
           (Term.app
            `eventually_of_forall
            [(Term.fun
              "fun"
              (Term.basicFun
               [`x]
               []
               "=>"
               (Term.app `total_of [(Term.hole "_") (Term.hole "_") (Term.hole "_")])))]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f `g]
        []
        "=>"
        («term_<|_»
         (Term.proj `eventually_or "." (fieldIdx "1"))
         "<|"
         (Term.app
          `eventually_of_forall
          [(Term.fun
            "fun"
            (Term.basicFun
             [`x]
             []
             "=>"
             (Term.app `total_of [(Term.hole "_") (Term.hole "_") (Term.hole "_")])))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj `eventually_or "." (fieldIdx "1"))
       "<|"
       (Term.app
        `eventually_of_forall
        [(Term.fun
          "fun"
          (Term.basicFun
           [`x]
           []
           "=>"
           (Term.app `total_of [(Term.hole "_") (Term.hole "_") (Term.hole "_")])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `eventually_of_forall
       [(Term.fun
         "fun"
         (Term.basicFun
          [`x]
          []
          "=>"
          (Term.app `total_of [(Term.hole "_") (Term.hole "_") (Term.hole "_")])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (Term.app `total_of [(Term.hole "_") (Term.hole "_") (Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `total_of [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `total_of
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eventually_of_forall
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `eventually_or "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `eventually_or
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app `induction_on₂ [`f `g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `induction_on₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `induction_on₂ [`f `g]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `IsTotal
       [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
        (Term.paren "(" («term_≤_» (Term.cdot "·") "≤" (Term.cdot "·")) ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.paren "(" («term_≤_» (Term.cdot "·") "≤" (Term.cdot "·")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_» (Term.cdot "·") "≤" (Term.cdot "·"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.cdot "·")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.cdot "·")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  [ LE β ] [ IsTotal β ( · ≤ · ) ] : IsTotal β* ( · ≤ · )
  :=
    ⟨
      fun
        f g
          =>
          induction_on₂ f g
            fun f g => eventually_or . 1 <| eventually_of_forall fun x => total_of _ _ _
      ⟩

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "If `φ` is an ultrafilter then the ultraproduct is a linear order. -/")]
      []
      []
      [(Command.noncomputable "noncomputable")]
      []
      [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `LinearOrder [`β]) "]")]
       (Term.typeSpec
        ":"
        (Term.app `LinearOrder [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])))
      (Command.declValSimple ":=" (Term.app `Lattice.toLinearOrder [(Term.hole "_")]) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Lattice.toLinearOrder [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Lattice.toLinearOrder
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `LinearOrder [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- If `φ` is an ultrafilter then the ultraproduct is a linear order. -/ noncomputable
  instance [ LinearOrder β ] : LinearOrder β* := Lattice.toLinearOrder _

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes
        "@["
        [(Term.attrInstance
          (Term.attrKind [])
          (to_additive "to_additive" [] [] (to_additiveRest [] [] [])))]
        "]")]
      []
      []
      []
      [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `OrderedCommMonoid [`β]) "]")]
       (Term.typeSpec
        ":"
        (Term.app `OrderedCommMonoid [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])))
      (Command.declValSimple
       ":="
       (Term.structInst
        "{"
        [[`Germ.partialOrder "," `Germ.commMonoid] "with"]
        [(Term.structInstField
          (Term.structInstLVal `mul_le_mul_left [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`f `g]
            []
            "=>"
            (Term.app
             (Term.app `induction_on₂ [`f `g])
             [(Term.fun
               "fun"
               (Term.basicFun
                [`f `g `H `h]
                []
                "=>"
                (Term.app
                 (Term.app `induction_on [`h])
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [`h]
                    []
                    "=>"
                    (Term.app
                     (Term.proj `H "." `mono)
                     [(Term.fun
                       "fun"
                       (Term.basicFun
                        [`x `H]
                        []
                        "=>"
                        (Term.app `mul_le_mul_left' [`H (Term.hole "_")])))])))])))]))))]
        (Term.optEllipsis [])
        []
        "}")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       [[`Germ.partialOrder "," `Germ.commMonoid] "with"]
       [(Term.structInstField
         (Term.structInstLVal `mul_le_mul_left [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`f `g]
           []
           "=>"
           (Term.app
            (Term.app `induction_on₂ [`f `g])
            [(Term.fun
              "fun"
              (Term.basicFun
               [`f `g `H `h]
               []
               "=>"
               (Term.app
                (Term.app `induction_on [`h])
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [`h]
                   []
                   "=>"
                   (Term.app
                    (Term.proj `H "." `mono)
                    [(Term.fun
                      "fun"
                      (Term.basicFun
                       [`x `H]
                       []
                       "=>"
                       (Term.app `mul_le_mul_left' [`H (Term.hole "_")])))])))])))]))))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f `g]
        []
        "=>"
        (Term.app
         (Term.app `induction_on₂ [`f `g])
         [(Term.fun
           "fun"
           (Term.basicFun
            [`f `g `H `h]
            []
            "=>"
            (Term.app
             (Term.app `induction_on [`h])
             [(Term.fun
               "fun"
               (Term.basicFun
                [`h]
                []
                "=>"
                (Term.app
                 (Term.proj `H "." `mono)
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [`x `H]
                    []
                    "=>"
                    (Term.app `mul_le_mul_left' [`H (Term.hole "_")])))])))])))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app `induction_on₂ [`f `g])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`f `g `H `h]
          []
          "=>"
          (Term.app
           (Term.app `induction_on [`h])
           [(Term.fun
             "fun"
             (Term.basicFun
              [`h]
              []
              "=>"
              (Term.app
               (Term.proj `H "." `mono)
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [`x `H]
                  []
                  "=>"
                  (Term.app `mul_le_mul_left' [`H (Term.hole "_")])))])))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f `g `H `h]
        []
        "=>"
        (Term.app
         (Term.app `induction_on [`h])
         [(Term.fun
           "fun"
           (Term.basicFun
            [`h]
            []
            "=>"
            (Term.app
             (Term.proj `H "." `mono)
             [(Term.fun
               "fun"
               (Term.basicFun
                [`x `H]
                []
                "=>"
                (Term.app `mul_le_mul_left' [`H (Term.hole "_")])))])))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app `induction_on [`h])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`h]
          []
          "=>"
          (Term.app
           (Term.proj `H "." `mono)
           [(Term.fun
             "fun"
             (Term.basicFun
              [`x `H]
              []
              "=>"
              (Term.app `mul_le_mul_left' [`H (Term.hole "_")])))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`h]
        []
        "=>"
        (Term.app
         (Term.proj `H "." `mono)
         [(Term.fun
           "fun"
           (Term.basicFun [`x `H] [] "=>" (Term.app `mul_le_mul_left' [`H (Term.hole "_")])))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `H "." `mono)
       [(Term.fun
         "fun"
         (Term.basicFun [`x `H] [] "=>" (Term.app `mul_le_mul_left' [`H (Term.hole "_")])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun [`x `H] [] "=>" (Term.app `mul_le_mul_left' [`H (Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_le_mul_left' [`H (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_le_mul_left'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `H "." `mono)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `H
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app `induction_on [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `induction_on
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `induction_on [`h]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
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
      `H
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app `induction_on₂ [`f `g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `induction_on₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `induction_on₂ [`f `g]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.commMonoid
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.partialOrder
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `OrderedCommMonoid [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ to_additive ]
  instance
    [ OrderedCommMonoid β ] : OrderedCommMonoid β*
    :=
      {
        Germ.partialOrder , Germ.commMonoid with
        mul_le_mul_left
          :=
          fun
            f g
              =>
              induction_on₂ f g
                fun f g H h => induction_on h fun h => H . mono fun x H => mul_le_mul_left' H _
        }

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes
        "@["
        [(Term.attrInstance
          (Term.attrKind [])
          (to_additive "to_additive" [] [] (to_additiveRest [] [] [])))]
        "]")]
      []
      []
      []
      [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `OrderedCancelCommMonoid [`β]) "]")]
       (Term.typeSpec
        ":"
        (Term.app
         `OrderedCancelCommMonoid
         [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])))
      (Command.declValSimple
       ":="
       (Term.structInst
        "{"
        [[`Germ.partialOrder "," `Germ.orderedCommMonoid] "with"]
        [(Term.structInstField
          (Term.structInstLVal `le_of_mul_le_mul_left [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`f `g `h]
            []
            "=>"
            (Term.app
             (Term.app `induction_on₃ [`f `g `h])
             [(Term.fun
               "fun"
               (Term.basicFun
                [`f `g `h `H]
                []
                "=>"
                (Term.app
                 (Term.proj `H "." `mono)
                 [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `le_of_mul_le_mul_left'))])))]))))]
        (Term.optEllipsis [])
        []
        "}")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       [[`Germ.partialOrder "," `Germ.orderedCommMonoid] "with"]
       [(Term.structInstField
         (Term.structInstLVal `le_of_mul_le_mul_left [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`f `g `h]
           []
           "=>"
           (Term.app
            (Term.app `induction_on₃ [`f `g `h])
            [(Term.fun
              "fun"
              (Term.basicFun
               [`f `g `h `H]
               []
               "=>"
               (Term.app
                (Term.proj `H "." `mono)
                [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `le_of_mul_le_mul_left'))])))]))))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f `g `h]
        []
        "=>"
        (Term.app
         (Term.app `induction_on₃ [`f `g `h])
         [(Term.fun
           "fun"
           (Term.basicFun
            [`f `g `h `H]
            []
            "=>"
            (Term.app
             (Term.proj `H "." `mono)
             [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `le_of_mul_le_mul_left'))])))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app `induction_on₃ [`f `g `h])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`f `g `h `H]
          []
          "=>"
          (Term.app
           (Term.proj `H "." `mono)
           [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `le_of_mul_le_mul_left'))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f `g `h `H]
        []
        "=>"
        (Term.app
         (Term.proj `H "." `mono)
         [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `le_of_mul_le_mul_left'))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `H "." `mono)
       [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `le_of_mul_le_mul_left'))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`x] [] "=>" `le_of_mul_le_mul_left'))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `le_of_mul_le_mul_left'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `H "." `mono)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `H
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app `induction_on₃ [`f `g `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `induction_on₃
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `induction_on₃ [`f `g `h])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
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
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.orderedCommMonoid
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.partialOrder
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `OrderedCancelCommMonoid [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ to_additive ]
  instance
    [ OrderedCancelCommMonoid β ] : OrderedCancelCommMonoid β*
    :=
      {
        Germ.partialOrder , Germ.orderedCommMonoid with
        le_of_mul_le_mul_left
          :=
          fun f g h => induction_on₃ f g h fun f g h H => H . mono fun x => le_of_mul_le_mul_left'
        }

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes
        "@["
        [(Term.attrInstance
          (Term.attrKind [])
          (to_additive "to_additive" [] [] (to_additiveRest [] [] [])))]
        "]")]
      []
      []
      []
      [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `OrderedCommGroup [`β]) "]")]
       (Term.typeSpec
        ":"
        (Term.app `OrderedCommGroup [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])))
      (Command.declValSimple
       ":="
       (Term.structInst
        "{"
        [[`Germ.orderedCancelCommMonoid "," `Germ.commGroup] "with"]
        []
        (Term.optEllipsis [])
        []
        "}")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       [[`Germ.orderedCancelCommMonoid "," `Germ.commGroup] "with"]
       []
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.commGroup
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.orderedCancelCommMonoid
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `OrderedCommGroup [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ to_additive ]
  instance
    [ OrderedCommGroup β ] : OrderedCommGroup β*
    := { Germ.orderedCancelCommMonoid , Germ.commGroup with }

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes
        "@["
        [(Term.attrInstance
          (Term.attrKind [])
          (to_additive "to_additive" [] [] (to_additiveRest [] [] [])))]
        "]")]
      []
      [(Command.noncomputable "noncomputable")]
      []
      [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `LinearOrderedCommGroup [`β]) "]")]
       (Term.typeSpec
        ":"
        (Term.app
         `LinearOrderedCommGroup
         [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])))
      (Command.declValSimple
       ":="
       (Term.structInst
        "{"
        [[`Germ.orderedCommGroup "," `Germ.linearOrder] "with"]
        []
        (Term.optEllipsis [])
        []
        "}")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       [[`Germ.orderedCommGroup "," `Germ.linearOrder] "with"]
       []
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.linearOrder
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.orderedCommGroup
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `LinearOrderedCommGroup [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ to_additive ] noncomputable
  instance
    [ LinearOrderedCommGroup β ] : LinearOrderedCommGroup β*
    := { Germ.orderedCommGroup , Germ.linearOrder with }

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `OrderedSemiring [`β]) "]")]
       (Term.typeSpec
        ":"
        (Term.app `OrderedSemiring [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])))
      (Command.declValSimple
       ":="
       (Term.structInst
        "{"
        [[`Germ.semiring "," `Germ.orderedAddCommMonoid] "with"]
        [(Term.structInstField
          (Term.structInstLVal `zero_le_one [])
          ":="
          (Term.app `const_le [`zero_le_one]))
         []
         (Term.structInstField
          (Term.structInstLVal `mul_le_mul_of_nonneg_left [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`x `y `z]
            []
            "=>"
            (Term.app
             (Term.app `induction_on₃ [`x `y `z])
             [(Term.fun
               "fun"
               (Term.basicFun
                [`f `g `h `hfg `hh]
                []
                "=>"
                («term_<|_»
                 (Term.proj `hh "." `mp)
                 "<|"
                 (Term.app
                  (Term.proj `hfg "." `mono)
                  [(Term.fun
                    "fun"
                    (Term.basicFun [`a] [] "=>" `mul_le_mul_of_nonneg_left))]))))]))))
         []
         (Term.structInstField
          (Term.structInstLVal `mul_le_mul_of_nonneg_right [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`x `y `z]
            []
            "=>"
            (Term.app
             (Term.app `induction_on₃ [`x `y `z])
             [(Term.fun
               "fun"
               (Term.basicFun
                [`f `g `h `hfg `hh]
                []
                "=>"
                («term_<|_»
                 (Term.proj `hh "." `mp)
                 "<|"
                 (Term.app
                  (Term.proj `hfg "." `mono)
                  [(Term.fun
                    "fun"
                    (Term.basicFun [`a] [] "=>" `mul_le_mul_of_nonneg_right))]))))]))))]
        (Term.optEllipsis [])
        []
        "}")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       [[`Germ.semiring "," `Germ.orderedAddCommMonoid] "with"]
       [(Term.structInstField
         (Term.structInstLVal `zero_le_one [])
         ":="
         (Term.app `const_le [`zero_le_one]))
        []
        (Term.structInstField
         (Term.structInstLVal `mul_le_mul_of_nonneg_left [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`x `y `z]
           []
           "=>"
           (Term.app
            (Term.app `induction_on₃ [`x `y `z])
            [(Term.fun
              "fun"
              (Term.basicFun
               [`f `g `h `hfg `hh]
               []
               "=>"
               («term_<|_»
                (Term.proj `hh "." `mp)
                "<|"
                (Term.app
                 (Term.proj `hfg "." `mono)
                 [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_le_mul_of_nonneg_left))]))))]))))
        []
        (Term.structInstField
         (Term.structInstLVal `mul_le_mul_of_nonneg_right [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`x `y `z]
           []
           "=>"
           (Term.app
            (Term.app `induction_on₃ [`x `y `z])
            [(Term.fun
              "fun"
              (Term.basicFun
               [`f `g `h `hfg `hh]
               []
               "=>"
               («term_<|_»
                (Term.proj `hh "." `mp)
                "<|"
                (Term.app
                 (Term.proj `hfg "." `mono)
                 [(Term.fun
                   "fun"
                   (Term.basicFun [`a] [] "=>" `mul_le_mul_of_nonneg_right))]))))]))))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x `y `z]
        []
        "=>"
        (Term.app
         (Term.app `induction_on₃ [`x `y `z])
         [(Term.fun
           "fun"
           (Term.basicFun
            [`f `g `h `hfg `hh]
            []
            "=>"
            («term_<|_»
             (Term.proj `hh "." `mp)
             "<|"
             (Term.app
              (Term.proj `hfg "." `mono)
              [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_le_mul_of_nonneg_right))]))))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app `induction_on₃ [`x `y `z])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`f `g `h `hfg `hh]
          []
          "=>"
          («term_<|_»
           (Term.proj `hh "." `mp)
           "<|"
           (Term.app
            (Term.proj `hfg "." `mono)
            [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_le_mul_of_nonneg_right))]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f `g `h `hfg `hh]
        []
        "=>"
        («term_<|_»
         (Term.proj `hh "." `mp)
         "<|"
         (Term.app
          (Term.proj `hfg "." `mono)
          [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_le_mul_of_nonneg_right))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj `hh "." `mp)
       "<|"
       (Term.app
        (Term.proj `hfg "." `mono)
        [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_le_mul_of_nonneg_right))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `hfg "." `mono)
       [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_le_mul_of_nonneg_right))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_le_mul_of_nonneg_right))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_le_mul_of_nonneg_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `hfg "." `mono)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hfg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `hh "." `mp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hh
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hh
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hfg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app `induction_on₃ [`x `y `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `induction_on₃
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `induction_on₃ [`x `y `z])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x `y `z]
        []
        "=>"
        (Term.app
         (Term.app `induction_on₃ [`x `y `z])
         [(Term.fun
           "fun"
           (Term.basicFun
            [`f `g `h `hfg `hh]
            []
            "=>"
            («term_<|_»
             (Term.proj `hh "." `mp)
             "<|"
             (Term.app
              (Term.proj `hfg "." `mono)
              [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_le_mul_of_nonneg_left))]))))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app `induction_on₃ [`x `y `z])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`f `g `h `hfg `hh]
          []
          "=>"
          («term_<|_»
           (Term.proj `hh "." `mp)
           "<|"
           (Term.app
            (Term.proj `hfg "." `mono)
            [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_le_mul_of_nonneg_left))]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f `g `h `hfg `hh]
        []
        "=>"
        («term_<|_»
         (Term.proj `hh "." `mp)
         "<|"
         (Term.app
          (Term.proj `hfg "." `mono)
          [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_le_mul_of_nonneg_left))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj `hh "." `mp)
       "<|"
       (Term.app
        (Term.proj `hfg "." `mono)
        [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_le_mul_of_nonneg_left))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `hfg "." `mono)
       [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_le_mul_of_nonneg_left))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_le_mul_of_nonneg_left))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_le_mul_of_nonneg_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `hfg "." `mono)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hfg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `hh "." `mp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hh
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hh
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hfg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app `induction_on₃ [`x `y `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `induction_on₃
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `induction_on₃ [`x `y `z])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `const_le [`zero_le_one])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_le_one
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `const_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.orderedAddCommMonoid
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.semiring
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `OrderedSemiring [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  [ OrderedSemiring β ] : OrderedSemiring β*
  :=
    {
      Germ.semiring , Germ.orderedAddCommMonoid with
      zero_le_one := const_le zero_le_one
        mul_le_mul_of_nonneg_left
          :=
          fun
            x y z
              =>
              induction_on₃ x y z
                fun f g h hfg hh => hh . mp <| hfg . mono fun a => mul_le_mul_of_nonneg_left
        mul_le_mul_of_nonneg_right
          :=
          fun
            x y z
              =>
              induction_on₃ x y z
                fun f g h hfg hh => hh . mp <| hfg . mono fun a => mul_le_mul_of_nonneg_right
      }

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `OrderedCommSemiring [`β]) "]")]
       (Term.typeSpec
        ":"
        (Term.app `OrderedCommSemiring [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])))
      (Command.declValSimple
       ":="
       (Term.structInst
        "{"
        [[`Germ.orderedSemiring "," `Germ.commSemiring] "with"]
        []
        (Term.optEllipsis [])
        []
        "}")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       [[`Germ.orderedSemiring "," `Germ.commSemiring] "with"]
       []
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.commSemiring
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.orderedSemiring
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `OrderedCommSemiring [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  [ OrderedCommSemiring β ] : OrderedCommSemiring β*
  := { Germ.orderedSemiring , Germ.commSemiring with }

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `OrderedRing [`β]) "]")]
       (Term.typeSpec
        ":"
        (Term.app `OrderedRing [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])))
      (Command.declValSimple
       ":="
       (Term.structInst
        "{"
        [[`Germ.ring "," `Germ.orderedAddCommGroup] "with"]
        [(Term.structInstField
          (Term.structInstLVal `zero_le_one [])
          ":="
          (Term.app `const_le [`zero_le_one]))
         []
         (Term.structInstField
          (Term.structInstLVal `mul_nonneg [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`x `y]
            []
            "=>"
            (Term.app
             (Term.app `induction_on₂ [`x `y])
             [(Term.fun
               "fun"
               (Term.basicFun
                [`f `g `hf `hg]
                []
                "=>"
                («term_<|_»
                 (Term.proj `hg "." `mp)
                 "<|"
                 (Term.app
                  (Term.proj `hf "." `mono)
                  [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_nonneg))]))))]))))]
        (Term.optEllipsis [])
        []
        "}")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       [[`Germ.ring "," `Germ.orderedAddCommGroup] "with"]
       [(Term.structInstField
         (Term.structInstLVal `zero_le_one [])
         ":="
         (Term.app `const_le [`zero_le_one]))
        []
        (Term.structInstField
         (Term.structInstLVal `mul_nonneg [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`x `y]
           []
           "=>"
           (Term.app
            (Term.app `induction_on₂ [`x `y])
            [(Term.fun
              "fun"
              (Term.basicFun
               [`f `g `hf `hg]
               []
               "=>"
               («term_<|_»
                (Term.proj `hg "." `mp)
                "<|"
                (Term.app
                 (Term.proj `hf "." `mono)
                 [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_nonneg))]))))]))))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x `y]
        []
        "=>"
        (Term.app
         (Term.app `induction_on₂ [`x `y])
         [(Term.fun
           "fun"
           (Term.basicFun
            [`f `g `hf `hg]
            []
            "=>"
            («term_<|_»
             (Term.proj `hg "." `mp)
             "<|"
             (Term.app
              (Term.proj `hf "." `mono)
              [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_nonneg))]))))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app `induction_on₂ [`x `y])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`f `g `hf `hg]
          []
          "=>"
          («term_<|_»
           (Term.proj `hg "." `mp)
           "<|"
           (Term.app
            (Term.proj `hf "." `mono)
            [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_nonneg))]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f `g `hf `hg]
        []
        "=>"
        («term_<|_»
         (Term.proj `hg "." `mp)
         "<|"
         (Term.app
          (Term.proj `hf "." `mono)
          [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_nonneg))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj `hg "." `mp)
       "<|"
       (Term.app
        (Term.proj `hf "." `mono)
        [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_nonneg))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `hf "." `mono)
       [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_nonneg))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_nonneg))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_nonneg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `hf "." `mono)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `hg "." `mp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app `induction_on₂ [`x `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `induction_on₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `induction_on₂ [`x `y]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `const_le [`zero_le_one])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_le_one
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `const_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.orderedAddCommGroup
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.ring
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `OrderedRing [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  [ OrderedRing β ] : OrderedRing β*
  :=
    {
      Germ.ring , Germ.orderedAddCommGroup with
      zero_le_one := const_le zero_le_one
        mul_nonneg
          :=
          fun x y => induction_on₂ x y fun f g hf hg => hg . mp <| hf . mono fun a => mul_nonneg
      }

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `OrderedCommRing [`β]) "]")]
       (Term.typeSpec
        ":"
        (Term.app `OrderedCommRing [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])))
      (Command.declValSimple
       ":="
       (Term.structInst
        "{"
        [[`Germ.orderedRing "," `Germ.orderedCommSemiring] "with"]
        []
        (Term.optEllipsis [])
        []
        "}")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       [[`Germ.orderedRing "," `Germ.orderedCommSemiring] "with"]
       []
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.orderedCommSemiring
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.orderedRing
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `OrderedCommRing [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  [ OrderedCommRing β ] : OrderedCommRing β*
  := { Germ.orderedRing , Germ.orderedCommSemiring with }

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `StrictOrderedSemiring [`β]) "]")]
       (Term.typeSpec
        ":"
        (Term.app `StrictOrderedSemiring [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])))
      (Command.declValSimple
       ":="
       (Term.structInst
        "{"
        [[`Germ.orderedSemiring "," `Germ.orderedCancelAddCommMonoid "," `Germ.nontrivial] "with"]
        [(Term.structInstField
          (Term.structInstLVal `mul_lt_mul_of_pos_left [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`x `y `z]
            []
            "=>"
            (Term.app
             (Term.app `induction_on₃ [`x `y `z])
             [(Term.fun
               "fun"
               (Term.basicFun
                [`f `g `h `hfg `hh]
                []
                "=>"
                («term_<|_»
                 (Term.proj `coe_lt "." (fieldIdx "2"))
                 "<|"
                 («term_<|_»
                  (Term.proj (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hh]) "." `mp)
                  "<|"
                  (Term.app
                   (Term.proj (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hfg]) "." `mono)
                   [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_lt_mul_of_pos_left))])))))]))))
         []
         (Term.structInstField
          (Term.structInstLVal `mul_lt_mul_of_pos_right [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`x `y `z]
            []
            "=>"
            (Term.app
             (Term.app `induction_on₃ [`x `y `z])
             [(Term.fun
               "fun"
               (Term.basicFun
                [`f `g `h `hfg `hh]
                []
                "=>"
                («term_<|_»
                 (Term.proj `coe_lt "." (fieldIdx "2"))
                 "<|"
                 («term_<|_»
                  (Term.proj (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hh]) "." `mp)
                  "<|"
                  (Term.app
                   (Term.proj (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hfg]) "." `mono)
                   [(Term.fun
                     "fun"
                     (Term.basicFun [`a] [] "=>" `mul_lt_mul_of_pos_right))])))))]))))]
        (Term.optEllipsis [])
        []
        "}")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       [[`Germ.orderedSemiring "," `Germ.orderedCancelAddCommMonoid "," `Germ.nontrivial] "with"]
       [(Term.structInstField
         (Term.structInstLVal `mul_lt_mul_of_pos_left [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`x `y `z]
           []
           "=>"
           (Term.app
            (Term.app `induction_on₃ [`x `y `z])
            [(Term.fun
              "fun"
              (Term.basicFun
               [`f `g `h `hfg `hh]
               []
               "=>"
               («term_<|_»
                (Term.proj `coe_lt "." (fieldIdx "2"))
                "<|"
                («term_<|_»
                 (Term.proj (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hh]) "." `mp)
                 "<|"
                 (Term.app
                  (Term.proj (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hfg]) "." `mono)
                  [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_lt_mul_of_pos_left))])))))]))))
        []
        (Term.structInstField
         (Term.structInstLVal `mul_lt_mul_of_pos_right [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`x `y `z]
           []
           "=>"
           (Term.app
            (Term.app `induction_on₃ [`x `y `z])
            [(Term.fun
              "fun"
              (Term.basicFun
               [`f `g `h `hfg `hh]
               []
               "=>"
               («term_<|_»
                (Term.proj `coe_lt "." (fieldIdx "2"))
                "<|"
                («term_<|_»
                 (Term.proj (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hh]) "." `mp)
                 "<|"
                 (Term.app
                  (Term.proj (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hfg]) "." `mono)
                  [(Term.fun
                    "fun"
                    (Term.basicFun [`a] [] "=>" `mul_lt_mul_of_pos_right))])))))]))))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x `y `z]
        []
        "=>"
        (Term.app
         (Term.app `induction_on₃ [`x `y `z])
         [(Term.fun
           "fun"
           (Term.basicFun
            [`f `g `h `hfg `hh]
            []
            "=>"
            («term_<|_»
             (Term.proj `coe_lt "." (fieldIdx "2"))
             "<|"
             («term_<|_»
              (Term.proj (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hh]) "." `mp)
              "<|"
              (Term.app
               (Term.proj (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hfg]) "." `mono)
               [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_lt_mul_of_pos_right))])))))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app `induction_on₃ [`x `y `z])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`f `g `h `hfg `hh]
          []
          "=>"
          («term_<|_»
           (Term.proj `coe_lt "." (fieldIdx "2"))
           "<|"
           («term_<|_»
            (Term.proj (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hh]) "." `mp)
            "<|"
            (Term.app
             (Term.proj (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hfg]) "." `mono)
             [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_lt_mul_of_pos_right))])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f `g `h `hfg `hh]
        []
        "=>"
        («term_<|_»
         (Term.proj `coe_lt "." (fieldIdx "2"))
         "<|"
         («term_<|_»
          (Term.proj (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hh]) "." `mp)
          "<|"
          (Term.app
           (Term.proj (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hfg]) "." `mono)
           [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_lt_mul_of_pos_right))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj `coe_lt "." (fieldIdx "2"))
       "<|"
       («term_<|_»
        (Term.proj (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hh]) "." `mp)
        "<|"
        (Term.app
         (Term.proj (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hfg]) "." `mono)
         [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_lt_mul_of_pos_right))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hh]) "." `mp)
       "<|"
       (Term.app
        (Term.proj (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hfg]) "." `mono)
        [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_lt_mul_of_pos_right))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hfg]) "." `mono)
       [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_lt_mul_of_pos_right))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_lt_mul_of_pos_right))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_lt_mul_of_pos_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hfg]) "." `mono)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hfg])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hfg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `coe_lt "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `coe_lt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hfg])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hh]) "." `mp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hh])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hh
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `coe_lt "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `coe_lt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hh])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `coe_lt "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `coe_lt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hh
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hfg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app `induction_on₃ [`x `y `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `induction_on₃
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `induction_on₃ [`x `y `z])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x `y `z]
        []
        "=>"
        (Term.app
         (Term.app `induction_on₃ [`x `y `z])
         [(Term.fun
           "fun"
           (Term.basicFun
            [`f `g `h `hfg `hh]
            []
            "=>"
            («term_<|_»
             (Term.proj `coe_lt "." (fieldIdx "2"))
             "<|"
             («term_<|_»
              (Term.proj (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hh]) "." `mp)
              "<|"
              (Term.app
               (Term.proj (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hfg]) "." `mono)
               [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_lt_mul_of_pos_left))])))))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app `induction_on₃ [`x `y `z])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`f `g `h `hfg `hh]
          []
          "=>"
          («term_<|_»
           (Term.proj `coe_lt "." (fieldIdx "2"))
           "<|"
           («term_<|_»
            (Term.proj (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hh]) "." `mp)
            "<|"
            (Term.app
             (Term.proj (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hfg]) "." `mono)
             [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_lt_mul_of_pos_left))])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f `g `h `hfg `hh]
        []
        "=>"
        («term_<|_»
         (Term.proj `coe_lt "." (fieldIdx "2"))
         "<|"
         («term_<|_»
          (Term.proj (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hh]) "." `mp)
          "<|"
          (Term.app
           (Term.proj (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hfg]) "." `mono)
           [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_lt_mul_of_pos_left))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj `coe_lt "." (fieldIdx "2"))
       "<|"
       («term_<|_»
        (Term.proj (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hh]) "." `mp)
        "<|"
        (Term.app
         (Term.proj (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hfg]) "." `mono)
         [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_lt_mul_of_pos_left))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hh]) "." `mp)
       "<|"
       (Term.app
        (Term.proj (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hfg]) "." `mono)
        [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_lt_mul_of_pos_left))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hfg]) "." `mono)
       [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_lt_mul_of_pos_left))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`a] [] "=>" `mul_lt_mul_of_pos_left))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_lt_mul_of_pos_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hfg]) "." `mono)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hfg])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hfg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `coe_lt "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `coe_lt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hfg])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hh]) "." `mp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hh])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hh
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `coe_lt "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `coe_lt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `coe_lt "." (fieldIdx "1")) [`hh])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `coe_lt "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `coe_lt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hh
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hfg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app `induction_on₃ [`x `y `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `induction_on₃
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `induction_on₃ [`x `y `z])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.nontrivial
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.orderedCancelAddCommMonoid
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.orderedSemiring
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `StrictOrderedSemiring [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  [ StrictOrderedSemiring β ] : StrictOrderedSemiring β*
  :=
    {
      Germ.orderedSemiring , Germ.orderedCancelAddCommMonoid , Germ.nontrivial with
      mul_lt_mul_of_pos_left
          :=
          fun
            x y z
              =>
              induction_on₃ x y z
                fun
                  f g h hfg hh
                    =>
                    coe_lt . 2
                      <|
                      coe_lt . 1 hh . mp <| coe_lt . 1 hfg . mono fun a => mul_lt_mul_of_pos_left
        mul_lt_mul_of_pos_right
          :=
          fun
            x y z
              =>
              induction_on₃ x y z
                fun
                  f g h hfg hh
                    =>
                    coe_lt . 2
                      <|
                      coe_lt . 1 hh . mp <| coe_lt . 1 hfg . mono fun a => mul_lt_mul_of_pos_right
      }

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `StrictOrderedCommSemiring [`β]) "]")]
       (Term.typeSpec
        ":"
        (Term.app
         `StrictOrderedCommSemiring
         [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])))
      (Command.declValSimple
       ":="
       (Term.structInst
        "{"
        [[`Germ.strictOrderedSemiring "," `Germ.orderedCommSemiring] "with"]
        []
        (Term.optEllipsis [])
        []
        "}")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       [[`Germ.strictOrderedSemiring "," `Germ.orderedCommSemiring] "with"]
       []
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.orderedCommSemiring
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.strictOrderedSemiring
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `StrictOrderedCommSemiring [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  [ StrictOrderedCommSemiring β ] : StrictOrderedCommSemiring β*
  := { Germ.strictOrderedSemiring , Germ.orderedCommSemiring with }

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `StrictOrderedRing [`β]) "]")]
       (Term.typeSpec
        ":"
        (Term.app `StrictOrderedRing [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])))
      (Command.declValSimple
       ":="
       (Term.structInst
        "{"
        [[`Germ.ring "," `Germ.strictOrderedSemiring] "with"]
        [(Term.structInstField
          (Term.structInstLVal `zero_le_one [])
          ":="
          (Term.app `const_le [`zero_le_one]))
         []
         (Term.structInstField
          (Term.structInstLVal `mul_pos [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`x `y]
            []
            "=>"
            (Term.app
             (Term.app `induction_on₂ [`x `y])
             [(Term.fun
               "fun"
               (Term.basicFun
                [`f `g `hf `hg]
                []
                "=>"
                («term_<|_»
                 (Term.proj `coe_pos "." (fieldIdx "2"))
                 "<|"
                 («term_<|_»
                  (Term.proj (Term.app (Term.proj `coe_pos "." (fieldIdx "1")) [`hg]) "." `mp)
                  "<|"
                  (Term.app
                   (Term.proj (Term.app (Term.proj `coe_pos "." (fieldIdx "1")) [`hf]) "." `mono)
                   [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `mul_pos))])))))]))))]
        (Term.optEllipsis [])
        []
        "}")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       [[`Germ.ring "," `Germ.strictOrderedSemiring] "with"]
       [(Term.structInstField
         (Term.structInstLVal `zero_le_one [])
         ":="
         (Term.app `const_le [`zero_le_one]))
        []
        (Term.structInstField
         (Term.structInstLVal `mul_pos [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`x `y]
           []
           "=>"
           (Term.app
            (Term.app `induction_on₂ [`x `y])
            [(Term.fun
              "fun"
              (Term.basicFun
               [`f `g `hf `hg]
               []
               "=>"
               («term_<|_»
                (Term.proj `coe_pos "." (fieldIdx "2"))
                "<|"
                («term_<|_»
                 (Term.proj (Term.app (Term.proj `coe_pos "." (fieldIdx "1")) [`hg]) "." `mp)
                 "<|"
                 (Term.app
                  (Term.proj (Term.app (Term.proj `coe_pos "." (fieldIdx "1")) [`hf]) "." `mono)
                  [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `mul_pos))])))))]))))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x `y]
        []
        "=>"
        (Term.app
         (Term.app `induction_on₂ [`x `y])
         [(Term.fun
           "fun"
           (Term.basicFun
            [`f `g `hf `hg]
            []
            "=>"
            («term_<|_»
             (Term.proj `coe_pos "." (fieldIdx "2"))
             "<|"
             («term_<|_»
              (Term.proj (Term.app (Term.proj `coe_pos "." (fieldIdx "1")) [`hg]) "." `mp)
              "<|"
              (Term.app
               (Term.proj (Term.app (Term.proj `coe_pos "." (fieldIdx "1")) [`hf]) "." `mono)
               [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `mul_pos))])))))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app `induction_on₂ [`x `y])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`f `g `hf `hg]
          []
          "=>"
          («term_<|_»
           (Term.proj `coe_pos "." (fieldIdx "2"))
           "<|"
           («term_<|_»
            (Term.proj (Term.app (Term.proj `coe_pos "." (fieldIdx "1")) [`hg]) "." `mp)
            "<|"
            (Term.app
             (Term.proj (Term.app (Term.proj `coe_pos "." (fieldIdx "1")) [`hf]) "." `mono)
             [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `mul_pos))])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f `g `hf `hg]
        []
        "=>"
        («term_<|_»
         (Term.proj `coe_pos "." (fieldIdx "2"))
         "<|"
         («term_<|_»
          (Term.proj (Term.app (Term.proj `coe_pos "." (fieldIdx "1")) [`hg]) "." `mp)
          "<|"
          (Term.app
           (Term.proj (Term.app (Term.proj `coe_pos "." (fieldIdx "1")) [`hf]) "." `mono)
           [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `mul_pos))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj `coe_pos "." (fieldIdx "2"))
       "<|"
       («term_<|_»
        (Term.proj (Term.app (Term.proj `coe_pos "." (fieldIdx "1")) [`hg]) "." `mp)
        "<|"
        (Term.app
         (Term.proj (Term.app (Term.proj `coe_pos "." (fieldIdx "1")) [`hf]) "." `mono)
         [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `mul_pos))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj (Term.app (Term.proj `coe_pos "." (fieldIdx "1")) [`hg]) "." `mp)
       "<|"
       (Term.app
        (Term.proj (Term.app (Term.proj `coe_pos "." (fieldIdx "1")) [`hf]) "." `mono)
        [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `mul_pos))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app (Term.proj `coe_pos "." (fieldIdx "1")) [`hf]) "." `mono)
       [(Term.fun "fun" (Term.basicFun [`x] [] "=>" `mul_pos))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`x] [] "=>" `mul_pos))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_pos
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app (Term.proj `coe_pos "." (fieldIdx "1")) [`hf]) "." `mono)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `coe_pos "." (fieldIdx "1")) [`hf])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `coe_pos "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `coe_pos
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `coe_pos "." (fieldIdx "1")) [`hf])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj (Term.app (Term.proj `coe_pos "." (fieldIdx "1")) [`hg]) "." `mp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `coe_pos "." (fieldIdx "1")) [`hg])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `coe_pos "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `coe_pos
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `coe_pos "." (fieldIdx "1")) [`hg])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `coe_pos "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `coe_pos
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app `induction_on₂ [`x `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `induction_on₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `induction_on₂ [`x `y]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `const_le [`zero_le_one])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_le_one
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `const_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.strictOrderedSemiring
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.ring
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `StrictOrderedRing [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  [ StrictOrderedRing β ] : StrictOrderedRing β*
  :=
    {
      Germ.ring , Germ.strictOrderedSemiring with
      zero_le_one := const_le zero_le_one
        mul_pos
          :=
          fun
            x y
              =>
              induction_on₂ x y
                fun
                  f g hf hg
                    =>
                    coe_pos . 2 <| coe_pos . 1 hg . mp <| coe_pos . 1 hf . mono fun x => mul_pos
      }

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `StrictOrderedCommRing [`β]) "]")]
       (Term.typeSpec
        ":"
        (Term.app `StrictOrderedCommRing [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])))
      (Command.declValSimple
       ":="
       (Term.structInst
        "{"
        [[`Germ.strictOrderedRing "," `Germ.orderedCommRing] "with"]
        []
        (Term.optEllipsis [])
        []
        "}")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       [[`Germ.strictOrderedRing "," `Germ.orderedCommRing] "with"]
       []
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.orderedCommRing
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.strictOrderedRing
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `StrictOrderedCommRing [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  [ StrictOrderedCommRing β ] : StrictOrderedCommRing β*
  := { Germ.strictOrderedRing , Germ.orderedCommRing with }

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [(Command.noncomputable "noncomputable")] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `LinearOrderedRing [`β]) "]")]
       (Term.typeSpec
        ":"
        (Term.app `LinearOrderedRing [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])))
      (Command.declValSimple
       ":="
       (Term.structInst
        "{"
        [[`Germ.strictOrderedRing "," `Germ.linearOrder] "with"]
        []
        (Term.optEllipsis [])
        []
        "}")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       [[`Germ.strictOrderedRing "," `Germ.linearOrder] "with"]
       []
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.linearOrder
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.strictOrderedRing
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `LinearOrderedRing [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
noncomputable
  instance
    [ LinearOrderedRing β ] : LinearOrderedRing β*
    := { Germ.strictOrderedRing , Germ.linearOrder with }

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [(Command.noncomputable "noncomputable")] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `LinearOrderedField [`β]) "]")]
       (Term.typeSpec
        ":"
        (Term.app `LinearOrderedField [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])))
      (Command.declValSimple
       ":="
       (Term.structInst
        "{"
        [[`Germ.linearOrderedRing "," `Germ.field] "with"]
        []
        (Term.optEllipsis [])
        []
        "}")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       [[`Germ.linearOrderedRing "," `Germ.field] "with"]
       []
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.field
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.linearOrderedRing
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `LinearOrderedField [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
noncomputable
  instance
    [ LinearOrderedField β ] : LinearOrderedField β*
    := { Germ.linearOrderedRing , Germ.field with }

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [(Command.noncomputable "noncomputable")] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `LinearOrderedCommRing [`β]) "]")]
       (Term.typeSpec
        ":"
        (Term.app `LinearOrderedCommRing [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])))
      (Command.declValSimple
       ":="
       (Term.structInst
        "{"
        [[`Germ.linearOrderedRing "," `Germ.commMonoid] "with"]
        []
        (Term.optEllipsis [])
        []
        "}")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       [[`Germ.linearOrderedRing "," `Germ.commMonoid] "with"]
       []
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.commMonoid
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Germ.linearOrderedRing
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `LinearOrderedCommRing [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
noncomputable
  instance
    [ LinearOrderedCommRing β ] : LinearOrderedCommRing β*
    := { Germ.linearOrderedRing , Germ.commMonoid with }

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `max_def [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `LinearOrder [`β]) "]")
        (Term.explicitBinder
         "("
         [`x `y]
         [":" (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
         []
         ")")]
       (Term.typeSpec ":" («term_=_» (Term.app `max [`x `y]) "=" (Term.app `map₂ [`max `x `y]))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.app `induction_on₂ [`x `y])
        [(Term.fun
          "fun"
          (Term.basicFun
           [`a `b]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.cases
                "cases"
                [(Tactic.casesTarget
                  []
                  (Term.app
                   `le_total
                   [(Term.typeAscription
                     "("
                     `a
                     ":"
                     [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
                     ")")
                    `b]))]
                []
                [])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] (Term.app `max_eq_right [`h]))
                    ","
                    (Tactic.rwRule [] `map₂_coe)
                    ","
                    (Tactic.rwRule [] `coe_eq)]
                   "]")
                  [])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.app
                   `h.mono
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [`i `hi]
                      []
                      "=>"
                      (Term.proj (Term.app `max_eq_right [`hi]) "." `symm)))]))])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] (Term.app `max_eq_left [`h]))
                    ","
                    (Tactic.rwRule [] `map₂_coe)
                    ","
                    (Tactic.rwRule [] `coe_eq)]
                   "]")
                  [])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.app
                   `h.mono
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [`i `hi]
                      []
                      "=>"
                      (Term.proj (Term.app `max_eq_left [`hi]) "." `symm)))]))])])))))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app `induction_on₂ [`x `y])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`a `b]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.cases
               "cases"
               [(Tactic.casesTarget
                 []
                 (Term.app
                  `le_total
                  [(Term.typeAscription
                    "("
                    `a
                    ":"
                    [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
                    ")")
                   `b]))]
               []
               [])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] (Term.app `max_eq_right [`h]))
                   ","
                   (Tactic.rwRule [] `map₂_coe)
                   ","
                   (Tactic.rwRule [] `coe_eq)]
                  "]")
                 [])
                []
                (Tactic.exact
                 "exact"
                 (Term.app
                  `h.mono
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [`i `hi]
                     []
                     "=>"
                     (Term.proj (Term.app `max_eq_right [`hi]) "." `symm)))]))])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] (Term.app `max_eq_left [`h]))
                   ","
                   (Tactic.rwRule [] `map₂_coe)
                   ","
                   (Tactic.rwRule [] `coe_eq)]
                  "]")
                 [])
                []
                (Tactic.exact
                 "exact"
                 (Term.app
                  `h.mono
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [`i `hi]
                     []
                     "=>"
                     (Term.proj (Term.app `max_eq_left [`hi]) "." `symm)))]))])])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a `b]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.cases
             "cases"
             [(Tactic.casesTarget
               []
               (Term.app
                `le_total
                [(Term.typeAscription
                  "("
                  `a
                  ":"
                  [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
                  ")")
                 `b]))]
             []
             [])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] (Term.app `max_eq_right [`h]))
                 ","
                 (Tactic.rwRule [] `map₂_coe)
                 ","
                 (Tactic.rwRule [] `coe_eq)]
                "]")
               [])
              []
              (Tactic.exact
               "exact"
               (Term.app
                `h.mono
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [`i `hi]
                   []
                   "=>"
                   (Term.proj (Term.app `max_eq_right [`hi]) "." `symm)))]))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] (Term.app `max_eq_left [`h]))
                 ","
                 (Tactic.rwRule [] `map₂_coe)
                 ","
                 (Tactic.rwRule [] `coe_eq)]
                "]")
               [])
              []
              (Tactic.exact
               "exact"
               (Term.app
                `h.mono
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [`i `hi]
                   []
                   "=>"
                   (Term.proj (Term.app `max_eq_left [`hi]) "." `symm)))]))])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.cases
           "cases"
           [(Tactic.casesTarget
             []
             (Term.app
              `le_total
              [(Term.typeAscription
                "("
                `a
                ":"
                [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
                ")")
               `b]))]
           []
           [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] (Term.app `max_eq_right [`h]))
               ","
               (Tactic.rwRule [] `map₂_coe)
               ","
               (Tactic.rwRule [] `coe_eq)]
              "]")
             [])
            []
            (Tactic.exact
             "exact"
             (Term.app
              `h.mono
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`i `hi]
                 []
                 "=>"
                 (Term.proj (Term.app `max_eq_right [`hi]) "." `symm)))]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] (Term.app `max_eq_left [`h]))
               ","
               (Tactic.rwRule [] `map₂_coe)
               ","
               (Tactic.rwRule [] `coe_eq)]
              "]")
             [])
            []
            (Tactic.exact
             "exact"
             (Term.app
              `h.mono
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`i `hi]
                 []
                 "=>"
                 (Term.proj (Term.app `max_eq_left [`hi]) "." `symm)))]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] (Term.app `max_eq_left [`h]))
           ","
           (Tactic.rwRule [] `map₂_coe)
           ","
           (Tactic.rwRule [] `coe_eq)]
          "]")
         [])
        []
        (Tactic.exact
         "exact"
         (Term.app
          `h.mono
          [(Term.fun
            "fun"
            (Term.basicFun
             [`i `hi]
             []
             "=>"
             (Term.proj (Term.app `max_eq_left [`hi]) "." `symm)))]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `h.mono
        [(Term.fun
          "fun"
          (Term.basicFun [`i `hi] [] "=>" (Term.proj (Term.app `max_eq_left [`hi]) "." `symm)))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `h.mono
       [(Term.fun
         "fun"
         (Term.basicFun [`i `hi] [] "=>" (Term.proj (Term.app `max_eq_left [`hi]) "." `symm)))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun [`i `hi] [] "=>" (Term.proj (Term.app `max_eq_left [`hi]) "." `symm)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `max_eq_left [`hi]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `max_eq_left [`hi])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hi
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `max_eq_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `max_eq_left [`hi]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hi
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h.mono
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] (Term.app `max_eq_left [`h]))
         ","
         (Tactic.rwRule [] `map₂_coe)
         ","
         (Tactic.rwRule [] `coe_eq)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map₂_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `max_eq_left [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `max_eq_left
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
          [(Tactic.rwRule [] (Term.app `max_eq_right [`h]))
           ","
           (Tactic.rwRule [] `map₂_coe)
           ","
           (Tactic.rwRule [] `coe_eq)]
          "]")
         [])
        []
        (Tactic.exact
         "exact"
         (Term.app
          `h.mono
          [(Term.fun
            "fun"
            (Term.basicFun
             [`i `hi]
             []
             "=>"
             (Term.proj (Term.app `max_eq_right [`hi]) "." `symm)))]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `h.mono
        [(Term.fun
          "fun"
          (Term.basicFun [`i `hi] [] "=>" (Term.proj (Term.app `max_eq_right [`hi]) "." `symm)))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `h.mono
       [(Term.fun
         "fun"
         (Term.basicFun [`i `hi] [] "=>" (Term.proj (Term.app `max_eq_right [`hi]) "." `symm)))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun [`i `hi] [] "=>" (Term.proj (Term.app `max_eq_right [`hi]) "." `symm)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `max_eq_right [`hi]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `max_eq_right [`hi])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hi
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `max_eq_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `max_eq_right [`hi]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hi
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h.mono
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] (Term.app `max_eq_right [`h]))
         ","
         (Tactic.rwRule [] `map₂_coe)
         ","
         (Tactic.rwRule [] `coe_eq)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map₂_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `max_eq_right [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `max_eq_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases
       "cases"
       [(Tactic.casesTarget
         []
         (Term.app
          `le_total
          [(Term.typeAscription
            "("
            `a
            ":"
            [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
            ")")
           `b]))]
       []
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le_total
       [(Term.typeAscription
         "("
         `a
         ":"
         [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
         ")")
        `b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription "(" `a ":" [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  max_def
  [ LinearOrder β ] ( x y : β* ) : max x y = map₂ max x y
  :=
    induction_on₂ x y
      fun
        a b
          =>
          by
            cases le_total ( a : β* ) b
              ·
                rw [ max_eq_right h , map₂_coe , coe_eq ]
                  exact h.mono fun i hi => max_eq_right hi . symm
              ·
                rw [ max_eq_left h , map₂_coe , coe_eq ]
                  exact h.mono fun i hi => max_eq_left hi . symm
#align filter.germ.max_def Filter.Germ.max_def

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `min_def [])
      (Command.declSig
       [(Term.instBinder "[" [`K ":"] (Term.app `LinearOrder [`β]) "]")
        (Term.explicitBinder
         "("
         [`x `y]
         [":" (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
         []
         ")")]
       (Term.typeSpec ":" («term_=_» (Term.app `min [`x `y]) "=" (Term.app `map₂ [`min `x `y]))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.app `induction_on₂ [`x `y])
        [(Term.fun
          "fun"
          (Term.basicFun
           [`a `b]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.cases
                "cases"
                [(Tactic.casesTarget
                  []
                  (Term.app
                   `le_total
                   [(Term.typeAscription
                     "("
                     `a
                     ":"
                     [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
                     ")")
                    `b]))]
                []
                [])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] (Term.app `min_eq_left [`h]))
                    ","
                    (Tactic.rwRule [] `map₂_coe)
                    ","
                    (Tactic.rwRule [] `coe_eq)]
                   "]")
                  [])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.app
                   `h.mono
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [`i `hi]
                      []
                      "=>"
                      (Term.proj (Term.app `min_eq_left [`hi]) "." `symm)))]))])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] (Term.app `min_eq_right [`h]))
                    ","
                    (Tactic.rwRule [] `map₂_coe)
                    ","
                    (Tactic.rwRule [] `coe_eq)]
                   "]")
                  [])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.app
                   `h.mono
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [`i `hi]
                      []
                      "=>"
                      (Term.proj (Term.app `min_eq_right [`hi]) "." `symm)))]))])])))))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app `induction_on₂ [`x `y])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`a `b]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.cases
               "cases"
               [(Tactic.casesTarget
                 []
                 (Term.app
                  `le_total
                  [(Term.typeAscription
                    "("
                    `a
                    ":"
                    [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
                    ")")
                   `b]))]
               []
               [])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] (Term.app `min_eq_left [`h]))
                   ","
                   (Tactic.rwRule [] `map₂_coe)
                   ","
                   (Tactic.rwRule [] `coe_eq)]
                  "]")
                 [])
                []
                (Tactic.exact
                 "exact"
                 (Term.app
                  `h.mono
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [`i `hi]
                     []
                     "=>"
                     (Term.proj (Term.app `min_eq_left [`hi]) "." `symm)))]))])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] (Term.app `min_eq_right [`h]))
                   ","
                   (Tactic.rwRule [] `map₂_coe)
                   ","
                   (Tactic.rwRule [] `coe_eq)]
                  "]")
                 [])
                []
                (Tactic.exact
                 "exact"
                 (Term.app
                  `h.mono
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [`i `hi]
                     []
                     "=>"
                     (Term.proj (Term.app `min_eq_right [`hi]) "." `symm)))]))])])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a `b]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.cases
             "cases"
             [(Tactic.casesTarget
               []
               (Term.app
                `le_total
                [(Term.typeAscription
                  "("
                  `a
                  ":"
                  [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
                  ")")
                 `b]))]
             []
             [])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] (Term.app `min_eq_left [`h]))
                 ","
                 (Tactic.rwRule [] `map₂_coe)
                 ","
                 (Tactic.rwRule [] `coe_eq)]
                "]")
               [])
              []
              (Tactic.exact
               "exact"
               (Term.app
                `h.mono
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [`i `hi]
                   []
                   "=>"
                   (Term.proj (Term.app `min_eq_left [`hi]) "." `symm)))]))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] (Term.app `min_eq_right [`h]))
                 ","
                 (Tactic.rwRule [] `map₂_coe)
                 ","
                 (Tactic.rwRule [] `coe_eq)]
                "]")
               [])
              []
              (Tactic.exact
               "exact"
               (Term.app
                `h.mono
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [`i `hi]
                   []
                   "=>"
                   (Term.proj (Term.app `min_eq_right [`hi]) "." `symm)))]))])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.cases
           "cases"
           [(Tactic.casesTarget
             []
             (Term.app
              `le_total
              [(Term.typeAscription
                "("
                `a
                ":"
                [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
                ")")
               `b]))]
           []
           [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] (Term.app `min_eq_left [`h]))
               ","
               (Tactic.rwRule [] `map₂_coe)
               ","
               (Tactic.rwRule [] `coe_eq)]
              "]")
             [])
            []
            (Tactic.exact
             "exact"
             (Term.app
              `h.mono
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`i `hi]
                 []
                 "=>"
                 (Term.proj (Term.app `min_eq_left [`hi]) "." `symm)))]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] (Term.app `min_eq_right [`h]))
               ","
               (Tactic.rwRule [] `map₂_coe)
               ","
               (Tactic.rwRule [] `coe_eq)]
              "]")
             [])
            []
            (Tactic.exact
             "exact"
             (Term.app
              `h.mono
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`i `hi]
                 []
                 "=>"
                 (Term.proj (Term.app `min_eq_right [`hi]) "." `symm)))]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] (Term.app `min_eq_right [`h]))
           ","
           (Tactic.rwRule [] `map₂_coe)
           ","
           (Tactic.rwRule [] `coe_eq)]
          "]")
         [])
        []
        (Tactic.exact
         "exact"
         (Term.app
          `h.mono
          [(Term.fun
            "fun"
            (Term.basicFun
             [`i `hi]
             []
             "=>"
             (Term.proj (Term.app `min_eq_right [`hi]) "." `symm)))]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `h.mono
        [(Term.fun
          "fun"
          (Term.basicFun [`i `hi] [] "=>" (Term.proj (Term.app `min_eq_right [`hi]) "." `symm)))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `h.mono
       [(Term.fun
         "fun"
         (Term.basicFun [`i `hi] [] "=>" (Term.proj (Term.app `min_eq_right [`hi]) "." `symm)))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun [`i `hi] [] "=>" (Term.proj (Term.app `min_eq_right [`hi]) "." `symm)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `min_eq_right [`hi]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `min_eq_right [`hi])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hi
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `min_eq_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `min_eq_right [`hi]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hi
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h.mono
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] (Term.app `min_eq_right [`h]))
         ","
         (Tactic.rwRule [] `map₂_coe)
         ","
         (Tactic.rwRule [] `coe_eq)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map₂_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `min_eq_right [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `min_eq_right
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
          [(Tactic.rwRule [] (Term.app `min_eq_left [`h]))
           ","
           (Tactic.rwRule [] `map₂_coe)
           ","
           (Tactic.rwRule [] `coe_eq)]
          "]")
         [])
        []
        (Tactic.exact
         "exact"
         (Term.app
          `h.mono
          [(Term.fun
            "fun"
            (Term.basicFun
             [`i `hi]
             []
             "=>"
             (Term.proj (Term.app `min_eq_left [`hi]) "." `symm)))]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `h.mono
        [(Term.fun
          "fun"
          (Term.basicFun [`i `hi] [] "=>" (Term.proj (Term.app `min_eq_left [`hi]) "." `symm)))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `h.mono
       [(Term.fun
         "fun"
         (Term.basicFun [`i `hi] [] "=>" (Term.proj (Term.app `min_eq_left [`hi]) "." `symm)))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun [`i `hi] [] "=>" (Term.proj (Term.app `min_eq_left [`hi]) "." `symm)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `min_eq_left [`hi]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `min_eq_left [`hi])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hi
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `min_eq_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `min_eq_left [`hi]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hi
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h.mono
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] (Term.app `min_eq_left [`h]))
         ","
         (Tactic.rwRule [] `map₂_coe)
         ","
         (Tactic.rwRule [] `coe_eq)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map₂_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `min_eq_left [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `min_eq_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases
       "cases"
       [(Tactic.casesTarget
         []
         (Term.app
          `le_total
          [(Term.typeAscription
            "("
            `a
            ":"
            [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
            ")")
           `b]))]
       []
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le_total
       [(Term.typeAscription
         "("
         `a
         ":"
         [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
         ")")
        `b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription "(" `a ":" [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  min_def
  [ K : LinearOrder β ] ( x y : β* ) : min x y = map₂ min x y
  :=
    induction_on₂ x y
      fun
        a b
          =>
          by
            cases le_total ( a : β* ) b
              ·
                rw [ min_eq_left h , map₂_coe , coe_eq ]
                  exact h.mono fun i hi => min_eq_left hi . symm
              ·
                rw [ min_eq_right h , map₂_coe , coe_eq ]
                  exact h.mono fun i hi => min_eq_right hi . symm
#align filter.germ.min_def Filter.Germ.min_def

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `abs_def [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `LinearOrderedAddCommGroup [`β]) "]")
        (Term.explicitBinder
         "("
         [`x]
         [":" (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_» («term|___|» (group "|") `x (group) "|") "=" (Term.app `map [`abs `x]))))
      (Command.declValSimple
       ":="
       (Term.app (Term.app `induction_on [`x]) [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `rfl))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.app `induction_on [`x]) [(Term.fun "fun" (Term.basicFun [`a] [] "=>" `rfl))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`a] [] "=>" `rfl))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app `induction_on [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `induction_on
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `induction_on [`x]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_» («term|___|» (group "|") `x (group) "|") "=" (Term.app `map [`abs `x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `map [`abs `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `abs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term|___|» (group "|") `x (group) "|")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
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
  abs_def
  [ LinearOrderedAddCommGroup β ] ( x : β* ) : | x | = map abs x
  := induction_on x fun a => rfl
#align filter.germ.abs_def Filter.Germ.abs_def

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `const_max [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `LinearOrder [`β]) "]")
        (Term.explicitBinder "(" [`x `y] [":" `β] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.typeAscription
          "("
          (coeNotation "↑" (Term.typeAscription "(" (Term.app `max [`x `y]) ":" [`β] ")"))
          ":"
          [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
          ")")
         "="
         (Term.app `max [(coeNotation "↑" `x) (coeNotation "↑" `y)]))))
      (Command.declValSimple
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
             [(Tactic.rwRule [] `max_def) "," (Tactic.rwRule [] `map₂_const)]
             "]")
            [])])))
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
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `max_def) "," (Tactic.rwRule [] `map₂_const)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `max_def) "," (Tactic.rwRule [] `map₂_const)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map₂_const
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `max_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.typeAscription
        "("
        (coeNotation "↑" (Term.typeAscription "(" (Term.app `max [`x `y]) ":" [`β] ")"))
        ":"
        [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
        ")")
       "="
       (Term.app `max [(coeNotation "↑" `x) (coeNotation "↑" `y)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `max [(coeNotation "↑" `x) (coeNotation "↑" `y)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (coeNotation "↑" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 1024,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (coeNotation "↑" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 1024,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `max
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription
       "("
       (coeNotation "↑" (Term.typeAscription "(" (Term.app `max [`x `y]) ":" [`β] ")"))
       ":"
       [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    const_max
    [ LinearOrder β ] ( x y : β ) : ( ↑ ( max x y : β ) : β* ) = max ↑ x ↑ y
    := by rw [ max_def , map₂_const ]
#align filter.germ.const_max Filter.Germ.const_max

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `const_min [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `LinearOrder [`β]) "]")
        (Term.explicitBinder "(" [`x `y] [":" `β] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.typeAscription
          "("
          (coeNotation "↑" (Term.typeAscription "(" (Term.app `min [`x `y]) ":" [`β] ")"))
          ":"
          [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
          ")")
         "="
         (Term.app `min [(coeNotation "↑" `x) (coeNotation "↑" `y)]))))
      (Command.declValSimple
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
             [(Tactic.rwRule [] `min_def) "," (Tactic.rwRule [] `map₂_const)]
             "]")
            [])])))
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
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `min_def) "," (Tactic.rwRule [] `map₂_const)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `min_def) "," (Tactic.rwRule [] `map₂_const)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map₂_const
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `min_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.typeAscription
        "("
        (coeNotation "↑" (Term.typeAscription "(" (Term.app `min [`x `y]) ":" [`β] ")"))
        ":"
        [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
        ")")
       "="
       (Term.app `min [(coeNotation "↑" `x) (coeNotation "↑" `y)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `min [(coeNotation "↑" `x) (coeNotation "↑" `y)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (coeNotation "↑" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 1024,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (coeNotation "↑" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 1024,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `min
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription
       "("
       (coeNotation "↑" (Term.typeAscription "(" (Term.app `min [`x `y]) ":" [`β] ")"))
       ":"
       [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    const_min
    [ LinearOrder β ] ( x y : β ) : ( ↑ ( min x y : β ) : β* ) = min ↑ x ↑ y
    := by rw [ min_def , map₂_const ]
#align filter.germ.const_min Filter.Germ.const_min

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `const_abs [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `LinearOrderedAddCommGroup [`β]) "]")
        (Term.explicitBinder "(" [`x] [":" `β] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.typeAscription
          "("
          (coeNotation "↑" («term|___|» (group "|") `x (group) "|"))
          ":"
          [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
          ")")
         "="
         («term|___|» (group "|") (coeNotation "↑" `x) (group) "|"))))
      (Command.declValSimple
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
             [(Tactic.rwRule [] `abs_def) "," (Tactic.rwRule [] `map_const)]
             "]")
            [])])))
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
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `abs_def) "," (Tactic.rwRule [] `map_const)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `abs_def) "," (Tactic.rwRule [] `map_const)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_const
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `abs_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.typeAscription
        "("
        (coeNotation "↑" («term|___|» (group "|") `x (group) "|"))
        ":"
        [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
        ")")
       "="
       («term|___|» (group "|") (coeNotation "↑" `x) (group) "|"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term|___|» (group "|") (coeNotation "↑" `x) (group) "|")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (coeNotation "↑" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription
       "("
       (coeNotation "↑" («term|___|» (group "|") `x (group) "|"))
       ":"
       [(Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Germ.Order.Filter.FilterProduct.«termβ*» "β*")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Germ.Order.Filter.FilterProduct.«termβ*»', expected 'Filter.Germ.Order.Filter.FilterProduct.termβ*._@.Order.Filter.FilterProduct._hyg.65'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    const_abs
    [ LinearOrderedAddCommGroup β ] ( x : β ) : ( ↑ | x | : β* ) = | ↑ x |
    := by rw [ abs_def , map_const ]
#align filter.germ.const_abs Filter.Germ.const_abs

end Germ

end Filter

