/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel

! This file was ported from Lean 3 source module category_theory.preadditive.of_biproducts
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Shapes.Biproducts
import Mathbin.GroupTheory.EckmannHilton

/-!
# Constructing a semiadditive structure from binary biproducts

We show that any category with zero morphisms and binary biproducts is enriched over the category
of commutative monoids.

-/


noncomputable section

universe v u

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory.SemiadditiveOfBinaryBiproducts

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]

section

variable (X Y : C)

/-- `f +ₗ g` is the composite `X ⟶ Y ⊞ Y ⟶ Y`, where the first map is `(f, g)` and the second map
    is `(𝟙 𝟙)`. -/
@[simp]
def leftAdd (f g : X ⟶ Y) : X ⟶ Y :=
  biprod.lift f g ≫ biprod.desc (𝟙 Y) (𝟙 Y)
#align
  category_theory.semiadditive_of_binary_biproducts.left_add CategoryTheory.SemiadditiveOfBinaryBiproducts.leftAdd

/-- `f +ᵣ g` is the composite `X ⟶ X ⊞ X ⟶ Y`, where the first map is `(𝟙, 𝟙)` and the second map
    is `(f g)`. -/
@[simp]
def rightAdd (f g : X ⟶ Y) : X ⟶ Y :=
  biprod.lift (𝟙 X) (𝟙 X) ≫ biprod.desc f g
#align
  category_theory.semiadditive_of_binary_biproducts.right_add CategoryTheory.SemiadditiveOfBinaryBiproducts.rightAdd

-- mathport name: «expr +ₗ »
local infixr:65 " +ₗ " => leftAdd X Y

-- mathport name: «expr +ᵣ »
local infixr:65 " +ᵣ " => rightAdd X Y

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `is_unital_left_add [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `EckmannHilton.IsUnital
         [(Term.paren
           "("
           (CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ₗ_»
            (Term.cdot "·")
            " +ₗ "
            (Term.cdot "·"))
           ")")
          (num "0")])))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.anonymousCtor
          "⟨"
          [(Term.fun
            "fun"
            (Term.basicFun
             [`f]
             []
             "=>"
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
                   [(Tactic.simpLemma
                     []
                     []
                     (Term.show
                      "show"
                      («term_=_»
                       (Term.app
                        `biprod.lift
                        [(Term.typeAscription
                          "("
                          (num "0")
                          ":"
                          [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
                          ")")
                         `f])
                       "="
                       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                        `f
                        " ≫ "
                        `biprod.inr))
                      (Term.byTactic'
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Tactic.«tactic_<;>_»
                           (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                           "<;>"
                           (Tactic.simp "simp" [] [] [] [] []))])))))]
                   "]"]
                  [])])))))]
          "⟩")
         ","
         (Term.anonymousCtor
          "⟨"
          [(Term.fun
            "fun"
            (Term.basicFun
             [`f]
             []
             "=>"
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
                   [(Tactic.simpLemma
                     []
                     []
                     (Term.show
                      "show"
                      («term_=_»
                       (Term.app
                        `biprod.lift
                        [`f
                         (Term.typeAscription
                          "("
                          (num "0")
                          ":"
                          [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
                          ")")])
                       "="
                       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                        `f
                        " ≫ "
                        `biprod.inl))
                      (Term.byTactic'
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Tactic.«tactic_<;>_»
                           (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                           "<;>"
                           (Tactic.simp "simp" [] [] [] [] []))])))))]
                   "]"]
                  [])])))))]
          "⟩")]
        "⟩")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.anonymousCtor
         "⟨"
         [(Term.fun
           "fun"
           (Term.basicFun
            [`f]
            []
            "=>"
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
                  [(Tactic.simpLemma
                    []
                    []
                    (Term.show
                     "show"
                     («term_=_»
                      (Term.app
                       `biprod.lift
                       [(Term.typeAscription
                         "("
                         (num "0")
                         ":"
                         [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
                         ")")
                        `f])
                      "="
                      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.inr))
                     (Term.byTactic'
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.«tactic_<;>_»
                          (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                          "<;>"
                          (Tactic.simp "simp" [] [] [] [] []))])))))]
                  "]"]
                 [])])))))]
         "⟩")
        ","
        (Term.anonymousCtor
         "⟨"
         [(Term.fun
           "fun"
           (Term.basicFun
            [`f]
            []
            "=>"
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
                  [(Tactic.simpLemma
                    []
                    []
                    (Term.show
                     "show"
                     («term_=_»
                      (Term.app
                       `biprod.lift
                       [`f
                        (Term.typeAscription
                         "("
                         (num "0")
                         ":"
                         [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
                         ")")])
                      "="
                      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.inl))
                     (Term.byTactic'
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.«tactic_<;>_»
                          (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                          "<;>"
                          (Tactic.simp "simp" [] [] [] [] []))])))))]
                  "]"]
                 [])])))))]
         "⟩")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [`f]
          []
          "=>"
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
                [(Tactic.simpLemma
                  []
                  []
                  (Term.show
                   "show"
                   («term_=_»
                    (Term.app
                     `biprod.lift
                     [`f
                      (Term.typeAscription
                       "("
                       (num "0")
                       ":"
                       [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
                       ")")])
                    "="
                    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.inl))
                   (Term.byTactic'
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Tactic.«tactic_<;>_»
                        (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                        "<;>"
                        (Tactic.simp "simp" [] [] [] [] []))])))))]
                "]"]
               [])])))))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f]
        []
        "=>"
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
              [(Tactic.simpLemma
                []
                []
                (Term.show
                 "show"
                 («term_=_»
                  (Term.app
                   `biprod.lift
                   [`f
                    (Term.typeAscription
                     "("
                     (num "0")
                     ":"
                     [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
                     ")")])
                  "="
                  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.inl))
                 (Term.byTactic'
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.«tactic_<;>_»
                      (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                      "<;>"
                      (Tactic.simp "simp" [] [] [] [] []))])))))]
              "]"]
             [])])))))
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
            [(Tactic.simpLemma
              []
              []
              (Term.show
               "show"
               («term_=_»
                (Term.app
                 `biprod.lift
                 [`f
                  (Term.typeAscription
                   "("
                   (num "0")
                   ":"
                   [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
                   ")")])
                "="
                (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.inl))
               (Term.byTactic'
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.«tactic_<;>_»
                    (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                    "<;>"
                    (Tactic.simp "simp" [] [] [] [] []))])))))]
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
        [(Tactic.simpLemma
          []
          []
          (Term.show
           "show"
           («term_=_»
            (Term.app
             `biprod.lift
             [`f
              (Term.typeAscription
               "("
               (num "0")
               ":"
               [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
               ")")])
            "="
            (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.inl))
           (Term.byTactic'
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.«tactic_<;>_»
                (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                "<;>"
                (Tactic.simp "simp" [] [] [] [] []))])))))]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       («term_=_»
        (Term.app
         `biprod.lift
         [`f
          (Term.typeAscription
           "("
           (num "0")
           ":"
           [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
           ")")])
        "="
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.inl))
       (Term.byTactic'
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
            "<;>"
            (Tactic.simp "simp" [] [] [] [] []))]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
       "<;>"
       (Tactic.simp "simp" [] [] [] [] []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        `biprod.lift
        [`f
         (Term.typeAscription
          "("
          (num "0")
          ":"
          [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
          ")")])
       "="
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.inl))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.inl)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `biprod.inl
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       `biprod.lift
       [`f
        (Term.typeAscription
         "("
         (num "0")
         ":"
         [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (num "0")
       ":"
       [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 11 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `biprod.lift
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [`f]
          []
          "=>"
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
                [(Tactic.simpLemma
                  []
                  []
                  (Term.show
                   "show"
                   («term_=_»
                    (Term.app
                     `biprod.lift
                     [(Term.typeAscription
                       "("
                       (num "0")
                       ":"
                       [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
                       ")")
                      `f])
                    "="
                    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.inr))
                   (Term.byTactic'
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Tactic.«tactic_<;>_»
                        (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                        "<;>"
                        (Tactic.simp "simp" [] [] [] [] []))])))))]
                "]"]
               [])])))))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f]
        []
        "=>"
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
              [(Tactic.simpLemma
                []
                []
                (Term.show
                 "show"
                 («term_=_»
                  (Term.app
                   `biprod.lift
                   [(Term.typeAscription
                     "("
                     (num "0")
                     ":"
                     [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
                     ")")
                    `f])
                  "="
                  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.inr))
                 (Term.byTactic'
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.«tactic_<;>_»
                      (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                      "<;>"
                      (Tactic.simp "simp" [] [] [] [] []))])))))]
              "]"]
             [])])))))
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
            [(Tactic.simpLemma
              []
              []
              (Term.show
               "show"
               («term_=_»
                (Term.app
                 `biprod.lift
                 [(Term.typeAscription
                   "("
                   (num "0")
                   ":"
                   [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
                   ")")
                  `f])
                "="
                (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.inr))
               (Term.byTactic'
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.«tactic_<;>_»
                    (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                    "<;>"
                    (Tactic.simp "simp" [] [] [] [] []))])))))]
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
        [(Tactic.simpLemma
          []
          []
          (Term.show
           "show"
           («term_=_»
            (Term.app
             `biprod.lift
             [(Term.typeAscription
               "("
               (num "0")
               ":"
               [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
               ")")
              `f])
            "="
            (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.inr))
           (Term.byTactic'
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.«tactic_<;>_»
                (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                "<;>"
                (Tactic.simp "simp" [] [] [] [] []))])))))]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       («term_=_»
        (Term.app
         `biprod.lift
         [(Term.typeAscription
           "("
           (num "0")
           ":"
           [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
           ")")
          `f])
        "="
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.inr))
       (Term.byTactic'
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
            "<;>"
            (Tactic.simp "simp" [] [] [] [] []))]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
       "<;>"
       (Tactic.simp "simp" [] [] [] [] []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        `biprod.lift
        [(Term.typeAscription
          "("
          (num "0")
          ":"
          [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
          ")")
         `f])
       "="
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.inr))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `f " ≫ " `biprod.inr)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `biprod.inr
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       `biprod.lift
       [(Term.typeAscription
         "("
         (num "0")
         ":"
         [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
         ")")
        `f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription
       "("
       (num "0")
       ":"
       [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 11 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `biprod.lift
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `EckmannHilton.IsUnital
       [(Term.paren
         "("
         (CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ₗ_»
          (Term.cdot "·")
          " +ₗ "
          (Term.cdot "·"))
         ")")
        (num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.paren
       "("
       (CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ₗ_»
        (Term.cdot "·")
        " +ₗ "
        (Term.cdot "·"))
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ₗ_»
       (Term.cdot "·")
       " +ₗ "
       (Term.cdot "·"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ₗ_»', expected 'CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.term_+ₗ_._@.CategoryTheory.Preadditive.OfBiproducts._hyg.11'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  is_unital_left_add
  : EckmannHilton.IsUnital ( · +ₗ · ) 0
  :=
    ⟨
      ⟨ fun f => by simp [ show biprod.lift ( 0 : X ⟶ Y ) f = f ≫ biprod.inr by ext <;> simp ] ⟩
        ,
        ⟨ fun f => by simp [ show biprod.lift f ( 0 : X ⟶ Y ) = f ≫ biprod.inl by ext <;> simp ] ⟩
      ⟩
#align
  category_theory.semiadditive_of_binary_biproducts.is_unital_left_add CategoryTheory.SemiadditiveOfBinaryBiproducts.is_unital_left_add

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `is_unital_right_add [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `EckmannHilton.IsUnital
         [(Term.paren
           "("
           (CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ᵣ_»
            (Term.cdot "·")
            " +ᵣ "
            (Term.cdot "·"))
           ")")
          (num "0")])))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.anonymousCtor
          "⟨"
          [(Term.fun
            "fun"
            (Term.basicFun
             [`f]
             []
             "=>"
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
                   [(Tactic.simpLemma
                     []
                     []
                     (Term.show
                      "show"
                      («term_=_»
                       (Term.app
                        `biprod.desc
                        [(Term.typeAscription
                          "("
                          (num "0")
                          ":"
                          [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
                          ")")
                         `f])
                       "="
                       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                        `biprod.snd
                        " ≫ "
                        `f))
                      (Term.byTactic'
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Tactic.«tactic_<;>_»
                           (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                           "<;>"
                           (Tactic.simp "simp" [] [] [] [] []))])))))]
                   "]"]
                  [])])))))]
          "⟩")
         ","
         (Term.anonymousCtor
          "⟨"
          [(Term.fun
            "fun"
            (Term.basicFun
             [`f]
             []
             "=>"
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
                   [(Tactic.simpLemma
                     []
                     []
                     (Term.show
                      "show"
                      («term_=_»
                       (Term.app
                        `biprod.desc
                        [`f
                         (Term.typeAscription
                          "("
                          (num "0")
                          ":"
                          [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
                          ")")])
                       "="
                       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                        `biprod.fst
                        " ≫ "
                        `f))
                      (Term.byTactic'
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Tactic.«tactic_<;>_»
                           (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                           "<;>"
                           (Tactic.simp "simp" [] [] [] [] []))])))))]
                   "]"]
                  [])])))))]
          "⟩")]
        "⟩")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.anonymousCtor
         "⟨"
         [(Term.fun
           "fun"
           (Term.basicFun
            [`f]
            []
            "=>"
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
                  [(Tactic.simpLemma
                    []
                    []
                    (Term.show
                     "show"
                     («term_=_»
                      (Term.app
                       `biprod.desc
                       [(Term.typeAscription
                         "("
                         (num "0")
                         ":"
                         [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
                         ")")
                        `f])
                      "="
                      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `biprod.snd " ≫ " `f))
                     (Term.byTactic'
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.«tactic_<;>_»
                          (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                          "<;>"
                          (Tactic.simp "simp" [] [] [] [] []))])))))]
                  "]"]
                 [])])))))]
         "⟩")
        ","
        (Term.anonymousCtor
         "⟨"
         [(Term.fun
           "fun"
           (Term.basicFun
            [`f]
            []
            "=>"
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
                  [(Tactic.simpLemma
                    []
                    []
                    (Term.show
                     "show"
                     («term_=_»
                      (Term.app
                       `biprod.desc
                       [`f
                        (Term.typeAscription
                         "("
                         (num "0")
                         ":"
                         [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
                         ")")])
                      "="
                      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `biprod.fst " ≫ " `f))
                     (Term.byTactic'
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.«tactic_<;>_»
                          (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                          "<;>"
                          (Tactic.simp "simp" [] [] [] [] []))])))))]
                  "]"]
                 [])])))))]
         "⟩")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [`f]
          []
          "=>"
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
                [(Tactic.simpLemma
                  []
                  []
                  (Term.show
                   "show"
                   («term_=_»
                    (Term.app
                     `biprod.desc
                     [`f
                      (Term.typeAscription
                       "("
                       (num "0")
                       ":"
                       [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
                       ")")])
                    "="
                    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `biprod.fst " ≫ " `f))
                   (Term.byTactic'
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Tactic.«tactic_<;>_»
                        (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                        "<;>"
                        (Tactic.simp "simp" [] [] [] [] []))])))))]
                "]"]
               [])])))))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f]
        []
        "=>"
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
              [(Tactic.simpLemma
                []
                []
                (Term.show
                 "show"
                 («term_=_»
                  (Term.app
                   `biprod.desc
                   [`f
                    (Term.typeAscription
                     "("
                     (num "0")
                     ":"
                     [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
                     ")")])
                  "="
                  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `biprod.fst " ≫ " `f))
                 (Term.byTactic'
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.«tactic_<;>_»
                      (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                      "<;>"
                      (Tactic.simp "simp" [] [] [] [] []))])))))]
              "]"]
             [])])))))
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
            [(Tactic.simpLemma
              []
              []
              (Term.show
               "show"
               («term_=_»
                (Term.app
                 `biprod.desc
                 [`f
                  (Term.typeAscription
                   "("
                   (num "0")
                   ":"
                   [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
                   ")")])
                "="
                (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `biprod.fst " ≫ " `f))
               (Term.byTactic'
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.«tactic_<;>_»
                    (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                    "<;>"
                    (Tactic.simp "simp" [] [] [] [] []))])))))]
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
        [(Tactic.simpLemma
          []
          []
          (Term.show
           "show"
           («term_=_»
            (Term.app
             `biprod.desc
             [`f
              (Term.typeAscription
               "("
               (num "0")
               ":"
               [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
               ")")])
            "="
            (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `biprod.fst " ≫ " `f))
           (Term.byTactic'
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.«tactic_<;>_»
                (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                "<;>"
                (Tactic.simp "simp" [] [] [] [] []))])))))]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       («term_=_»
        (Term.app
         `biprod.desc
         [`f
          (Term.typeAscription
           "("
           (num "0")
           ":"
           [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
           ")")])
        "="
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `biprod.fst " ≫ " `f))
       (Term.byTactic'
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
            "<;>"
            (Tactic.simp "simp" [] [] [] [] []))]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
       "<;>"
       (Tactic.simp "simp" [] [] [] [] []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        `biprod.desc
        [`f
         (Term.typeAscription
          "("
          (num "0")
          ":"
          [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
          ")")])
       "="
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `biprod.fst " ≫ " `f))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `biprod.fst " ≫ " `f)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `biprod.fst
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       `biprod.desc
       [`f
        (Term.typeAscription
         "("
         (num "0")
         ":"
         [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (num "0")
       ":"
       [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 11 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `biprod.desc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [`f]
          []
          "=>"
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
                [(Tactic.simpLemma
                  []
                  []
                  (Term.show
                   "show"
                   («term_=_»
                    (Term.app
                     `biprod.desc
                     [(Term.typeAscription
                       "("
                       (num "0")
                       ":"
                       [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
                       ")")
                      `f])
                    "="
                    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `biprod.snd " ≫ " `f))
                   (Term.byTactic'
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Tactic.«tactic_<;>_»
                        (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                        "<;>"
                        (Tactic.simp "simp" [] [] [] [] []))])))))]
                "]"]
               [])])))))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f]
        []
        "=>"
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
              [(Tactic.simpLemma
                []
                []
                (Term.show
                 "show"
                 («term_=_»
                  (Term.app
                   `biprod.desc
                   [(Term.typeAscription
                     "("
                     (num "0")
                     ":"
                     [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
                     ")")
                    `f])
                  "="
                  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `biprod.snd " ≫ " `f))
                 (Term.byTactic'
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.«tactic_<;>_»
                      (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                      "<;>"
                      (Tactic.simp "simp" [] [] [] [] []))])))))]
              "]"]
             [])])))))
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
            [(Tactic.simpLemma
              []
              []
              (Term.show
               "show"
               («term_=_»
                (Term.app
                 `biprod.desc
                 [(Term.typeAscription
                   "("
                   (num "0")
                   ":"
                   [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
                   ")")
                  `f])
                "="
                (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `biprod.snd " ≫ " `f))
               (Term.byTactic'
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.«tactic_<;>_»
                    (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                    "<;>"
                    (Tactic.simp "simp" [] [] [] [] []))])))))]
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
        [(Tactic.simpLemma
          []
          []
          (Term.show
           "show"
           («term_=_»
            (Term.app
             `biprod.desc
             [(Term.typeAscription
               "("
               (num "0")
               ":"
               [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
               ")")
              `f])
            "="
            (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `biprod.snd " ≫ " `f))
           (Term.byTactic'
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.«tactic_<;>_»
                (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                "<;>"
                (Tactic.simp "simp" [] [] [] [] []))])))))]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       («term_=_»
        (Term.app
         `biprod.desc
         [(Term.typeAscription
           "("
           (num "0")
           ":"
           [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
           ")")
          `f])
        "="
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `biprod.snd " ≫ " `f))
       (Term.byTactic'
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
            "<;>"
            (Tactic.simp "simp" [] [] [] [] []))]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
       "<;>"
       (Tactic.simp "simp" [] [] [] [] []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        `biprod.desc
        [(Term.typeAscription
          "("
          (num "0")
          ":"
          [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
          ")")
         `f])
       "="
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `biprod.snd " ≫ " `f))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `biprod.snd " ≫ " `f)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `biprod.snd
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       `biprod.desc
       [(Term.typeAscription
         "("
         (num "0")
         ":"
         [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
         ")")
        `f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription
       "("
       (num "0")
       ":"
       [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 11 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `biprod.desc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `EckmannHilton.IsUnital
       [(Term.paren
         "("
         (CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ᵣ_»
          (Term.cdot "·")
          " +ᵣ "
          (Term.cdot "·"))
         ")")
        (num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.paren
       "("
       (CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ᵣ_»
        (Term.cdot "·")
        " +ᵣ "
        (Term.cdot "·"))
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ᵣ_»
       (Term.cdot "·")
       " +ᵣ "
       (Term.cdot "·"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ᵣ_»', expected 'CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.term_+ᵣ_._@.CategoryTheory.Preadditive.OfBiproducts._hyg.70'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  is_unital_right_add
  : EckmannHilton.IsUnital ( · +ᵣ · ) 0
  :=
    ⟨
      ⟨ fun f => by simp [ show biprod.desc ( 0 : X ⟶ Y ) f = biprod.snd ≫ f by ext <;> simp ] ⟩
        ,
        ⟨ fun f => by simp [ show biprod.desc f ( 0 : X ⟶ Y ) = biprod.fst ≫ f by ext <;> simp ] ⟩
      ⟩
#align
  category_theory.semiadditive_of_binary_biproducts.is_unital_right_add CategoryTheory.SemiadditiveOfBinaryBiproducts.is_unital_right_add

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `distrib [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`f `g `h `k]
         [":" (Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ₗ_»
          (CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ᵣ_»
           `f
           " +ᵣ "
           `g)
          " +ₗ "
          (CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ᵣ_»
           `h
           " +ᵣ "
           `k))
         "="
         (CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ᵣ_»
          (CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ₗ_»
           `f
           " +ₗ "
           `h)
          " +ᵣ "
          (CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ₗ_»
           `g
           " +ₗ "
           `k)))))
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
              `diag
              []
              [(Term.typeSpec
                ":"
                (Combinatorics.Quiver.Basic.«term_⟶_»
                 (CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Biproducts.«term_⊞_»
                  `X
                  " ⊞ "
                  `X)
                 " ⟶ "
                 (CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Biproducts.«term_⊞_»
                  `Y
                  " ⊞ "
                  `Y)))]
              ":="
              (Term.app
               `biprod.lift
               [(Term.app `biprod.desc [`f `g]) (Term.app `biprod.desc [`h `k])]))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hd₁ []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `biprod.inl " ≫ " `diag)
                 "="
                 (Term.app `biprod.lift [`f `h])))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.«tactic_<;>_»
                   (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                   "<;>"
                   (Tactic.simp "simp" [] [] [] [] []))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hd₂ []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `biprod.inr " ≫ " `diag)
                 "="
                 (Term.app `biprod.lift [`g `k])))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.«tactic_<;>_»
                   (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                   "<;>"
                   (Tactic.simp "simp" [] [] [] [] []))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`h₁ []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Term.app
                  `biprod.lift
                  [(CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ᵣ_»
                    `f
                    " +ᵣ "
                    `g)
                   (CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ᵣ_»
                    `h
                    " +ᵣ "
                    `k)])
                 "="
                 (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                  (Term.app
                   `biprod.lift
                   [(Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [`X])
                    (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [`X])])
                  " ≫ "
                  `diag)))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.«tactic_<;>_»
                   (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                   "<;>"
                   (Tactic.simp "simp" [] [] [] [] []))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`h₂ []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                  `diag
                  " ≫ "
                  (Term.app
                   `biprod.desc
                   [(Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [`Y])
                    (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [`Y])]))
                 "="
                 (Term.app
                  `biprod.desc
                  [(CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ₗ_»
                    `f
                    " +ₗ "
                    `h)
                   (CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ₗ_»
                    `g
                    " +ₗ "
                    `k)])))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.«tactic_<;>_»
                   (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                   "<;>"
                   (Tactic.simp
                    "simp"
                    []
                    []
                    []
                    ["["
                     [(Tactic.simpLemma [] [] (Term.app `reassoc_of [`hd₁]))
                      ","
                      (Tactic.simpLemma [] [] (Term.app `reassoc_of [`hd₂]))]
                     "]"]
                    []))]))))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `leftAdd)
              ","
              (Tactic.rwRule [] `h₁)
              ","
              (Tactic.rwRule [] `category.assoc)
              ","
              (Tactic.rwRule [] `h₂)
              ","
              (Tactic.rwRule [] `rightAdd)]
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
         [(Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `diag
             []
             [(Term.typeSpec
               ":"
               (Combinatorics.Quiver.Basic.«term_⟶_»
                (CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Biproducts.«term_⊞_»
                 `X
                 " ⊞ "
                 `X)
                " ⟶ "
                (CategoryTheory.Limits.CategoryTheory.Limits.Shapes.Biproducts.«term_⊞_»
                 `Y
                 " ⊞ "
                 `Y)))]
             ":="
             (Term.app
              `biprod.lift
              [(Term.app `biprod.desc [`f `g]) (Term.app `biprod.desc [`h `k])]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hd₁ []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `biprod.inl " ≫ " `diag)
                "="
                (Term.app `biprod.lift [`f `h])))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.«tactic_<;>_»
                  (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                  "<;>"
                  (Tactic.simp "simp" [] [] [] [] []))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hd₂ []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `biprod.inr " ≫ " `diag)
                "="
                (Term.app `biprod.lift [`g `k])))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.«tactic_<;>_»
                  (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                  "<;>"
                  (Tactic.simp "simp" [] [] [] [] []))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h₁ []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.app
                 `biprod.lift
                 [(CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ᵣ_»
                   `f
                   " +ᵣ "
                   `g)
                  (CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ᵣ_»
                   `h
                   " +ᵣ "
                   `k)])
                "="
                (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                 (Term.app
                  `biprod.lift
                  [(Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [`X])
                   (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [`X])])
                 " ≫ "
                 `diag)))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.«tactic_<;>_»
                  (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                  "<;>"
                  (Tactic.simp "simp" [] [] [] [] []))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h₂ []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                 `diag
                 " ≫ "
                 (Term.app
                  `biprod.desc
                  [(Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [`Y])
                   (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [`Y])]))
                "="
                (Term.app
                 `biprod.desc
                 [(CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ₗ_»
                   `f
                   " +ₗ "
                   `h)
                  (CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ₗ_»
                   `g
                   " +ₗ "
                   `k)])))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.«tactic_<;>_»
                  (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                  "<;>"
                  (Tactic.simp
                   "simp"
                   []
                   []
                   []
                   ["["
                    [(Tactic.simpLemma [] [] (Term.app `reassoc_of [`hd₁]))
                     ","
                     (Tactic.simpLemma [] [] (Term.app `reassoc_of [`hd₂]))]
                    "]"]
                   []))]))))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `leftAdd)
             ","
             (Tactic.rwRule [] `h₁)
             ","
             (Tactic.rwRule [] `category.assoc)
             ","
             (Tactic.rwRule [] `h₂)
             ","
             (Tactic.rwRule [] `rightAdd)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `leftAdd)
         ","
         (Tactic.rwRule [] `h₁)
         ","
         (Tactic.rwRule [] `category.assoc)
         ","
         (Tactic.rwRule [] `h₂)
         ","
         (Tactic.rwRule [] `rightAdd)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rightAdd
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `category.assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `leftAdd
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`h₂ []]
         [(Term.typeSpec
           ":"
           («term_=_»
            (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
             `diag
             " ≫ "
             (Term.app
              `biprod.desc
              [(Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [`Y])
               (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [`Y])]))
            "="
            (Term.app
             `biprod.desc
             [(CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ₗ_»
               `f
               " +ₗ "
               `h)
              (CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ₗ_»
               `g
               " +ₗ "
               `k)])))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.«tactic_<;>_»
              (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
              "<;>"
              (Tactic.simp
               "simp"
               []
               []
               []
               ["["
                [(Tactic.simpLemma [] [] (Term.app `reassoc_of [`hd₁]))
                 ","
                 (Tactic.simpLemma [] [] (Term.app `reassoc_of [`hd₂]))]
                "]"]
               []))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
           "<;>"
           (Tactic.simp
            "simp"
            []
            []
            []
            ["["
             [(Tactic.simpLemma [] [] (Term.app `reassoc_of [`hd₁]))
              ","
              (Tactic.simpLemma [] [] (Term.app `reassoc_of [`hd₂]))]
             "]"]
            []))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
       "<;>"
       (Tactic.simp
        "simp"
        []
        []
        []
        ["["
         [(Tactic.simpLemma [] [] (Term.app `reassoc_of [`hd₁]))
          ","
          (Tactic.simpLemma [] [] (Term.app `reassoc_of [`hd₂]))]
         "]"]
        []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpLemma [] [] (Term.app `reassoc_of [`hd₁]))
         ","
         (Tactic.simpLemma [] [] (Term.app `reassoc_of [`hd₂]))]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `reassoc_of [`hd₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hd₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `reassoc_of
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `reassoc_of [`hd₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hd₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `reassoc_of
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        `diag
        " ≫ "
        (Term.app
         `biprod.desc
         [(Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [`Y])
          (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [`Y])]))
       "="
       (Term.app
        `biprod.desc
        [(CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ₗ_»
          `f
          " +ₗ "
          `h)
         (CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ₗ_»
          `g
          " +ₗ "
          `k)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `biprod.desc
       [(CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ₗ_»
         `f
         " +ₗ "
         `h)
        (CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ₗ_»
         `g
         " +ₗ "
         `k)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ₗ_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ₗ_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ₗ_»
       `g
       " +ₗ "
       `k)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ₗ_»', expected 'CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.term_+ₗ_._@.CategoryTheory.Preadditive.OfBiproducts._hyg.11'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
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
  distrib
  ( f g h k : X ⟶ Y ) : f +ᵣ g +ₗ h +ᵣ k = f +ₗ h +ᵣ g +ₗ k
  :=
    by
      let diag : X ⊞ X ⟶ Y ⊞ Y := biprod.lift biprod.desc f g biprod.desc h k
        have hd₁ : biprod.inl ≫ diag = biprod.lift f h := by ext <;> simp
        have hd₂ : biprod.inr ≫ diag = biprod.lift g k := by ext <;> simp
        have h₁ : biprod.lift f +ᵣ g h +ᵣ k = biprod.lift 𝟙 X 𝟙 X ≫ diag := by ext <;> simp
        have
          h₂
            : diag ≫ biprod.desc 𝟙 Y 𝟙 Y = biprod.desc f +ₗ h g +ₗ k
            :=
            by ext <;> simp [ reassoc_of hd₁ , reassoc_of hd₂ ]
        rw [ leftAdd , h₁ , category.assoc , h₂ , rightAdd ]
#align
  category_theory.semiadditive_of_binary_biproducts.distrib CategoryTheory.SemiadditiveOfBinaryBiproducts.distrib

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "In a category with binary biproducts, the morphisms form a commutative monoid. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `addCommMonoidHomOfHasBinaryBiproducts [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.app `AddCommMonoid [(Combinatorics.Quiver.Basic.«term_⟶_» `X " ⟶ " `Y)]))])
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `add
           []
           []
           ":="
           (Term.paren
            "("
            (CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ᵣ_»
             (Term.cdot "·")
             " +ᵣ "
             (Term.cdot "·"))
            ")"))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `add_assoc
           []
           []
           ":="
           (Term.proj
            (Term.app
             `EckmannHilton.mul_assoc
             [(Term.app `is_unital_left_add [`X `Y])
              (Term.app `is_unital_right_add [`X `Y])
              (Term.app `distrib [`X `Y])])
            "."
            `assoc))))
        []
        (Command.whereStructField (Term.letDecl (Term.letIdDecl `zero [] [] ":=" (num "0"))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `zero_add
           []
           []
           ":="
           (Term.proj (Term.app `is_unital_right_add [`X `Y]) "." `left_id))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `add_zero
           []
           []
           ":="
           (Term.proj (Term.app `is_unital_right_add [`X `Y]) "." `right_id))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `add_comm
           []
           []
           ":="
           (Term.proj
            (Term.app
             `EckmannHilton.mul_comm
             [(Term.app `is_unital_left_add [`X `Y])
              (Term.app `is_unital_right_add [`X `Y])
              (Term.app `distrib [`X `Y])])
            "."
            `comm))))]
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        `EckmannHilton.mul_comm
        [(Term.app `is_unital_left_add [`X `Y])
         (Term.app `is_unital_right_add [`X `Y])
         (Term.app `distrib [`X `Y])])
       "."
       `comm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `EckmannHilton.mul_comm
       [(Term.app `is_unital_left_add [`X `Y])
        (Term.app `is_unital_right_add [`X `Y])
        (Term.app `distrib [`X `Y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `distrib [`X `Y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `distrib
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `distrib [`X `Y]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `is_unital_right_add [`X `Y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_unital_right_add
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `is_unital_right_add [`X `Y])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `is_unital_left_add [`X `Y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_unital_left_add
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `is_unital_left_add [`X `Y])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `EckmannHilton.mul_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `EckmannHilton.mul_comm
      [(Term.paren "(" (Term.app `is_unital_left_add [`X `Y]) ")")
       (Term.paren "(" (Term.app `is_unital_right_add [`X `Y]) ")")
       (Term.paren "(" (Term.app `distrib [`X `Y]) ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `is_unital_right_add [`X `Y]) "." `right_id)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `is_unital_right_add [`X `Y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_unital_right_add
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `is_unital_right_add [`X `Y])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `is_unital_right_add [`X `Y]) "." `left_id)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `is_unital_right_add [`X `Y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_unital_right_add
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `is_unital_right_add [`X `Y])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        `EckmannHilton.mul_assoc
        [(Term.app `is_unital_left_add [`X `Y])
         (Term.app `is_unital_right_add [`X `Y])
         (Term.app `distrib [`X `Y])])
       "."
       `assoc)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `EckmannHilton.mul_assoc
       [(Term.app `is_unital_left_add [`X `Y])
        (Term.app `is_unital_right_add [`X `Y])
        (Term.app `distrib [`X `Y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `distrib [`X `Y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `distrib
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `distrib [`X `Y]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `is_unital_right_add [`X `Y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_unital_right_add
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `is_unital_right_add [`X `Y])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `is_unital_left_add [`X `Y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_unital_left_add
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `is_unital_left_add [`X `Y])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `EckmannHilton.mul_assoc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `EckmannHilton.mul_assoc
      [(Term.paren "(" (Term.app `is_unital_left_add [`X `Y]) ")")
       (Term.paren "(" (Term.app `is_unital_right_add [`X `Y]) ")")
       (Term.paren "(" (Term.app `distrib [`X `Y]) ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.paren
       "("
       (CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ᵣ_»
        (Term.cdot "·")
        " +ᵣ "
        (Term.cdot "·"))
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ᵣ_»
       (Term.cdot "·")
       " +ᵣ "
       (Term.cdot "·"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.«term_+ᵣ_»', expected 'CategoryTheory.SemiadditiveOfBinaryBiproducts.CategoryTheory.Preadditive.OfBiproducts.term_+ᵣ_._@.CategoryTheory.Preadditive.OfBiproducts._hyg.70'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- In a category with binary biproducts, the morphisms form a commutative monoid. -/
  def
    addCommMonoidHomOfHasBinaryBiproducts
    : AddCommMonoid X ⟶ Y
    where
      add := ( · +ᵣ · )
        add_assoc
          :=
          EckmannHilton.mul_assoc is_unital_left_add X Y is_unital_right_add X Y distrib X Y . assoc
        zero := 0
        zero_add := is_unital_right_add X Y . left_id
        add_zero := is_unital_right_add X Y . right_id
        add_comm
          :=
          EckmannHilton.mul_comm is_unital_left_add X Y is_unital_right_add X Y distrib X Y . comm
#align
  category_theory.semiadditive_of_binary_biproducts.add_comm_monoid_hom_of_has_binary_biproducts CategoryTheory.SemiadditiveOfBinaryBiproducts.addCommMonoidHomOfHasBinaryBiproducts

end

section

variable {X Y Z : C}

attribute [local instance] add_comm_monoid_hom_of_has_binary_biproducts

theorem add_eq_right_addition (f g : X ⟶ Y) : f + g = biprod.lift (𝟙 X) (𝟙 X) ≫ biprod.desc f g :=
  rfl
#align
  category_theory.semiadditive_of_binary_biproducts.add_eq_right_addition CategoryTheory.SemiadditiveOfBinaryBiproducts.add_eq_right_addition

theorem add_eq_left_addition (f g : X ⟶ Y) : f + g = biprod.lift f g ≫ biprod.desc (𝟙 Y) (𝟙 Y) :=
  congr_fun₂
    (EckmannHilton.mul (is_unital_left_add X Y) (is_unital_right_add X Y) (distrib X Y)).symm f g
#align
  category_theory.semiadditive_of_binary_biproducts.add_eq_left_addition CategoryTheory.SemiadditiveOfBinaryBiproducts.add_eq_left_addition

theorem add_comp (f g : X ⟶ Y) (h : Y ⟶ Z) : (f + g) ≫ h = f ≫ h + g ≫ h :=
  by
  simp only [add_eq_right_addition, category.assoc]
  congr
  ext <;> simp
#align
  category_theory.semiadditive_of_binary_biproducts.add_comp CategoryTheory.SemiadditiveOfBinaryBiproducts.add_comp

theorem comp_add (f : X ⟶ Y) (g h : Y ⟶ Z) : f ≫ (g + h) = f ≫ g + f ≫ h :=
  by
  simp only [add_eq_left_addition, ← category.assoc]
  congr
  ext <;> simp
#align
  category_theory.semiadditive_of_binary_biproducts.comp_add CategoryTheory.SemiadditiveOfBinaryBiproducts.comp_add

end

end CategoryTheory.SemiadditiveOfBinaryBiproducts

