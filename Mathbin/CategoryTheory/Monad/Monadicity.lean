/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.monad.monadicity
! leanprover-community/mathlib commit 5a3e819569b0f12cbec59d740a2613018e7b8eec
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathbin.CategoryTheory.Limits.Shapes.Reflexive
import Mathbin.CategoryTheory.Monad.Coequalizer
import Mathbin.CategoryTheory.Monad.Limits

/-!
# Monadicity theorems

We prove monadicity theorems which can establish a given functor is monadic. In particular, we
show three versions of Beck's monadicity theorem, and the reflexive (crude) monadicity theorem:

`G` is a monadic right adjoint if it has a right adjoint, and:

* `D` has, `G` preserves and reflects `G`-split coequalizers, see
  `category_theory.monad.monadic_of_has_preserves_reflects_G_split_coequalizers`
* `G` creates `G`-split coequalizers, see
  `category_theory.monad.monadic_of_creates_G_split_coequalizers`
  (The converse of this is also shown, see
   `category_theory.monad.creates_G_split_coequalizers_of_monadic`)
* `D` has and `G` preserves `G`-split coequalizers, and `G` reflects isomorphisms, see
  `category_theory.monad.monadic_of_has_preserves_G_split_coequalizers_of_reflects_isomorphisms`
* `D` has and `G` preserves reflexive coequalizers, and `G` reflects isomorphisms, see
  `category_theory.monad.monadic_of_has_preserves_reflexive_coequalizers_of_reflects_isomorphisms`

## Tags

Beck, monadicity, descent

## TODO

Dualise to show comonadicity theorems.
-/


universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Monad

open Limits

noncomputable section

-- Hide the implementation details in this namespace.
namespace MonadicityInternal

section

-- We use these parameters and notations to simplify the statements of internal constructions
-- here.
parameter {C : Type u₁}{D : Type u₂}

parameter [Category.{v₁} C][Category.{v₁} D]

parameter {G : D ⥤ C}[IsRightAdjoint G]

-- mathport name: exprF
-- An unfortunate consequence of the local notation is that it is only recognised if there is an
-- extra space after the reference.
local notation "F" => leftAdjoint G

-- mathport name: expradj
local notation "adj" => Adjunction.ofRightAdjoint G

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The \"main pair\" for an algebra `(A, α)` is the pair of morphisms `(F α, ε_FA)`. It is always a\nreflexive pair, and will be used to construct the left adjoint to the comparison functor and show it\nis an equivalence.\n-/")]
      []
      []
      []
      []
      [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `main_pair_reflexive [])]
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`A]
         [":"
          (Term.proj
           (Term.proj
            (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
            "."
            `toMonad)
           "."
           `Algebra)]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `IsReflexivePair
         [(Term.app
           (Term.proj
            (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
            "."
            `map)
           [(Term.proj `A "." `a)])
          (Term.app
           (Term.proj
            (Term.proj
             (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
             "."
             `counit)
            "."
            `app)
           [(Term.app
             (Term.proj
              (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
              "."
              `obj)
             [(Term.proj `A "." `A)])])])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.apply
            "apply"
            (Term.app
             `is_reflexive_pair.mk'
             [(Term.app
               (Term.proj
                (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
                "."
                `map)
               [(Term.app
                 (Term.proj
                  (Term.proj
                   (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                    "adj")
                   "."
                   `Unit)
                  "."
                  `app)
                 [(Term.hole "_")])])
              (Term.hole "_")
              (Term.hole "_")]))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 (Term.proj
                  (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF
                   "F")
                  "."
                  `map_comp))
                ","
                (Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 (Term.proj
                  (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF
                   "F")
                  "."
                  `map_id))]
               "]")
              [])
             []
             (Tactic.exact
              "exact"
              (Term.app
               `congr_arg
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.hole "_")]
                  []
                  "=>"
                  (Term.app
                   (Term.proj
                    (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF
                     "F")
                    "."
                    `map)
                   [(Term.hole "_")])))
                `A.unit]))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 []
                 (Term.proj
                  (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                   "adj")
                  "."
                  `left_triangle_components))]
               "]")
              [])
             []
             (Tactic.tacticRfl "rfl")])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.apply
           "apply"
           (Term.app
            `is_reflexive_pair.mk'
            [(Term.app
              (Term.proj
               (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
               "."
               `map)
              [(Term.app
                (Term.proj
                 (Term.proj
                  (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                   "adj")
                  "."
                  `Unit)
                 "."
                 `app)
                [(Term.hole "_")])])
             (Term.hole "_")
             (Term.hole "_")]))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.proj
                 (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
                 "."
                 `map_comp))
               ","
               (Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.proj
                 (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
                 "."
                 `map_id))]
              "]")
             [])
            []
            (Tactic.exact
             "exact"
             (Term.app
              `congr_arg
              [(Term.fun
                "fun"
                (Term.basicFun
                 [(Term.hole "_")]
                 []
                 "=>"
                 (Term.app
                  (Term.proj
                   (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF
                    "F")
                   "."
                   `map)
                  [(Term.hole "_")])))
               `A.unit]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                []
                (Term.proj
                 (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                  "adj")
                 "."
                 `left_triangle_components))]
              "]")
             [])
            []
            (Tactic.tacticRfl "rfl")])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            []
            (Term.proj
             (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
             "."
             `left_triangle_components))]
          "]")
         [])
        []
        (Tactic.tacticRfl "rfl")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          []
          (Term.proj
           (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
           "."
           `left_triangle_components))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
       "."
       `left_triangle_components)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj', expected 'CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj._@.CategoryTheory.Monad.Monadicity._hyg.534'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The "main pair" for an algebra `(A, α)` is the pair of morphisms `(F α, ε_FA)`. It is always a
    reflexive pair, and will be used to construct the left adjoint to the comparison functor and show it
    is an equivalence.
    -/
  instance
    main_pair_reflexive
    ( A : adj . toMonad . Algebra ) : IsReflexivePair F . map A . a adj . counit . app F . obj A . A
    :=
      by
        apply is_reflexive_pair.mk' F . map adj . Unit . app _ _ _
          · rw [ ← F . map_comp , ← F . map_id ] exact congr_arg fun _ => F . map _ A.unit
          · rw [ adj . left_triangle_components ] rfl
#align
  category_theory.monad.monadicity_internal.main_pair_reflexive CategoryTheory.Monad.MonadicityInternal.main_pair_reflexive

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The \"main pair\" for an algebra `(A, α)` is the pair of morphisms `(F α, ε_FA)`. It is always a\n`G`-split pair, and will be used to construct the left adjoint to the comparison functor and show it\nis an equivalence.\n-/")]
      []
      []
      []
      []
      [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `main_pair_G_split [])]
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`A]
         [":"
          (Term.proj
           (Term.proj
            (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
            "."
            `toMonad)
           "."
           `Algebra)]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         (Term.proj `G "." `IsSplitPair)
         [(Term.app
           (Term.proj
            (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
            "."
            `map)
           [(Term.proj `A "." `a)])
          (Term.app
           (Term.proj
            (Term.proj
             (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
             "."
             `counit)
            "."
            `app)
           [(Term.app
             (Term.proj
              (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
              "."
              `obj)
             [(Term.proj `A "." `A)])])])))
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `splittable
           []
           []
           ":="
           (Term.anonymousCtor
            "⟨"
            [(Term.hole "_")
             ","
             (Term.hole "_")
             ","
             (Term.anonymousCtor "⟨" [(Term.app `beckSplitCoequalizer [`A])] "⟩")]
            "⟩"))))]
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.hole "_")
        ","
        (Term.hole "_")
        ","
        (Term.anonymousCtor "⟨" [(Term.app `beckSplitCoequalizer [`A])] "⟩")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.app `beckSplitCoequalizer [`A])] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `beckSplitCoequalizer [`A])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `beckSplitCoequalizer
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       (Term.proj `G "." `IsSplitPair)
       [(Term.app
         (Term.proj
          (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
          "."
          `map)
         [(Term.proj `A "." `a)])
        (Term.app
         (Term.proj
          (Term.proj
           (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
           "."
           `counit)
          "."
          `app)
         [(Term.app
           (Term.proj
            (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
            "."
            `obj)
           [(Term.proj `A "." `A)])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.proj
         (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
         "."
         `counit)
        "."
        `app)
       [(Term.app
         (Term.proj
          (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
          "."
          `obj)
         [(Term.proj `A "." `A)])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
        "."
        `obj)
       [(Term.proj `A "." `A)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `A "." `A)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `A
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
       "."
       `obj)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF', expected 'CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF._@.CategoryTheory.Monad.Monadicity._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The "main pair" for an algebra `(A, α)` is the pair of morphisms `(F α, ε_FA)`. It is always a
    `G`-split pair, and will be used to construct the left adjoint to the comparison functor and show it
    is an equivalence.
    -/
  instance
    main_pair_G_split
    ( A : adj . toMonad . Algebra ) : G . IsSplitPair F . map A . a adj . counit . app F . obj A . A
    where splittable := ⟨ _ , _ , ⟨ beckSplitCoequalizer A ⟩ ⟩
#align
  category_theory.monad.monadicity_internal.main_pair_G_split CategoryTheory.Monad.MonadicityInternal.main_pair_G_split

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The object function for the left adjoint to the comparison functor. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `comparisonLeftAdjointObj [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`A]
         [":"
          (Term.proj
           (Term.proj
            (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
            "."
            `toMonad)
           "."
           `Algebra)]
         []
         ")")
        (Term.instBinder
         "["
         []
         (Term.app
          `HasCoequalizer
          [(Term.app
            (Term.proj
             (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
             "."
             `map)
            [(Term.proj `A "." `a)])
           (Term.app
            (Term.proj
             (Term.proj
              (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
               "adj")
              "."
              `counit)
             "."
             `app)
            [(Term.hole "_")])])
         "]")]
       [(Term.typeSpec ":" `D)])
      (Command.declValSimple
       ":="
       (Term.app
        `coequalizer
        [(Term.app
          (Term.proj
           (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
           "."
           `map)
          [(Term.proj `A "." `a)])
         (Term.app
          (Term.proj
           (Term.proj
            (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
            "."
            `counit)
           "."
           `app)
          [(Term.hole "_")])])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `coequalizer
       [(Term.app
         (Term.proj
          (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
          "."
          `map)
         [(Term.proj `A "." `a)])
        (Term.app
         (Term.proj
          (Term.proj
           (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
           "."
           `counit)
          "."
          `app)
         [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.proj
         (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
         "."
         `counit)
        "."
        `app)
       [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.proj
        (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
        "."
        `counit)
       "."
       `app)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
       "."
       `counit)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj', expected 'CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj._@.CategoryTheory.Monad.Monadicity._hyg.534'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The object function for the left adjoint to the comparison functor. -/
  def
    comparisonLeftAdjointObj
    ( A : adj . toMonad . Algebra ) [ HasCoequalizer F . map A . a adj . counit . app _ ] : D
    := coequalizer F . map A . a adj . counit . app _
#align
  category_theory.monad.monadicity_internal.comparison_left_adjoint_obj CategoryTheory.Monad.MonadicityInternal.comparisonLeftAdjointObj

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "We have a bijection of homsets which will be used to construct the left adjoint to the comparison\nfunctor.\n-/")]
      [(Term.attributes
        "@["
        [(Term.attrInstance (Term.attrKind []) (Attr.simps "simps" [] (Attr.simpsArgsRest [] [])))]
        "]")]
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `comparisonLeftAdjointHomEquiv [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`A]
         [":"
          (Term.proj
           (Term.proj
            (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
            "."
            `toMonad)
           "."
           `Algebra)]
         []
         ")")
        (Term.explicitBinder "(" [`B] [":" `D] [] ")")
        (Term.instBinder
         "["
         []
         (Term.app
          `HasCoequalizer
          [(Term.app
            (Term.proj
             (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
             "."
             `map)
            [(Term.proj `A "." `a)])
           (Term.app
            (Term.proj
             (Term.proj
              (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
               "adj")
              "."
              `counit)
             "."
             `app)
            [(Term.app
              (Term.proj
               (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
               "."
               `obj)
              [(Term.proj `A "." `A)])])])
         "]")]
       [(Term.typeSpec
         ":"
         (Logic.Equiv.Defs.«term_≃_»
          (Combinatorics.Quiver.Basic.«term_⟶_»
           (Term.app `comparison_left_adjoint_obj [`A])
           " ⟶ "
           `B)
          " ≃ "
          (Combinatorics.Quiver.Basic.«term_⟶_»
           `A
           " ⟶ "
           (Term.app
            (Term.proj
             (Term.app
              `comparison
              [(CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                "adj")])
             "."
             `obj)
            [`B]))))])
      (Command.declValSimple
       ":="
       (calc
        "calc"
        (calcStep
         (Logic.Equiv.Defs.«term_≃_»
          (Combinatorics.Quiver.Basic.«term_⟶_»
           (Term.app `comparison_left_adjoint_obj [`A])
           " ⟶ "
           `B)
          " ≃ "
          («term{_:_//_}»
           "{"
           `f
           [":"
            (Combinatorics.Quiver.Basic.«term_⟶_»
             (Term.app
              (Term.proj
               (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
               "."
               `obj)
              [(Term.proj `A "." `A)])
             " ⟶ "
             `B)]
           "//"
           (Term.hole "_")
           "}"))
         ":="
         (Term.app `Cofork.IsColimit.homIso [(Term.app `colimit.isColimit [(Term.hole "_")]) `B]))
        [(calcStep
          (Logic.Equiv.Defs.«term_≃_»
           (Term.hole "_")
           " ≃ "
           («term{_:_//_}»
            "{"
            `g
            [":"
             (Combinatorics.Quiver.Basic.«term_⟶_»
              (Term.proj `A "." `A)
              " ⟶ "
              (Term.app (Term.proj `G "." `obj) [`B]))]
            "//"
            («term_=_»
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
              (Term.app
               (Term.proj `G "." `map)
               [(Term.app
                 (Term.proj
                  (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF
                   "F")
                  "."
                  `map)
                 [`g])])
              " ≫ "
              (Term.app
               (Term.proj `G "." `map)
               [(Term.app
                 (Term.proj
                  (Term.proj
                   (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                    "adj")
                   "."
                   `counit)
                  "."
                  `app)
                 [`B])]))
             "="
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
              (Term.proj `A "." `a)
              " ≫ "
              `g))
            "}"))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.refine'
               "refine'"
               (Term.app
                (Term.proj
                 (Term.app
                  (Term.proj
                   (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                    "adj")
                   "."
                   `homEquiv)
                  [(Term.hole "_") (Term.hole "_")])
                 "."
                 `subtypeEquiv)
                [(Term.hole "_")]))
              []
              (Tactic.intro "intro" [`f])
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule
                  [(patternIgnore (token.«← » "←"))]
                  (Term.proj
                   (Term.proj
                    (Term.app
                     (Term.proj
                      (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                       "adj")
                      "."
                      `homEquiv)
                     [(Term.hole "_") (Term.hole "_")])
                    "."
                    `Injective)
                   "."
                   `eq_iff))
                 ","
                 (Tactic.rwRule [] `adjunction.hom_equiv_naturality_left)
                 ","
                 (Tactic.rwRule
                  []
                  (Term.proj
                   (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                    "adj")
                   "."
                   `hom_equiv_unit))
                 ","
                 (Tactic.rwRule
                  []
                  (Term.proj
                   (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                    "adj")
                   "."
                   `hom_equiv_unit))
                 ","
                 (Tactic.rwRule [] `G.map_comp)]
                "]")
               [])
              []
              (Tactic.dsimp "dsimp" [] [] [] [] [])
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule
                  []
                  (Term.proj
                   (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                    "adj")
                   "."
                   `right_triangle_components_assoc))
                 ","
                 (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `G.map_comp)
                 ","
                 (Tactic.rwRule
                  []
                  (Term.proj
                   (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF
                    "F")
                   "."
                   `map_comp))
                 ","
                 (Tactic.rwRule [] `category.assoc)
                 ","
                 (Tactic.rwRule
                  []
                  (Term.proj
                   (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                    "adj")
                   "."
                   `counit_naturality))
                 ","
                 (Tactic.rwRule
                  []
                  (Term.proj
                   (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                    "adj")
                   "."
                   `left_triangle_components_assoc))]
                "]")
               [])
              []
              (Tactic.apply "apply" `eq_comm)]))))
         (calcStep
          (Logic.Equiv.Defs.«term_≃_»
           (Term.hole "_")
           " ≃ "
           (Combinatorics.Quiver.Basic.«term_⟶_»
            `A
            " ⟶ "
            (Term.app
             (Term.proj
              (Term.app
               `comparison
               [(CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                 "adj")])
              "."
              `obj)
             [`B])))
          ":="
          (Term.structInst
           "{"
           []
           [(Term.structInstField
             (Term.structInstLVal `toFun [])
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`g]
               []
               "=>"
               (Term.structInst
                "{"
                []
                [(Term.structInstField (Term.structInstLVal `f []) ":=" (Term.hole "_"))
                 []
                 (Term.structInstField (Term.structInstLVal `h' []) ":=" (Term.proj `g "." `Prop))]
                (Term.optEllipsis [])
                []
                "}"))))
            []
            (Term.structInstField
             (Term.structInstLVal `invFun [])
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`f]
               []
               "=>"
               (Term.anonymousCtor "⟨" [(Term.proj `f "." `f) "," (Term.proj `f "." `h)] "⟩"))))
            []
            (Term.structInstField
             (Term.structInstLVal `left_inv [])
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`g]
               []
               "=>"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] []) ";" (Tactic.tacticRfl "rfl")]))))))
            []
            (Term.structInstField
             (Term.structInstLVal `right_inv [])
             ":="
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
                  [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
                   ";"
                   (Tactic.tacticRfl "rfl")]))))))]
           (Term.optEllipsis [])
           []
           "}"))])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calc
       "calc"
       (calcStep
        (Logic.Equiv.Defs.«term_≃_»
         (Combinatorics.Quiver.Basic.«term_⟶_»
          (Term.app `comparison_left_adjoint_obj [`A])
          " ⟶ "
          `B)
         " ≃ "
         («term{_:_//_}»
          "{"
          `f
          [":"
           (Combinatorics.Quiver.Basic.«term_⟶_»
            (Term.app
             (Term.proj
              (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
              "."
              `obj)
             [(Term.proj `A "." `A)])
            " ⟶ "
            `B)]
          "//"
          (Term.hole "_")
          "}"))
        ":="
        (Term.app `Cofork.IsColimit.homIso [(Term.app `colimit.isColimit [(Term.hole "_")]) `B]))
       [(calcStep
         (Logic.Equiv.Defs.«term_≃_»
          (Term.hole "_")
          " ≃ "
          («term{_:_//_}»
           "{"
           `g
           [":"
            (Combinatorics.Quiver.Basic.«term_⟶_»
             (Term.proj `A "." `A)
             " ⟶ "
             (Term.app (Term.proj `G "." `obj) [`B]))]
           "//"
           («term_=_»
            (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
             (Term.app
              (Term.proj `G "." `map)
              [(Term.app
                (Term.proj
                 (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
                 "."
                 `map)
                [`g])])
             " ≫ "
             (Term.app
              (Term.proj `G "." `map)
              [(Term.app
                (Term.proj
                 (Term.proj
                  (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                   "adj")
                  "."
                  `counit)
                 "."
                 `app)
                [`B])]))
            "="
            (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» (Term.proj `A "." `a) " ≫ " `g))
           "}"))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.refine'
              "refine'"
              (Term.app
               (Term.proj
                (Term.app
                 (Term.proj
                  (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                   "adj")
                  "."
                  `homEquiv)
                 [(Term.hole "_") (Term.hole "_")])
                "."
                `subtypeEquiv)
               [(Term.hole "_")]))
             []
             (Tactic.intro "intro" [`f])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 (Term.proj
                  (Term.proj
                   (Term.app
                    (Term.proj
                     (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                      "adj")
                     "."
                     `homEquiv)
                    [(Term.hole "_") (Term.hole "_")])
                   "."
                   `Injective)
                  "."
                  `eq_iff))
                ","
                (Tactic.rwRule [] `adjunction.hom_equiv_naturality_left)
                ","
                (Tactic.rwRule
                 []
                 (Term.proj
                  (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                   "adj")
                  "."
                  `hom_equiv_unit))
                ","
                (Tactic.rwRule
                 []
                 (Term.proj
                  (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                   "adj")
                  "."
                  `hom_equiv_unit))
                ","
                (Tactic.rwRule [] `G.map_comp)]
               "]")
              [])
             []
             (Tactic.dsimp "dsimp" [] [] [] [] [])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 []
                 (Term.proj
                  (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                   "adj")
                  "."
                  `right_triangle_components_assoc))
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `G.map_comp)
                ","
                (Tactic.rwRule
                 []
                 (Term.proj
                  (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF
                   "F")
                  "."
                  `map_comp))
                ","
                (Tactic.rwRule [] `category.assoc)
                ","
                (Tactic.rwRule
                 []
                 (Term.proj
                  (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                   "adj")
                  "."
                  `counit_naturality))
                ","
                (Tactic.rwRule
                 []
                 (Term.proj
                  (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                   "adj")
                  "."
                  `left_triangle_components_assoc))]
               "]")
              [])
             []
             (Tactic.apply "apply" `eq_comm)]))))
        (calcStep
         (Logic.Equiv.Defs.«term_≃_»
          (Term.hole "_")
          " ≃ "
          (Combinatorics.Quiver.Basic.«term_⟶_»
           `A
           " ⟶ "
           (Term.app
            (Term.proj
             (Term.app
              `comparison
              [(CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                "adj")])
             "."
             `obj)
            [`B])))
         ":="
         (Term.structInst
          "{"
          []
          [(Term.structInstField
            (Term.structInstLVal `toFun [])
            ":="
            (Term.fun
             "fun"
             (Term.basicFun
              [`g]
              []
              "=>"
              (Term.structInst
               "{"
               []
               [(Term.structInstField (Term.structInstLVal `f []) ":=" (Term.hole "_"))
                []
                (Term.structInstField (Term.structInstLVal `h' []) ":=" (Term.proj `g "." `Prop))]
               (Term.optEllipsis [])
               []
               "}"))))
           []
           (Term.structInstField
            (Term.structInstLVal `invFun [])
            ":="
            (Term.fun
             "fun"
             (Term.basicFun
              [`f]
              []
              "=>"
              (Term.anonymousCtor "⟨" [(Term.proj `f "." `f) "," (Term.proj `f "." `h)] "⟩"))))
           []
           (Term.structInstField
            (Term.structInstLVal `left_inv [])
            ":="
            (Term.fun
             "fun"
             (Term.basicFun
              [`g]
              []
              "=>"
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] []) ";" (Tactic.tacticRfl "rfl")]))))))
           []
           (Term.structInstField
            (Term.structInstLVal `right_inv [])
            ":="
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
                 [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] []) ";" (Tactic.tacticRfl "rfl")]))))))]
          (Term.optEllipsis [])
          []
          "}"))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       []
       [(Term.structInstField
         (Term.structInstLVal `toFun [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`g]
           []
           "=>"
           (Term.structInst
            "{"
            []
            [(Term.structInstField (Term.structInstLVal `f []) ":=" (Term.hole "_"))
             []
             (Term.structInstField (Term.structInstLVal `h' []) ":=" (Term.proj `g "." `Prop))]
            (Term.optEllipsis [])
            []
            "}"))))
        []
        (Term.structInstField
         (Term.structInstLVal `invFun [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`f]
           []
           "=>"
           (Term.anonymousCtor "⟨" [(Term.proj `f "." `f) "," (Term.proj `f "." `h)] "⟩"))))
        []
        (Term.structInstField
         (Term.structInstLVal `left_inv [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`g]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] []) ";" (Tactic.tacticRfl "rfl")]))))))
        []
        (Term.structInstField
         (Term.structInstLVal `right_inv [])
         ":="
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
              [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] []) ";" (Tactic.tacticRfl "rfl")]))))))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
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
           [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] []) ";" (Tactic.tacticRfl "rfl")])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] []) ";" (Tactic.tacticRfl "rfl")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`g]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] []) ";" (Tactic.tacticRfl "rfl")])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] []) ";" (Tactic.tacticRfl "rfl")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`f]
        []
        "=>"
        (Term.anonymousCtor "⟨" [(Term.proj `f "." `f) "," (Term.proj `f "." `h)] "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.proj `f "." `f) "," (Term.proj `f "." `h)] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `f "." `h)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `f "." `f)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`g]
        []
        "=>"
        (Term.structInst
         "{"
         []
         [(Term.structInstField (Term.structInstLVal `f []) ":=" (Term.hole "_"))
          []
          (Term.structInstField (Term.structInstLVal `h' []) ":=" (Term.proj `g "." `Prop))]
         (Term.optEllipsis [])
         []
         "}")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       []
       [(Term.structInstField (Term.structInstLVal `f []) ":=" (Term.hole "_"))
        []
        (Term.structInstField (Term.structInstLVal `h' []) ":=" (Term.proj `g "." `Prop))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `g "." `Prop)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Logic.Equiv.Defs.«term_≃_»
       (Term.hole "_")
       " ≃ "
       (Combinatorics.Quiver.Basic.«term_⟶_»
        `A
        " ⟶ "
        (Term.app
         (Term.proj
          (Term.app
           `comparison
           [(CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
             "adj")])
          "."
          `obj)
         [`B])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Combinatorics.Quiver.Basic.«term_⟶_»
       `A
       " ⟶ "
       (Term.app
        (Term.proj
         (Term.app
          `comparison
          [(CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")])
         "."
         `obj)
        [`B]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app
         `comparison
         [(CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")])
        "."
        `obj)
       [`B])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `B
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        `comparison
        [(CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")])
       "."
       `obj)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `comparison
       [(CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj', expected 'CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj._@.CategoryTheory.Monad.Monadicity._hyg.534'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      We have a bijection of homsets which will be used to construct the left adjoint to the comparison
      functor.
      -/
    @[ simps ]
  def
    comparisonLeftAdjointHomEquiv
    ( A : adj . toMonad . Algebra )
        ( B : D )
        [ HasCoequalizer F . map A . a adj . counit . app F . obj A . A ]
      : comparison_left_adjoint_obj A ⟶ B ≃ A ⟶ comparison adj . obj B
    :=
      calc
        comparison_left_adjoint_obj A ⟶ B ≃ { f : F . obj A . A ⟶ B // _ }
          :=
          Cofork.IsColimit.homIso colimit.isColimit _ B
        _
              ≃
              {
                g
                : A . A ⟶ G . obj B
                //
                G . map F . map g ≫ G . map adj . counit . app B = A . a ≫ g
                }
            :=
            by
              refine' adj . homEquiv _ _ . subtypeEquiv _
                intro f
                rw
                  [
                    ← adj . homEquiv _ _ . Injective . eq_iff
                      ,
                      adjunction.hom_equiv_naturality_left
                      ,
                      adj . hom_equiv_unit
                      ,
                      adj . hom_equiv_unit
                      ,
                      G.map_comp
                    ]
                dsimp
                rw
                  [
                    adj . right_triangle_components_assoc
                      ,
                      ← G.map_comp
                      ,
                      F . map_comp
                      ,
                      category.assoc
                      ,
                      adj . counit_naturality
                      ,
                      adj . left_triangle_components_assoc
                    ]
                apply eq_comm
          _ ≃ A ⟶ comparison adj . obj B
            :=
            {
              toFun := fun g => { f := _ h' := g . Prop }
                invFun := fun f => ⟨ f . f , f . h ⟩
                left_inv := fun g => by ext ; rfl
                right_inv := fun f => by ext ; rfl
              }
#align
  category_theory.monad.monadicity_internal.comparison_left_adjoint_hom_equiv CategoryTheory.Monad.MonadicityInternal.comparisonLeftAdjointHomEquiv

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "Construct the adjunction to the comparison functor.\n-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `leftAdjointComparison [])
      (Command.optDeclSig
       [(Term.instBinder
         "["
         []
         (Term.forall
          "∀"
          [`A]
          [(Term.typeSpec
            ":"
            (Term.proj
             (Term.proj
              (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
               "adj")
              "."
              `toMonad)
             "."
             `Algebra))]
          ","
          (Term.app
           `HasCoequalizer
           [(Term.app
             (Term.proj
              (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
              "."
              `map)
             [(Term.proj `A "." `a)])
            (Term.app
             (Term.proj
              (Term.proj
               (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                "adj")
               "."
               `counit)
              "."
              `app)
             [(Term.app
               (Term.proj
                (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
                "."
                `obj)
               [(Term.proj `A "." `A)])])]))
         "]")]
       [(Term.typeSpec
         ":"
         (CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
          (Term.proj
           (Term.proj
            (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
            "."
            `toMonad)
           "."
           `Algebra)
          " ⥤ "
          `D))])
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.app
             (Term.explicit "@" `adjunction.left_adjoint_of_equiv)
             [(Term.hole "_")
              (Term.hole "_")
              (Term.hole "_")
              (Term.hole "_")
              (Term.app
               `comparison
               [(CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                 "adj")])
              (Term.fun
               "fun"
               (Term.basicFun [`A] [] "=>" (Term.app `comparison_left_adjoint_obj [`A])))
              (Term.fun "fun" (Term.basicFun [`A `B] [] "=>" (Term.hole "_")))
              (Term.hole "_")]))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.apply "apply" `comparison_left_adjoint_hom_equiv)])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.intro "intro" [`A `B `B' `g `h])
             []
             (Std.Tactic.Ext.tacticExt1___ "ext1" [])
             []
             (Tactic.dsimp
              "dsimp"
              []
              []
              []
              ["[" [(Tactic.simpLemma [] [] `comparison_left_adjoint_hom_equiv)] "]"]
              [])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 (Term.proj
                  (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                   "adj")
                  "."
                  `hom_equiv_naturality_right))
                ","
                (Tactic.rwRule [] `category.assoc)]
               "]")
              [])])])))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.refine'
           "refine'"
           (Term.app
            (Term.explicit "@" `adjunction.left_adjoint_of_equiv)
            [(Term.hole "_")
             (Term.hole "_")
             (Term.hole "_")
             (Term.hole "_")
             (Term.app
              `comparison
              [(CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                "adj")])
             (Term.fun
              "fun"
              (Term.basicFun [`A] [] "=>" (Term.app `comparison_left_adjoint_obj [`A])))
             (Term.fun "fun" (Term.basicFun [`A `B] [] "=>" (Term.hole "_")))
             (Term.hole "_")]))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.apply "apply" `comparison_left_adjoint_hom_equiv)])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro "intro" [`A `B `B' `g `h])
            []
            (Std.Tactic.Ext.tacticExt1___ "ext1" [])
            []
            (Tactic.dsimp
             "dsimp"
             []
             []
             []
             ["[" [(Tactic.simpLemma [] [] `comparison_left_adjoint_hom_equiv)] "]"]
             [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.proj
                 (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                  "adj")
                 "."
                 `hom_equiv_naturality_right))
               ","
               (Tactic.rwRule [] `category.assoc)]
              "]")
             [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.intro "intro" [`A `B `B' `g `h])
        []
        (Std.Tactic.Ext.tacticExt1___ "ext1" [])
        []
        (Tactic.dsimp
         "dsimp"
         []
         []
         []
         ["[" [(Tactic.simpLemma [] [] `comparison_left_adjoint_hom_equiv)] "]"]
         [])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            [(patternIgnore (token.«← » "←"))]
            (Term.proj
             (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
             "."
             `hom_equiv_naturality_right))
           ","
           (Tactic.rwRule [] `category.assoc)]
          "]")
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.proj
           (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
           "."
           `hom_equiv_naturality_right))
         ","
         (Tactic.rwRule [] `category.assoc)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `category.assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
       "."
       `hom_equiv_naturality_right)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj', expected 'CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj._@.CategoryTheory.Monad.Monadicity._hyg.534'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    Construct the adjunction to the comparison functor.
    -/
  def
    leftAdjointComparison
    [
        ∀
          A
          : adj . toMonad . Algebra
          ,
          HasCoequalizer F . map A . a adj . counit . app F . obj A . A
        ]
      : adj . toMonad . Algebra ⥤ D
    :=
      by
        refine'
            @ adjunction.left_adjoint_of_equiv
              _ _ _ _ comparison adj fun A => comparison_left_adjoint_obj A fun A B => _ _
          · apply comparison_left_adjoint_hom_equiv
          ·
            intro A B B' g h
              ext1
              dsimp [ comparison_left_adjoint_hom_equiv ]
              rw [ ← adj . hom_equiv_naturality_right , category.assoc ]
#align
  category_theory.monad.monadicity_internal.left_adjoint_comparison CategoryTheory.Monad.MonadicityInternal.leftAdjointComparison

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Provided we have the appropriate coequalizers, we have an adjunction to the comparison functor.\n-/")]
      [(Term.attributes
        "@["
        [(Term.attrInstance
          (Term.attrKind [])
          (Attr.simps "simps" [] (Attr.simpsArgsRest [] [(group `counit)])))]
        "]")]
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `comparisonAdjunction [])
      (Command.optDeclSig
       [(Term.instBinder
         "["
         []
         (Term.forall
          "∀"
          [`A]
          [(Term.typeSpec
            ":"
            (Term.proj
             (Term.proj
              (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
               "adj")
              "."
              `toMonad)
             "."
             `Algebra))]
          ","
          (Term.app
           `HasCoequalizer
           [(Term.app
             (Term.proj
              (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
              "."
              `map)
             [(Term.proj `A "." `a)])
            (Term.app
             (Term.proj
              (Term.proj
               (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                "adj")
               "."
               `counit)
              "."
              `app)
             [(Term.app
               (Term.proj
                (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
                "."
                `obj)
               [(Term.proj `A "." `A)])])]))
         "]")]
       [(Term.typeSpec
         ":"
         (CategoryTheory.CategoryTheory.Adjunction.Basic.«term_⊣_»
          `left_adjoint_comparison
          " ⊣ "
          (Term.app
           `comparison
           [(CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
             "adj")])))])
      (Command.declValSimple
       ":="
       (Term.app `Adjunction.adjunctionOfEquivLeft [(Term.hole "_") (Term.hole "_")])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Adjunction.adjunctionOfEquivLeft [(Term.hole "_") (Term.hole "_")])
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
      `Adjunction.adjunctionOfEquivLeft
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (CategoryTheory.CategoryTheory.Adjunction.Basic.«term_⊣_»
       `left_adjoint_comparison
       " ⊣ "
       (Term.app
        `comparison
        [(CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `comparison
       [(CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj', expected 'CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj._@.CategoryTheory.Monad.Monadicity._hyg.534'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      Provided we have the appropriate coequalizers, we have an adjunction to the comparison functor.
      -/
    @[ simps counit ]
  def
    comparisonAdjunction
    [
        ∀
          A
          : adj . toMonad . Algebra
          ,
          HasCoequalizer F . map A . a adj . counit . app F . obj A . A
        ]
      : left_adjoint_comparison ⊣ comparison adj
    := Adjunction.adjunctionOfEquivLeft _ _
#align
  category_theory.monad.monadicity_internal.comparison_adjunction CategoryTheory.Monad.MonadicityInternal.comparisonAdjunction

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `comparison_adjunction_unit_f_aux [])
      (Command.declSig
       [(Term.instBinder
         "["
         []
         (Term.forall
          "∀"
          [`A]
          [(Term.typeSpec
            ":"
            (Term.proj
             (Term.proj
              (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
               "adj")
              "."
              `toMonad)
             "."
             `Algebra))]
          ","
          (Term.app
           `HasCoequalizer
           [(Term.app
             (Term.proj
              (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
              "."
              `map)
             [(Term.proj `A "." `a)])
            (Term.app
             (Term.proj
              (Term.proj
               (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                "adj")
               "."
               `counit)
              "."
              `app)
             [(Term.app
               (Term.proj
                (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
                "."
                `obj)
               [(Term.proj `A "." `A)])])]))
         "]")
        (Term.explicitBinder
         "("
         [`A]
         [":"
          (Term.proj
           (Term.proj
            (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
            "."
            `toMonad)
           "."
           `Algebra)]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.proj
          (Term.app (Term.proj (Term.proj `comparison_adjunction "." `Unit) "." `app) [`A])
          "."
          `f)
         "="
         (Term.app
          (Term.proj
           (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
           "."
           `homEquiv)
          [(Term.proj `A "." `A)
           (Term.hole "_")
           (Term.app
            `coequalizer.π
            [(Term.app
              (Term.proj
               (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
               "."
               `map)
              [(Term.proj `A "." `a)])
             (Term.app
              (Term.proj
               (Term.proj
                (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                 "adj")
                "."
                `counit)
               "."
               `app)
              [(Term.app
                (Term.proj
                 (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
                 "."
                 `obj)
                [(Term.proj `A "." `A)])])])]))))
      (Command.declValSimple
       ":="
       (Term.app
        `congr_arg
        [(Term.app
          (Term.proj
           (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
           "."
           `homEquiv)
          [(Term.hole "_") (Term.hole "_")])
         (Term.app `Category.comp_id [(Term.hole "_")])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `congr_arg
       [(Term.app
         (Term.proj
          (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
          "."
          `homEquiv)
         [(Term.hole "_") (Term.hole "_")])
        (Term.app `Category.comp_id [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Category.comp_id [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Category.comp_id
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Category.comp_id [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj
        (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
        "."
        `homEquiv)
       [(Term.hole "_") (Term.hole "_")])
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
      (Term.proj
       (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
       "."
       `homEquiv)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj', expected 'CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj._@.CategoryTheory.Monad.Monadicity._hyg.534'
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
  comparison_adjunction_unit_f_aux
  [ ∀ A : adj . toMonad . Algebra , HasCoequalizer F . map A . a adj . counit . app F . obj A . A ]
      ( A : adj . toMonad . Algebra )
    :
      comparison_adjunction . Unit . app A . f
        =
        adj . homEquiv A . A _ coequalizer.π F . map A . a adj . counit . app F . obj A . A
  := congr_arg adj . homEquiv _ _ Category.comp_id _
#align
  category_theory.monad.monadicity_internal.comparison_adjunction_unit_f_aux CategoryTheory.Monad.MonadicityInternal.comparison_adjunction_unit_f_aux

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "This is a cofork which is helpful for establishing monadicity: the morphism from the Beck\ncoequalizer to this cofork is the unit for the adjunction on the comparison functor.\n-/")]
      [(Term.attributes
        "@["
        [(Term.attrInstance
          (Term.attrKind [])
          (Attr.simps "simps" [] (Attr.simpsArgsRest [] [(group `x)])))]
        "]")]
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `unitCofork [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`A]
         [":"
          (Term.proj
           (Term.proj
            (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
            "."
            `toMonad)
           "."
           `Algebra)]
         []
         ")")
        (Term.instBinder
         "["
         []
         (Term.app
          `HasCoequalizer
          [(Term.app
            (Term.proj
             (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
             "."
             `map)
            [(Term.proj `A "." `a)])
           (Term.app
            (Term.proj
             (Term.proj
              (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
               "adj")
              "."
              `counit)
             "."
             `app)
            [(Term.app
              (Term.proj
               (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
               "."
               `obj)
              [(Term.proj `A "." `A)])])])
         "]")]
       [(Term.typeSpec
         ":"
         (Term.app
          `Cofork
          [(Term.app
            (Term.proj `G "." `map)
            [(Term.app
              (Term.proj
               (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
               "."
               `map)
              [(Term.proj `A "." `a)])])
           (Term.app
            (Term.proj `G "." `map)
            [(Term.app
              (Term.proj
               (Term.proj
                (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                 "adj")
                "."
                `counit)
               "."
               `app)
              [(Term.app
                (Term.proj
                 (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
                 "."
                 `obj)
                [(Term.proj `A "." `A)])])])]))])
      (Command.declValSimple
       ":="
       (Term.app
        `Cofork.ofπ
        [(Term.app
          (Term.proj `G "." `map)
          [(Term.app
            `coequalizer.π
            [(Term.app
              (Term.proj
               (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
               "."
               `map)
              [(Term.proj `A "." `a)])
             (Term.app
              (Term.proj
               (Term.proj
                (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                 "adj")
                "."
                `counit)
               "."
               `app)
              [(Term.app
                (Term.proj
                 (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
                 "."
                 `obj)
                [(Term.proj `A "." `A)])])])])
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.change
              "change"
              («term_=_»
               (Term.hole "_")
               "="
               (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                (Term.app `G.map [(Term.hole "_")])
                " ≫ "
                (Term.hole "_")))
              [])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `G.map_comp)
                ","
                (Tactic.rwRule [] `coequalizer.condition)
                ","
                (Tactic.rwRule [] `G.map_comp)]
               "]")
              [])])))])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Cofork.ofπ
       [(Term.app
         (Term.proj `G "." `map)
         [(Term.app
           `coequalizer.π
           [(Term.app
             (Term.proj
              (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
              "."
              `map)
             [(Term.proj `A "." `a)])
            (Term.app
             (Term.proj
              (Term.proj
               (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                "adj")
               "."
               `counit)
              "."
              `app)
             [(Term.app
               (Term.proj
                (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
                "."
                `obj)
               [(Term.proj `A "." `A)])])])])
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.change
             "change"
             («term_=_»
              (Term.hole "_")
              "="
              (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
               (Term.app `G.map [(Term.hole "_")])
               " ≫ "
               (Term.hole "_")))
             [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `G.map_comp)
               ","
               (Tactic.rwRule [] `coequalizer.condition)
               ","
               (Tactic.rwRule [] `G.map_comp)]
              "]")
             [])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.change
           "change"
           («term_=_»
            (Term.hole "_")
            "="
            (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
             (Term.app `G.map [(Term.hole "_")])
             " ≫ "
             (Term.hole "_")))
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `G.map_comp)
             ","
             (Tactic.rwRule [] `coequalizer.condition)
             ","
             (Tactic.rwRule [] `G.map_comp)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `G.map_comp)
         ","
         (Tactic.rwRule [] `coequalizer.condition)
         ","
         (Tactic.rwRule [] `G.map_comp)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `G.map_comp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coequalizer.condition
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `G.map_comp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       («term_=_»
        (Term.hole "_")
        "="
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         (Term.app `G.map [(Term.hole "_")])
         " ≫ "
         (Term.hole "_")))
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app `G.map [(Term.hole "_")])
        " ≫ "
        (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `G.map [(Term.hole "_")])
       " ≫ "
       (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `G.map [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `G.map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(Tactic.change
          "change"
          («term_=_»
           (Term.hole "_")
           "="
           (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
            (Term.app `G.map [(Term.hole "_")])
            " ≫ "
            (Term.hole "_")))
          [])
         []
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `G.map_comp)
            ","
            (Tactic.rwRule [] `coequalizer.condition)
            ","
            (Tactic.rwRule [] `G.map_comp)]
           "]")
          [])])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj `G "." `map)
       [(Term.app
         `coequalizer.π
         [(Term.app
           (Term.proj
            (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
            "."
            `map)
           [(Term.proj `A "." `a)])
          (Term.app
           (Term.proj
            (Term.proj
             (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
             "."
             `counit)
            "."
            `app)
           [(Term.app
             (Term.proj
              (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
              "."
              `obj)
             [(Term.proj `A "." `A)])])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `coequalizer.π
       [(Term.app
         (Term.proj
          (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
          "."
          `map)
         [(Term.proj `A "." `a)])
        (Term.app
         (Term.proj
          (Term.proj
           (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
           "."
           `counit)
          "."
          `app)
         [(Term.app
           (Term.proj
            (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
            "."
            `obj)
           [(Term.proj `A "." `A)])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.proj
         (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
         "."
         `counit)
        "."
        `app)
       [(Term.app
         (Term.proj
          (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
          "."
          `obj)
         [(Term.proj `A "." `A)])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
        "."
        `obj)
       [(Term.proj `A "." `A)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `A "." `A)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `A
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
       "."
       `obj)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF', expected 'CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF._@.CategoryTheory.Monad.Monadicity._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      This is a cofork which is helpful for establishing monadicity: the morphism from the Beck
      coequalizer to this cofork is the unit for the adjunction on the comparison functor.
      -/
    @[ simps x ]
  def
    unitCofork
    ( A : adj . toMonad . Algebra )
        [ HasCoequalizer F . map A . a adj . counit . app F . obj A . A ]
      : Cofork G . map F . map A . a G . map adj . counit . app F . obj A . A
    :=
      Cofork.ofπ
        G . map coequalizer.π F . map A . a adj . counit . app F . obj A . A
          by change _ = G.map _ ≫ _ rw [ ← G.map_comp , coequalizer.condition , G.map_comp ]
#align
  category_theory.monad.monadicity_internal.unit_cofork CategoryTheory.Monad.MonadicityInternal.unitCofork

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
      (Command.declId `unit_cofork_π [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`A]
         [":"
          (Term.proj
           (Term.proj
            (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
            "."
            `toMonad)
           "."
           `Algebra)]
         []
         ")")
        (Term.instBinder
         "["
         []
         (Term.app
          `HasCoequalizer
          [(Term.app
            (Term.proj
             (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
             "."
             `map)
            [(Term.proj `A "." `a)])
           (Term.app
            (Term.proj
             (Term.proj
              (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
               "adj")
              "."
              `counit)
             "."
             `app)
            [(Term.app
              (Term.proj
               (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
               "."
               `obj)
              [(Term.proj `A "." `A)])])])
         "]")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.proj (Term.app `unit_cofork [`A]) "." `π)
         "="
         (Term.app
          (Term.proj `G "." `map)
          [(Term.app
            `coequalizer.π
            [(Term.app
              (Term.proj
               (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
               "."
               `map)
              [(Term.proj `A "." `a)])
             (Term.app
              (Term.proj
               (Term.proj
                (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                 "adj")
                "."
                `counit)
               "."
               `app)
              [(Term.app
                (Term.proj
                 (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
                 "."
                 `obj)
                [(Term.proj `A "." `A)])])])]))))
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
       (Term.proj (Term.app `unit_cofork [`A]) "." `π)
       "="
       (Term.app
        (Term.proj `G "." `map)
        [(Term.app
          `coequalizer.π
          [(Term.app
            (Term.proj
             (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
             "."
             `map)
            [(Term.proj `A "." `a)])
           (Term.app
            (Term.proj
             (Term.proj
              (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
               "adj")
              "."
              `counit)
             "."
             `app)
            [(Term.app
              (Term.proj
               (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
               "."
               `obj)
              [(Term.proj `A "." `A)])])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `G "." `map)
       [(Term.app
         `coequalizer.π
         [(Term.app
           (Term.proj
            (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
            "."
            `map)
           [(Term.proj `A "." `a)])
          (Term.app
           (Term.proj
            (Term.proj
             (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
             "."
             `counit)
            "."
            `app)
           [(Term.app
             (Term.proj
              (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
              "."
              `obj)
             [(Term.proj `A "." `A)])])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `coequalizer.π
       [(Term.app
         (Term.proj
          (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
          "."
          `map)
         [(Term.proj `A "." `a)])
        (Term.app
         (Term.proj
          (Term.proj
           (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
           "."
           `counit)
          "."
          `app)
         [(Term.app
           (Term.proj
            (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
            "."
            `obj)
           [(Term.proj `A "." `A)])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.proj
         (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
         "."
         `counit)
        "."
        `app)
       [(Term.app
         (Term.proj
          (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
          "."
          `obj)
         [(Term.proj `A "." `A)])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
        "."
        `obj)
       [(Term.proj `A "." `A)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `A "." `A)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `A
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
       "."
       `obj)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF', expected 'CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF._@.CategoryTheory.Monad.Monadicity._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    unit_cofork_π
    ( A : adj . toMonad . Algebra )
        [ HasCoequalizer F . map A . a adj . counit . app F . obj A . A ]
      : unit_cofork A . π = G . map coequalizer.π F . map A . a adj . counit . app F . obj A . A
    := rfl
#align
  category_theory.monad.monadicity_internal.unit_cofork_π CategoryTheory.Monad.MonadicityInternal.unit_cofork_π

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `comparison_adjunction_unit_f [])
      (Command.declSig
       [(Term.instBinder
         "["
         []
         (Term.forall
          "∀"
          [`A]
          [(Term.typeSpec
            ":"
            (Term.proj
             (Term.proj
              (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
               "adj")
              "."
              `toMonad)
             "."
             `Algebra))]
          ","
          (Term.app
           `HasCoequalizer
           [(Term.app
             (Term.proj
              (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
              "."
              `map)
             [(Term.proj `A "." `a)])
            (Term.app
             (Term.proj
              (Term.proj
               (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                "adj")
               "."
               `counit)
              "."
              `app)
             [(Term.app
               (Term.proj
                (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
                "."
                `obj)
               [(Term.proj `A "." `A)])])]))
         "]")
        (Term.explicitBinder
         "("
         [`A]
         [":"
          (Term.proj
           (Term.proj
            (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
            "."
            `toMonad)
           "."
           `Algebra)]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.proj
          (Term.app (Term.proj (Term.proj `comparison_adjunction "." `Unit) "." `app) [`A])
          "."
          `f)
         "="
         (Term.app
          (Term.proj (Term.app `beckCoequalizer [`A]) "." `desc)
          [(Term.app `unit_cofork [`A])]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.apply
            "apply"
            (Term.app `limits.cofork.is_colimit.hom_ext [(Term.app `beck_coequalizer [`A])]))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `cofork.is_colimit.π_desc)] "]")
            [])
           []
           (Tactic.dsimp
            "dsimp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `beck_cofork_π) "," (Tactic.simpLemma [] [] `unit_cofork_π)]
             "]"]
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `comparison_adjunction_unit_f_aux)
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app
                (Term.proj
                 (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                  "adj")
                 "."
                 `hom_equiv_naturality_left)
                [`A.a]))
              ","
              (Tactic.rwRule [] `coequalizer.condition)
              ","
              (Tactic.rwRule
               []
               (Term.proj
                (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                 "adj")
                "."
                `hom_equiv_naturality_right))
              ","
              (Tactic.rwRule
               []
               (Term.proj
                (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                 "adj")
                "."
                `hom_equiv_unit))
              ","
              (Tactic.rwRule [] `category.assoc)]
             "]")
            [])
           []
           (Tactic.apply
            "apply"
            (Term.proj
             (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
             "."
             `right_triangle_components_assoc))])))
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
         [(Tactic.apply
           "apply"
           (Term.app `limits.cofork.is_colimit.hom_ext [(Term.app `beck_coequalizer [`A])]))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `cofork.is_colimit.π_desc)] "]")
           [])
          []
          (Tactic.dsimp
           "dsimp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `beck_cofork_π) "," (Tactic.simpLemma [] [] `unit_cofork_π)]
            "]"]
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `comparison_adjunction_unit_f_aux)
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app
               (Term.proj
                (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                 "adj")
                "."
                `hom_equiv_naturality_left)
               [`A.a]))
             ","
             (Tactic.rwRule [] `coequalizer.condition)
             ","
             (Tactic.rwRule
              []
              (Term.proj
               (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                "adj")
               "."
               `hom_equiv_naturality_right))
             ","
             (Tactic.rwRule
              []
              (Term.proj
               (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                "adj")
               "."
               `hom_equiv_unit))
             ","
             (Tactic.rwRule [] `category.assoc)]
            "]")
           [])
          []
          (Tactic.apply
           "apply"
           (Term.proj
            (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
            "."
            `right_triangle_components_assoc))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply
       "apply"
       (Term.proj
        (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
        "."
        `right_triangle_components_assoc))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
       "."
       `right_triangle_components_assoc)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj', expected 'CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj._@.CategoryTheory.Monad.Monadicity._hyg.534'
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
  comparison_adjunction_unit_f
  [ ∀ A : adj . toMonad . Algebra , HasCoequalizer F . map A . a adj . counit . app F . obj A . A ]
      ( A : adj . toMonad . Algebra )
    : comparison_adjunction . Unit . app A . f = beckCoequalizer A . desc unit_cofork A
  :=
    by
      apply limits.cofork.is_colimit.hom_ext beck_coequalizer A
        rw [ cofork.is_colimit.π_desc ]
        dsimp only [ beck_cofork_π , unit_cofork_π ]
        rw
          [
            comparison_adjunction_unit_f_aux
              ,
              ← adj . hom_equiv_naturality_left A.a
              ,
              coequalizer.condition
              ,
              adj . hom_equiv_naturality_right
              ,
              adj . hom_equiv_unit
              ,
              category.assoc
            ]
        apply adj . right_triangle_components_assoc
#align
  category_theory.monad.monadicity_internal.comparison_adjunction_unit_f CategoryTheory.Monad.MonadicityInternal.comparison_adjunction_unit_f

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The cofork which describes the counit of the adjunction: the morphism from the coequalizer of\nthis pair to this morphism is the counit.\n-/")]
      [(Term.attributes
        "@["
        [(Term.attrInstance (Term.attrKind []) (Attr.simps "simps" [] (Attr.simpsArgsRest [] [])))]
        "]")]
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `counitCofork [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`B] [":" `D] [] ")")]
       [(Term.typeSpec
         ":"
         (Term.app
          `Cofork
          [(Term.app
            (Term.proj
             (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
             "."
             `map)
            [(Term.app
              (Term.proj `G "." `map)
              [(Term.app
                (Term.proj
                 (Term.proj
                  (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                   "adj")
                  "."
                  `counit)
                 "."
                 `app)
                [`B])])])
           (Term.app
            (Term.proj
             (Term.proj
              (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
               "adj")
              "."
              `counit)
             "."
             `app)
            [(Term.app
              (Term.proj
               (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
               "."
               `obj)
              [(Term.app (Term.proj `G "." `obj) [`B])])])]))])
      (Command.declValSimple
       ":="
       (Term.app
        `Cofork.ofπ
        [(Term.app
          (Term.proj
           (Term.proj
            (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
            "."
            `counit)
           "."
           `app)
          [`B])
         (Term.app
          (Term.proj
           (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
           "."
           `counit_naturality)
          [(Term.hole "_")])])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Cofork.ofπ
       [(Term.app
         (Term.proj
          (Term.proj
           (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
           "."
           `counit)
          "."
          `app)
         [`B])
        (Term.app
         (Term.proj
          (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
          "."
          `counit_naturality)
         [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
        "."
        `counit_naturality)
       [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
       "."
       `counit_naturality)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj', expected 'CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj._@.CategoryTheory.Monad.Monadicity._hyg.534'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      The cofork which describes the counit of the adjunction: the morphism from the coequalizer of
      this pair to this morphism is the counit.
      -/
    @[ simps ]
  def
    counitCofork
    ( B : D ) : Cofork F . map G . map adj . counit . app B adj . counit . app F . obj G . obj B
    := Cofork.ofπ adj . counit . app B adj . counit_naturality _
#align
  category_theory.monad.monadicity_internal.counit_cofork CategoryTheory.Monad.MonadicityInternal.counitCofork

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "The unit cofork is a colimit provided `G` preserves it.  -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `unitColimitOfPreservesCoequalizer [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`A]
         [":"
          (Term.proj
           (Term.proj
            (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
            "."
            `toMonad)
           "."
           `Algebra)]
         []
         ")")
        (Term.instBinder
         "["
         []
         (Term.app
          `HasCoequalizer
          [(Term.app
            (Term.proj
             (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
             "."
             `map)
            [(Term.proj `A "." `a)])
           (Term.app
            (Term.proj
             (Term.proj
              (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
               "adj")
              "."
              `counit)
             "."
             `app)
            [(Term.app
              (Term.proj
               (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
               "."
               `obj)
              [(Term.proj `A "." `A)])])])
         "]")
        (Term.instBinder
         "["
         []
         (Term.app
          `PreservesColimit
          [(Term.app
            `parallelPair
            [(Term.app
              (Term.proj
               (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
               "."
               `map)
              [(Term.proj `A "." `a)])
             (Term.app
              (Term.proj
               (Term.proj
                (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                 "adj")
                "."
                `counit)
               "."
               `app)
              [(Term.app
                (Term.proj
                 (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
                 "."
                 `obj)
                [(Term.proj `A "." `A)])])])
           `G])
         "]")]
       [(Term.typeSpec ":" (Term.app `IsColimit [(Term.app `unit_cofork [`A])]))])
      (Command.declValSimple
       ":="
       (Term.app `isColimitOfHasCoequalizerOfPreservesColimit [`G (Term.hole "_") (Term.hole "_")])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `isColimitOfHasCoequalizerOfPreservesColimit [`G (Term.hole "_") (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `G
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `isColimitOfHasCoequalizerOfPreservesColimit
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `IsColimit [(Term.app `unit_cofork [`A])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `unit_cofork [`A])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `unit_cofork
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `unit_cofork [`A]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsColimit
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `PreservesColimit
       [(Term.app
         `parallelPair
         [(Term.app
           (Term.proj
            (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
            "."
            `map)
           [(Term.proj `A "." `a)])
          (Term.app
           (Term.proj
            (Term.proj
             (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
             "."
             `counit)
            "."
            `app)
           [(Term.app
             (Term.proj
              (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
              "."
              `obj)
             [(Term.proj `A "." `A)])])])
        `G])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `G
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `parallelPair
       [(Term.app
         (Term.proj
          (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
          "."
          `map)
         [(Term.proj `A "." `a)])
        (Term.app
         (Term.proj
          (Term.proj
           (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
           "."
           `counit)
          "."
          `app)
         [(Term.app
           (Term.proj
            (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
            "."
            `obj)
           [(Term.proj `A "." `A)])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.proj
         (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
         "."
         `counit)
        "."
        `app)
       [(Term.app
         (Term.proj
          (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
          "."
          `obj)
         [(Term.proj `A "." `A)])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
        "."
        `obj)
       [(Term.proj `A "." `A)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `A "." `A)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `A
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
       "."
       `obj)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF', expected 'CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF._@.CategoryTheory.Monad.Monadicity._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The unit cofork is a colimit provided `G` preserves it.  -/
  def
    unitColimitOfPreservesCoequalizer
    ( A : adj . toMonad . Algebra )
        [ HasCoequalizer F . map A . a adj . counit . app F . obj A . A ]
        [ PreservesColimit parallelPair F . map A . a adj . counit . app F . obj A . A G ]
      : IsColimit unit_cofork A
    := isColimitOfHasCoequalizerOfPreservesColimit G _ _
#align
  category_theory.monad.monadicity_internal.unit_colimit_of_preserves_coequalizer CategoryTheory.Monad.MonadicityInternal.unitColimitOfPreservesCoequalizer

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "The counit cofork is a colimit provided `G` reflects it. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `counitCoequalizerOfReflectsCoequalizer [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`B] [":" `D] [] ")")
        (Term.instBinder
         "["
         []
         (Term.app
          `ReflectsColimit
          [(Term.app
            `parallelPair
            [(Term.app
              (Term.proj
               (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
               "."
               `map)
              [(Term.app
                (Term.proj `G "." `map)
                [(Term.app
                  (Term.proj
                   (Term.proj
                    (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                     "adj")
                    "."
                    `counit)
                   "."
                   `app)
                  [`B])])])
             (Term.app
              (Term.proj
               (Term.proj
                (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                 "adj")
                "."
                `counit)
               "."
               `app)
              [(Term.app
                (Term.proj
                 (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
                 "."
                 `obj)
                [(Term.app (Term.proj `G "." `obj) [`B])])])])
           `G])
         "]")]
       [(Term.typeSpec ":" (Term.app `IsColimit [(Term.app `counit_cofork [`B])]))])
      (Command.declValSimple
       ":="
       (Term.app
        `isColimitOfIsColimitCoforkMap
        [`G
         (Term.hole "_")
         (Term.app
          `beckCoequalizer
          [(Term.app
            (Term.proj
             (Term.app
              `comparison
              [(CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                "adj")])
             "."
             `obj)
            [`B])])])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `isColimitOfIsColimitCoforkMap
       [`G
        (Term.hole "_")
        (Term.app
         `beckCoequalizer
         [(Term.app
           (Term.proj
            (Term.app
             `comparison
             [(CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
               "adj")])
            "."
            `obj)
           [`B])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `beckCoequalizer
       [(Term.app
         (Term.proj
          (Term.app
           `comparison
           [(CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
             "adj")])
          "."
          `obj)
         [`B])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app
         `comparison
         [(CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")])
        "."
        `obj)
       [`B])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `B
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        `comparison
        [(CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")])
       "."
       `obj)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `comparison
       [(CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj', expected 'CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj._@.CategoryTheory.Monad.Monadicity._hyg.534'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The counit cofork is a colimit provided `G` reflects it. -/
  def
    counitCoequalizerOfReflectsCoequalizer
    ( B : D )
        [
          ReflectsColimit
            parallelPair F . map G . map adj . counit . app B adj . counit . app F . obj G . obj B G
          ]
      : IsColimit counit_cofork B
    := isColimitOfIsColimitCoforkMap G _ beckCoequalizer comparison adj . obj B
#align
  category_theory.monad.monadicity_internal.counit_coequalizer_of_reflects_coequalizer CategoryTheory.Monad.MonadicityInternal.counitCoequalizerOfReflectsCoequalizer

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `comparison_adjunction_counit_app [])
      (Command.declSig
       [(Term.instBinder
         "["
         []
         (Term.forall
          "∀"
          [`A]
          [(Term.typeSpec
            ":"
            (Term.proj
             (Term.proj
              (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
               "adj")
              "."
              `toMonad)
             "."
             `Algebra))]
          ","
          (Term.app
           `HasCoequalizer
           [(Term.app
             (Term.proj
              (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
              "."
              `map)
             [(Term.proj `A "." `a)])
            (Term.app
             (Term.proj
              (Term.proj
               (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                "adj")
               "."
               `counit)
              "."
              `app)
             [(Term.app
               (Term.proj
                (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termF "F")
                "."
                `obj)
               [(Term.proj `A "." `A)])])]))
         "]")
        (Term.explicitBinder "(" [`B] [":" `D] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (Term.proj (Term.proj `comparison_adjunction "." `counit) "." `app) [`B])
         "="
         (Term.app `colimit.desc [(Term.hole "_") (Term.app `counit_cofork [`B])]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.apply "apply" `coequalizer.hom_ext)
           []
           (Tactic.change
            "change"
            («term_=_»
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
              (Term.app `coequalizer.π [(Term.hole "_") (Term.hole "_")])
              " ≫ "
              (Term.app
               `coequalizer.desc
               [(Term.app
                 (Term.proj
                  (Term.app
                   (Term.proj
                    (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                     "adj")
                    "."
                    `homEquiv)
                   [(Term.hole "_") `B])
                  "."
                  `symm)
                 [(Term.app
                   (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
                   [(Term.hole "_")])])
                (Term.hole "_")]))
             "="
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
              (Term.app `coequalizer.π [(Term.hole "_") (Term.hole "_")])
              " ≫ "
              (Term.app `coequalizer.desc [(Term.hole "_") (Term.hole "_")])))
            [])
           []
           (Tactic.simp "simp" [] [] [] [] [])])))
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
         [(Tactic.apply "apply" `coequalizer.hom_ext)
          []
          (Tactic.change
           "change"
           («term_=_»
            (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
             (Term.app `coequalizer.π [(Term.hole "_") (Term.hole "_")])
             " ≫ "
             (Term.app
              `coequalizer.desc
              [(Term.app
                (Term.proj
                 (Term.app
                  (Term.proj
                   (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                    "adj")
                   "."
                   `homEquiv)
                  [(Term.hole "_") `B])
                 "."
                 `symm)
                [(Term.app
                  (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
                  [(Term.hole "_")])])
               (Term.hole "_")]))
            "="
            (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
             (Term.app `coequalizer.π [(Term.hole "_") (Term.hole "_")])
             " ≫ "
             (Term.app `coequalizer.desc [(Term.hole "_") (Term.hole "_")])))
           [])
          []
          (Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       («term_=_»
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         (Term.app `coequalizer.π [(Term.hole "_") (Term.hole "_")])
         " ≫ "
         (Term.app
          `coequalizer.desc
          [(Term.app
            (Term.proj
             (Term.app
              (Term.proj
               (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
                "adj")
               "."
               `homEquiv)
              [(Term.hole "_") `B])
             "."
             `symm)
            [(Term.app
              (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
              [(Term.hole "_")])])
           (Term.hole "_")]))
        "="
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         (Term.app `coequalizer.π [(Term.hole "_") (Term.hole "_")])
         " ≫ "
         (Term.app `coequalizer.desc [(Term.hole "_") (Term.hole "_")])))
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app `coequalizer.π [(Term.hole "_") (Term.hole "_")])
        " ≫ "
        (Term.app
         `coequalizer.desc
         [(Term.app
           (Term.proj
            (Term.app
             (Term.proj
              (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj
               "adj")
              "."
              `homEquiv)
             [(Term.hole "_") `B])
            "."
            `symm)
           [(Term.app
             (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
             [(Term.hole "_")])])
          (Term.hole "_")]))
       "="
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app `coequalizer.π [(Term.hole "_") (Term.hole "_")])
        " ≫ "
        (Term.app `coequalizer.desc [(Term.hole "_") (Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `coequalizer.π [(Term.hole "_") (Term.hole "_")])
       " ≫ "
       (Term.app `coequalizer.desc [(Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `coequalizer.desc [(Term.hole "_") (Term.hole "_")])
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
      `coequalizer.desc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `coequalizer.π [(Term.hole "_") (Term.hole "_")])
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
      `coequalizer.π
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app `coequalizer.π [(Term.hole "_") (Term.hole "_")])
       " ≫ "
       (Term.app
        `coequalizer.desc
        [(Term.app
          (Term.proj
           (Term.app
            (Term.proj
             (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
             "."
             `homEquiv)
            [(Term.hole "_") `B])
           "."
           `symm)
          [(Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.hole "_")])])
         (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `coequalizer.desc
       [(Term.app
         (Term.proj
          (Term.app
           (Term.proj
            (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
            "."
            `homEquiv)
           [(Term.hole "_") `B])
          "."
          `symm)
         [(Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.hole "_")])])
        (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app
       (Term.proj
        (Term.app
         (Term.proj
          (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
          "."
          `homEquiv)
         [(Term.hole "_") `B])
        "."
        `symm)
       [(Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        (Term.proj
         (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
         "."
         `homEquiv)
        [(Term.hole "_") `B])
       "."
       `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj
        (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
        "."
        `homEquiv)
       [(Term.hole "_") `B])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `B
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
       "."
       `homEquiv)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj "adj")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj', expected 'CategoryTheory.Monad.MonadicityInternal.CategoryTheory.Monad.Monadicity.termadj._@.CategoryTheory.Monad.Monadicity._hyg.534'
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
  comparison_adjunction_counit_app
  [ ∀ A : adj . toMonad . Algebra , HasCoequalizer F . map A . a adj . counit . app F . obj A . A ]
      ( B : D )
    : comparison_adjunction . counit . app B = colimit.desc _ counit_cofork B
  :=
    by
      apply coequalizer.hom_ext
        change
          coequalizer.π _ _ ≫ coequalizer.desc adj . homEquiv _ B . symm 𝟙 _ _
            =
            coequalizer.π _ _ ≫ coequalizer.desc _ _
        simp
#align
  category_theory.monad.monadicity_internal.comparison_adjunction_counit_app CategoryTheory.Monad.MonadicityInternal.comparison_adjunction_counit_app

end

end MonadicityInternal

open CategoryTheory.Adjunction

open MonadicityInternal

variable {C : Type u₁} {D : Type u₂}

variable [Category.{v₁} C] [Category.{v₁} D]

variable (G : D ⥤ C)

/--
If `G` is monadic, it creates colimits of `G`-split pairs. This is the "boring" direction of Beck's
monadicity theorem, the converse is given in `monadic_of_creates_G_split_coequalizers`.
-/
def createsGSplitCoequalizersOfMonadic [MonadicRightAdjoint G] ⦃A B⦄ (f g : A ⟶ B)
    [G.IsSplitPair f g] : CreatesColimit (parallelPair f g) G :=
  by
  apply monadic_creates_colimit_of_preserves_colimit _ _
  infer_instance
  · apply preserves_colimit_of_iso_diagram _ (diagramIsoParallelPair.{v₁} _).symm
    dsimp
    infer_instance
  · apply preserves_colimit_of_iso_diagram _ (diagramIsoParallelPair.{v₁} _).symm
    dsimp
    infer_instance
#align
  category_theory.monad.creates_G_split_coequalizers_of_monadic CategoryTheory.Monad.createsGSplitCoequalizersOfMonadic

variable [IsRightAdjoint G]

section BeckMonadicity

/-- To show `G` is a monadic right adjoint, we can show it preserves and reflects `G`-split
coequalizers, and `C` has them.
-/
def monadicOfHasPreservesReflectsGSplitCoequalizers
    [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsSplitPair f g], HasCoequalizer f g]
    [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsSplitPair f g], PreservesColimit (parallelPair f g) G]
    [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsSplitPair f g], ReflectsColimit (parallelPair f g) G] :
    MonadicRightAdjoint G :=
  by
  let L : (adjunction.of_right_adjoint G).toMonad.Algebra ⥤ D := left_adjoint_comparison
  letI i : is_right_adjoint (comparison (of_right_adjoint G)) := ⟨_, comparison_adjunction⟩
  constructor
  let this :
    ∀ X : (of_right_adjoint G).toMonad.Algebra,
      is_iso ((of_right_adjoint (comparison (of_right_adjoint G))).Unit.app X) :=
    by
    intro X
    apply is_iso_of_reflects_iso _ (monad.forget (of_right_adjoint G).toMonad)
    · change is_iso (comparison_adjunction.unit.app X).f
      rw [comparison_adjunction_unit_f]
      change
        is_iso
          (is_colimit.cocone_point_unique_up_to_iso (beck_coequalizer X)
              (unit_colimit_of_preserves_coequalizer X)).Hom
      refine' is_iso.of_iso (is_colimit.cocone_point_unique_up_to_iso _ _)
  let this : ∀ Y : D, is_iso ((of_right_adjoint (comparison (of_right_adjoint G))).counit.app Y) :=
    by
    intro Y
    change is_iso (comparison_adjunction.counit.app Y)
    rw [comparison_adjunction_counit_app]
    change is_iso (is_colimit.cocone_point_unique_up_to_iso _ _).Hom
    infer_instance
    apply counit_coequalizer_of_reflects_coequalizer _
    letI :
      G.is_split_pair ((left_adjoint G).map (G.map ((adjunction.of_right_adjoint G).counit.app Y)))
        ((adjunction.of_right_adjoint G).counit.app ((left_adjoint G).obj (G.obj Y))) :=
      monadicity_internal.main_pair_G_split ((comparison (adjunction.of_right_adjoint G)).obj Y)
    infer_instance
  exact adjunction.is_right_adjoint_to_is_equivalence
#align
  category_theory.monad.monadic_of_has_preserves_reflects_G_split_coequalizers CategoryTheory.Monad.monadicOfHasPreservesReflectsGSplitCoequalizers

/--
Beck's monadicity theorem. If `G` has a right adjoint and creates coequalizers of `G`-split pairs,
then it is monadic.
This is the converse of `creates_G_split_of_monadic`.
-/
def monadicOfCreatesGSplitCoequalizers
    [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsSplitPair f g], CreatesColimit (parallelPair f g) G] :
    MonadicRightAdjoint G :=
  by
  let this : ∀ ⦃A B⦄ (f g : A ⟶ B) [G.is_split_pair f g], has_colimit (parallel_pair f g ⋙ G) :=
    by
    intro A B f g i
    apply has_colimit_of_iso (diagramIsoParallelPair.{v₁} _)
    change has_coequalizer (G.map f) (G.map g)
    infer_instance
  apply monadic_of_has_preserves_reflects_G_split_coequalizers _
  · infer_instance
  · intro A B f g i
    apply has_colimit_of_created (parallel_pair f g) G
  · intro A B f g i
    infer_instance
  · intro A B f g i
    infer_instance
#align
  category_theory.monad.monadic_of_creates_G_split_coequalizers CategoryTheory.Monad.monadicOfCreatesGSplitCoequalizers

/-- An alternate version of Beck's monadicity theorem. If `G` reflects isomorphisms, preserves
coequalizers of `G`-split pairs and `C` has coequalizers of `G`-split pairs, then it is monadic.
-/
def monadicOfHasPreservesGSplitCoequalizersOfReflectsIsomorphisms [ReflectsIsomorphisms G]
    [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsSplitPair f g], HasCoequalizer f g]
    [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsSplitPair f g], PreservesColimit (parallelPair f g) G] :
    MonadicRightAdjoint G :=
  by
  apply monadic_of_has_preserves_reflects_G_split_coequalizers _
  · infer_instance
  · assumption
  · assumption
  · intro A B f g i
    apply reflects_colimit_of_reflects_isomorphisms
#align
  category_theory.monad.monadic_of_has_preserves_G_split_coequalizers_of_reflects_isomorphisms CategoryTheory.Monad.monadicOfHasPreservesGSplitCoequalizersOfReflectsIsomorphisms

end BeckMonadicity

section ReflexiveMonadicity

variable [HasReflexiveCoequalizers D] [ReflectsIsomorphisms G]

variable [∀ ⦃A B⦄ (f g : A ⟶ B) [IsReflexivePair f g], PreservesColimit (parallelPair f g) G]

/-- Reflexive (crude) monadicity theorem. If `G` has a right adjoint, `D` has and `G` preserves
reflexive coequalizers and `G` reflects isomorphisms, then `G` is monadic.
-/
def monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms : MonadicRightAdjoint G :=
  by
  let L : (adjunction.of_right_adjoint G).toMonad.Algebra ⥤ D := left_adjoint_comparison
  letI i : is_right_adjoint (comparison (adjunction.of_right_adjoint G)) :=
    ⟨_, comparison_adjunction⟩
  constructor
  let this :
    ∀ X : (adjunction.of_right_adjoint G).toMonad.Algebra,
      is_iso
        ((adjunction.of_right_adjoint (comparison (adjunction.of_right_adjoint G))).Unit.app X) :=
    by
    intro X
    apply is_iso_of_reflects_iso _ (monad.forget (adjunction.of_right_adjoint G).toMonad)
    · change is_iso (comparison_adjunction.unit.app X).f
      rw [comparison_adjunction_unit_f]
      change
        is_iso
          (is_colimit.cocone_point_unique_up_to_iso (beck_coequalizer X)
              (unit_colimit_of_preserves_coequalizer X)).Hom
      apply is_iso.of_iso (is_colimit.cocone_point_unique_up_to_iso _ _)
  let this :
    ∀ Y : D,
      is_iso ((of_right_adjoint (comparison (adjunction.of_right_adjoint G))).counit.app Y) :=
    by
    intro Y
    change is_iso (comparison_adjunction.counit.app Y)
    rw [comparison_adjunction_counit_app]
    change is_iso (is_colimit.cocone_point_unique_up_to_iso _ _).Hom
    infer_instance
    apply counit_coequalizer_of_reflects_coequalizer _
    apply reflects_colimit_of_reflects_isomorphisms
  exact adjunction.is_right_adjoint_to_is_equivalence
#align
  category_theory.monad.monadic_of_has_preserves_reflexive_coequalizers_of_reflects_isomorphisms CategoryTheory.Monad.monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms

end ReflexiveMonadicity

end Monad

end CategoryTheory

