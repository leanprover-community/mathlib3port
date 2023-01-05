/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers

! This file was ported from Lean 3 source module geometry.euclidean.angle.oriented.affine
! leanprover-community/mathlib commit 5a3e819569b0f12cbec59d740a2613018e7b8eec
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Convex.Side
import Mathbin.Geometry.Euclidean.Angle.Oriented.Basic
import Mathbin.Geometry.Euclidean.Angle.Unoriented.Affine

/-!
# Oriented angles.

This file defines oriented angles in Euclidean affine spaces.

## Main definitions

* `euclidean_geometry.oangle`, with notation `∡`, is the oriented angle determined by three
  points.

-/


noncomputable section

open FiniteDimensional Complex

open Affine EuclideanGeometry Real RealInnerProductSpace ComplexConjugate

namespace EuclideanGeometry

variable {V : Type _} {P : Type _} [InnerProductSpace ℝ V] [MetricSpace P]

variable [NormedAddTorsor V P] [hd2 : Fact (finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

include hd2

-- mathport name: expro
local notation "o" => Module.Oriented.positiveOrientation

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The oriented angle at `p₂` between the line segments to `p₁` and `p₃`, modulo `2 * π`. If\neither of those points equals `p₂`, this is 0. See `euclidean_geometry.angle` for the\ncorresponding unoriented angle definition. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `oangle [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`p₁ `p₂ `p₃] [":" `P] [] ")")]
       [(Term.typeSpec ":" `Real.Angle)])
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
         "."
         `oangle)
        [(Algebra.Group.Defs.«term_-ᵥ_» `p₁ " -ᵥ " `p₂)
         (Algebra.Group.Defs.«term_-ᵥ_» `p₃ " -ᵥ " `p₂)])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
        "."
        `oangle)
       [(Algebra.Group.Defs.«term_-ᵥ_» `p₁ " -ᵥ " `p₂)
        (Algebra.Group.Defs.«term_-ᵥ_» `p₃ " -ᵥ " `p₂)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_-ᵥ_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_-ᵥ_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_-ᵥ_» `p₃ " -ᵥ " `p₂)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p₂
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `p₃
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Group.Defs.«term_-ᵥ_» `p₃ " -ᵥ " `p₂)
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_-ᵥ_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_-ᵥ_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Algebra.Group.Defs.«term_-ᵥ_» `p₁ " -ᵥ " `p₂)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p₂
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `p₁
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Group.Defs.«term_-ᵥ_» `p₁ " -ᵥ " `p₂)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o") "." `oangle)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo._@.Geometry.Euclidean.Angle.Oriented.Affine._hyg.7'
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
    The oriented angle at `p₂` between the line segments to `p₁` and `p₃`, modulo `2 * π`. If
    either of those points equals `p₂`, this is 0. See `euclidean_geometry.angle` for the
    corresponding unoriented angle definition. -/
  def oangle ( p₁ p₂ p₃ : P ) : Real.Angle := o . oangle p₁ -ᵥ p₂ p₃ -ᵥ p₂
#align euclidean_geometry.oangle EuclideanGeometry.oangle

-- mathport name: oangle
scoped notation "∡" => EuclideanGeometry.oangle

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Oriented angles are continuous when neither end point equals the middle point. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `continuous_at_oangle [])
      (Command.declSig
       [(Term.implicitBinder "{" [`x] [":" («term_×_» `P "×" («term_×_» `P "×" `P))] "}")
        (Term.explicitBinder
         "("
         [`hx12]
         [":"
          («term_≠_»
           (Term.proj `x "." (fieldIdx "1"))
           "≠"
           (Term.proj (Term.proj `x "." (fieldIdx "2")) "." (fieldIdx "1")))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hx32]
         [":"
          («term_≠_»
           (Term.proj (Term.proj `x "." (fieldIdx "2")) "." (fieldIdx "2"))
           "≠"
           (Term.proj (Term.proj `x "." (fieldIdx "2")) "." (fieldIdx "1")))]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `ContinuousAt
         [(Term.fun
           "fun"
           (Term.basicFun
            [`y]
            [(Term.typeSpec ":" («term_×_» `P "×" («term_×_» `P "×" `P)))]
            "=>"
            (Term.app
             (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
             [(Term.proj `y "." (fieldIdx "1"))
              (Term.proj (Term.proj `y "." (fieldIdx "2")) "." (fieldIdx "1"))
              (Term.proj (Term.proj `y "." (fieldIdx "2")) "." (fieldIdx "2"))])))
          `x])))
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
              `f
              []
              [(Term.typeSpec
                ":"
                (Term.arrow («term_×_» `P "×" («term_×_» `P "×" `P)) "→" («term_×_» `V "×" `V)))]
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`y]
                []
                "=>"
                (Term.tuple
                 "("
                 [(Algebra.Group.Defs.«term_-ᵥ_»
                   (Term.proj `y "." (fieldIdx "1"))
                   " -ᵥ "
                   (Term.proj (Term.proj `y "." (fieldIdx "2")) "." (fieldIdx "1")))
                  ","
                  [(Algebra.Group.Defs.«term_-ᵥ_»
                    (Term.proj (Term.proj `y "." (fieldIdx "2")) "." (fieldIdx "2"))
                    " -ᵥ "
                    (Term.proj (Term.proj `y "." (fieldIdx "2")) "." (fieldIdx "1")))]]
                 ")"))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hf1 []]
              [(Term.typeSpec
                ":"
                («term_≠_» (Term.proj (Term.app `f [`x]) "." (fieldIdx "1")) "≠" (num "0")))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx12)] "]"] [])]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hf2 []]
              [(Term.typeSpec
                ":"
                («term_≠_» (Term.proj (Term.app `f [`x]) "." (fieldIdx "2")) "≠" (num "0")))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx32)] "]"] [])]))))))
           []
           (Tactic.exact
            "exact"
            (Term.app
             (Term.proj
              (Term.app
               (Term.proj
                (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
                "."
                `continuous_at_oangle)
               [`hf1 `hf2])
              "."
              `comp)
             [(Term.proj
               (Term.app
                (Term.proj (Term.app `continuous_fst.vsub [`continuous_snd.fst]) "." `prod_mk)
                [(Term.app `continuous_snd.snd.vsub [`continuous_snd.fst])])
               "."
               `ContinuousAt)]))])))
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
             `f
             []
             [(Term.typeSpec
               ":"
               (Term.arrow («term_×_» `P "×" («term_×_» `P "×" `P)) "→" («term_×_» `V "×" `V)))]
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`y]
               []
               "=>"
               (Term.tuple
                "("
                [(Algebra.Group.Defs.«term_-ᵥ_»
                  (Term.proj `y "." (fieldIdx "1"))
                  " -ᵥ "
                  (Term.proj (Term.proj `y "." (fieldIdx "2")) "." (fieldIdx "1")))
                 ","
                 [(Algebra.Group.Defs.«term_-ᵥ_»
                   (Term.proj (Term.proj `y "." (fieldIdx "2")) "." (fieldIdx "2"))
                   " -ᵥ "
                   (Term.proj (Term.proj `y "." (fieldIdx "2")) "." (fieldIdx "1")))]]
                ")"))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hf1 []]
             [(Term.typeSpec
               ":"
               («term_≠_» (Term.proj (Term.app `f [`x]) "." (fieldIdx "1")) "≠" (num "0")))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx12)] "]"] [])]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hf2 []]
             [(Term.typeSpec
               ":"
               («term_≠_» (Term.proj (Term.app `f [`x]) "." (fieldIdx "2")) "≠" (num "0")))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hx32)] "]"] [])]))))))
          []
          (Tactic.exact
           "exact"
           (Term.app
            (Term.proj
             (Term.app
              (Term.proj
               (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
               "."
               `continuous_at_oangle)
              [`hf1 `hf2])
             "."
             `comp)
            [(Term.proj
              (Term.app
               (Term.proj (Term.app `continuous_fst.vsub [`continuous_snd.fst]) "." `prod_mk)
               [(Term.app `continuous_snd.snd.vsub [`continuous_snd.fst])])
              "."
              `ContinuousAt)]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        (Term.proj
         (Term.app
          (Term.proj
           (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
           "."
           `continuous_at_oangle)
          [`hf1 `hf2])
         "."
         `comp)
        [(Term.proj
          (Term.app
           (Term.proj (Term.app `continuous_fst.vsub [`continuous_snd.fst]) "." `prod_mk)
           [(Term.app `continuous_snd.snd.vsub [`continuous_snd.fst])])
          "."
          `ContinuousAt)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app
         (Term.proj
          (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
          "."
          `continuous_at_oangle)
         [`hf1 `hf2])
        "."
        `comp)
       [(Term.proj
         (Term.app
          (Term.proj (Term.app `continuous_fst.vsub [`continuous_snd.fst]) "." `prod_mk)
          [(Term.app `continuous_snd.snd.vsub [`continuous_snd.fst])])
         "."
         `ContinuousAt)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        (Term.proj (Term.app `continuous_fst.vsub [`continuous_snd.fst]) "." `prod_mk)
        [(Term.app `continuous_snd.snd.vsub [`continuous_snd.fst])])
       "."
       `ContinuousAt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj (Term.app `continuous_fst.vsub [`continuous_snd.fst]) "." `prod_mk)
       [(Term.app `continuous_snd.snd.vsub [`continuous_snd.fst])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `continuous_snd.snd.vsub [`continuous_snd.fst])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `continuous_snd.fst
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `continuous_snd.snd.vsub
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `continuous_snd.snd.vsub [`continuous_snd.fst])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `continuous_fst.vsub [`continuous_snd.fst]) "." `prod_mk)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `continuous_fst.vsub [`continuous_snd.fst])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `continuous_snd.fst
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `continuous_fst.vsub
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `continuous_fst.vsub [`continuous_snd.fst])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj
       (Term.paren "(" (Term.app `continuous_fst.vsub [`continuous_snd.fst]) ")")
       "."
       `prod_mk)
      [(Term.paren "(" (Term.app `continuous_snd.snd.vsub [`continuous_snd.fst]) ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        (Term.proj
         (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
         "."
         `continuous_at_oangle)
        [`hf1 `hf2])
       "."
       `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj
        (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
        "."
        `continuous_at_oangle)
       [`hf1 `hf2])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hf2
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
       "."
       `continuous_at_oangle)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo._@.Geometry.Euclidean.Angle.Oriented.Affine._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Oriented angles are continuous when neither end point equals the middle point. -/
  theorem
    continuous_at_oangle
    { x : P × P × P } ( hx12 : x . 1 ≠ x . 2 . 1 ) ( hx32 : x . 2 . 2 ≠ x . 2 . 1 )
      : ContinuousAt fun y : P × P × P => ∡ y . 1 y . 2 . 1 y . 2 . 2 x
    :=
      by
        let f : P × P × P → V × V := fun y => ( y . 1 -ᵥ y . 2 . 1 , y . 2 . 2 -ᵥ y . 2 . 1 )
          have hf1 : f x . 1 ≠ 0 := by simp [ hx12 ]
          have hf2 : f x . 2 ≠ 0 := by simp [ hx32 ]
          exact
            o . continuous_at_oangle hf1 hf2 . comp
              continuous_fst.vsub continuous_snd.fst . prod_mk
                  continuous_snd.snd.vsub continuous_snd.fst
                .
                ContinuousAt
#align euclidean_geometry.continuous_at_oangle EuclideanGeometry.continuous_at_oangle

/-- The angle ∡AAB at a point. -/
@[simp]
theorem oangle_self_left (p₁ p₂ : P) : ∡ p₁ p₁ p₂ = 0 := by simp [oangle]
#align euclidean_geometry.oangle_self_left EuclideanGeometry.oangle_self_left

/-- The angle ∡ABB at a point. -/
@[simp]
theorem oangle_self_right (p₁ p₂ : P) : ∡ p₁ p₂ p₂ = 0 := by simp [oangle]
#align euclidean_geometry.oangle_self_right EuclideanGeometry.oangle_self_right

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "The angle ∡ABA at a point. -/")]
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `oangle_self_left_right [])
      (Command.declSig
       [(Term.explicitBinder "(" [`p₁ `p₂] [":" `P] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
          [`p₁ `p₂ `p₁])
         "="
         (num "0"))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
         "."
         `oangle_self)
        [(Term.hole "_")])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
        "."
        `oangle_self)
       [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
       "."
       `oangle_self)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo._@.Geometry.Euclidean.Angle.Oriented.Affine._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The angle ∡ABA at a point. -/ @[ simp ]
  theorem oangle_self_left_right ( p₁ p₂ : P ) : ∡ p₁ p₂ p₁ = 0 := o . oangle_self _
#align euclidean_geometry.oangle_self_left_right EuclideanGeometry.oangle_self_left_right

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "If the angle between three points is nonzero, the first two points are not equal. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `left_ne_of_oangle_ne_zero [])
      (Command.declSig
       [(Term.implicitBinder "{" [`p₁ `p₂ `p₃] [":" `P] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          («term_≠_»
           (Term.app
            (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
            [`p₁ `p₂ `p₃])
           "≠"
           (num "0"))]
         []
         ")")]
       (Term.typeSpec ":" («term_≠_» `p₁ "≠" `p₂)))
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
             [(Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app (Term.explicit "@" `vsub_ne_zero) [`V]))]
             "]")
            [])
           []
           (Tactic.exact
            "exact"
            (Term.app
             (Term.proj
              (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
              "."
              `left_ne_zero_of_oangle_ne_zero)
             [`h]))])))
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
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app (Term.explicit "@" `vsub_ne_zero) [`V]))]
            "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            (Term.proj
             (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
             "."
             `left_ne_zero_of_oangle_ne_zero)
            [`h]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        (Term.proj
         (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
         "."
         `left_ne_zero_of_oangle_ne_zero)
        [`h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
        "."
        `left_ne_zero_of_oangle_ne_zero)
       [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
       "."
       `left_ne_zero_of_oangle_ne_zero)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo._@.Geometry.Euclidean.Angle.Oriented.Affine._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- If the angle between three points is nonzero, the first two points are not equal. -/
  theorem
    left_ne_of_oangle_ne_zero
    { p₁ p₂ p₃ : P } ( h : ∡ p₁ p₂ p₃ ≠ 0 ) : p₁ ≠ p₂
    := by rw [ ← @ vsub_ne_zero V ] exact o . left_ne_zero_of_oangle_ne_zero h
#align euclidean_geometry.left_ne_of_oangle_ne_zero EuclideanGeometry.left_ne_of_oangle_ne_zero

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "If the angle between three points is nonzero, the last two points are not equal. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `right_ne_of_oangle_ne_zero [])
      (Command.declSig
       [(Term.implicitBinder "{" [`p₁ `p₂ `p₃] [":" `P] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          («term_≠_»
           (Term.app
            (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
            [`p₁ `p₂ `p₃])
           "≠"
           (num "0"))]
         []
         ")")]
       (Term.typeSpec ":" («term_≠_» `p₃ "≠" `p₂)))
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
             [(Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app (Term.explicit "@" `vsub_ne_zero) [`V]))]
             "]")
            [])
           []
           (Tactic.exact
            "exact"
            (Term.app
             (Term.proj
              (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
              "."
              `right_ne_zero_of_oangle_ne_zero)
             [`h]))])))
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
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app (Term.explicit "@" `vsub_ne_zero) [`V]))]
            "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            (Term.proj
             (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
             "."
             `right_ne_zero_of_oangle_ne_zero)
            [`h]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        (Term.proj
         (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
         "."
         `right_ne_zero_of_oangle_ne_zero)
        [`h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
        "."
        `right_ne_zero_of_oangle_ne_zero)
       [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
       "."
       `right_ne_zero_of_oangle_ne_zero)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo._@.Geometry.Euclidean.Angle.Oriented.Affine._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- If the angle between three points is nonzero, the last two points are not equal. -/
  theorem
    right_ne_of_oangle_ne_zero
    { p₁ p₂ p₃ : P } ( h : ∡ p₁ p₂ p₃ ≠ 0 ) : p₃ ≠ p₂
    := by rw [ ← @ vsub_ne_zero V ] exact o . right_ne_zero_of_oangle_ne_zero h
#align euclidean_geometry.right_ne_of_oangle_ne_zero EuclideanGeometry.right_ne_of_oangle_ne_zero

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "If the angle between three points is nonzero, the first and third points are not equal. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `left_ne_right_of_oangle_ne_zero [])
      (Command.declSig
       [(Term.implicitBinder "{" [`p₁ `p₂ `p₃] [":" `P] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          («term_≠_»
           (Term.app
            (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
            [`p₁ `p₂ `p₃])
           "≠"
           (num "0"))]
         []
         ")")]
       (Term.typeSpec ":" («term_≠_» `p₁ "≠" `p₃)))
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
             [(Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.proj (Term.app `vsub_left_injective [`p₂]) "." `ne_iff))]
             "]")
            [])
           []
           (Tactic.exact
            "exact"
            (Term.app
             (Term.proj
              (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
              "."
              `ne_of_oangle_ne_zero)
             [`h]))])))
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
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.proj (Term.app `vsub_left_injective [`p₂]) "." `ne_iff))]
            "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            (Term.proj
             (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
             "."
             `ne_of_oangle_ne_zero)
            [`h]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        (Term.proj
         (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
         "."
         `ne_of_oangle_ne_zero)
        [`h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
        "."
        `ne_of_oangle_ne_zero)
       [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
       "."
       `ne_of_oangle_ne_zero)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo._@.Geometry.Euclidean.Angle.Oriented.Affine._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- If the angle between three points is nonzero, the first and third points are not equal. -/
  theorem
    left_ne_right_of_oangle_ne_zero
    { p₁ p₂ p₃ : P } ( h : ∡ p₁ p₂ p₃ ≠ 0 ) : p₁ ≠ p₃
    := by rw [ ← vsub_left_injective p₂ . ne_iff ] exact o . ne_of_oangle_ne_zero h
#align
  euclidean_geometry.left_ne_right_of_oangle_ne_zero EuclideanGeometry.left_ne_right_of_oangle_ne_zero

/-- If the angle between three points is `π`, the first two points are not equal. -/
theorem left_ne_of_oangle_eq_pi {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = π) : p₁ ≠ p₂ :=
  left_ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_ne_zero : ∡ p₁ p₂ p₃ ≠ 0)
#align euclidean_geometry.left_ne_of_oangle_eq_pi EuclideanGeometry.left_ne_of_oangle_eq_pi

/-- If the angle between three points is `π`, the last two points are not equal. -/
theorem right_ne_of_oangle_eq_pi {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = π) : p₃ ≠ p₂ :=
  right_ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_ne_zero : ∡ p₁ p₂ p₃ ≠ 0)
#align euclidean_geometry.right_ne_of_oangle_eq_pi EuclideanGeometry.right_ne_of_oangle_eq_pi

/-- If the angle between three points is `π`, the first and third points are not equal. -/
theorem left_ne_right_of_oangle_eq_pi {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = π) : p₁ ≠ p₃ :=
  left_ne_right_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_ne_zero : ∡ p₁ p₂ p₃ ≠ 0)
#align
  euclidean_geometry.left_ne_right_of_oangle_eq_pi EuclideanGeometry.left_ne_right_of_oangle_eq_pi

/-- If the angle between three points is `π / 2`, the first two points are not equal. -/
theorem left_ne_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π / 2 : ℝ)) : p₁ ≠ p₂ :=
  left_ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_div_two_ne_zero : ∡ p₁ p₂ p₃ ≠ 0)
#align
  euclidean_geometry.left_ne_of_oangle_eq_pi_div_two EuclideanGeometry.left_ne_of_oangle_eq_pi_div_two

/-- If the angle between three points is `π / 2`, the last two points are not equal. -/
theorem right_ne_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π / 2 : ℝ)) : p₃ ≠ p₂ :=
  right_ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_div_two_ne_zero : ∡ p₁ p₂ p₃ ≠ 0)
#align
  euclidean_geometry.right_ne_of_oangle_eq_pi_div_two EuclideanGeometry.right_ne_of_oangle_eq_pi_div_two

/-- If the angle between three points is `π / 2`, the first and third points are not equal. -/
theorem left_ne_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π / 2 : ℝ)) :
    p₁ ≠ p₃ :=
  left_ne_right_of_oangle_ne_zero (h.symm ▸ Real.Angle.pi_div_two_ne_zero : ∡ p₁ p₂ p₃ ≠ 0)
#align
  euclidean_geometry.left_ne_right_of_oangle_eq_pi_div_two EuclideanGeometry.left_ne_right_of_oangle_eq_pi_div_two

/-- If the angle between three points is `-π / 2`, the first two points are not equal. -/
theorem left_ne_of_oangle_eq_neg_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (-π / 2 : ℝ)) :
    p₁ ≠ p₂ :=
  left_ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.neg_pi_div_two_ne_zero : ∡ p₁ p₂ p₃ ≠ 0)
#align
  euclidean_geometry.left_ne_of_oangle_eq_neg_pi_div_two EuclideanGeometry.left_ne_of_oangle_eq_neg_pi_div_two

/-- If the angle between three points is `-π / 2`, the last two points are not equal. -/
theorem right_ne_of_oangle_eq_neg_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (-π / 2 : ℝ)) :
    p₃ ≠ p₂ :=
  right_ne_of_oangle_ne_zero (h.symm ▸ Real.Angle.neg_pi_div_two_ne_zero : ∡ p₁ p₂ p₃ ≠ 0)
#align
  euclidean_geometry.right_ne_of_oangle_eq_neg_pi_div_two EuclideanGeometry.right_ne_of_oangle_eq_neg_pi_div_two

/-- If the angle between three points is `-π / 2`, the first and third points are not equal. -/
theorem left_ne_right_of_oangle_eq_neg_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (-π / 2 : ℝ)) :
    p₁ ≠ p₃ :=
  left_ne_right_of_oangle_ne_zero (h.symm ▸ Real.Angle.neg_pi_div_two_ne_zero : ∡ p₁ p₂ p₃ ≠ 0)
#align
  euclidean_geometry.left_ne_right_of_oangle_eq_neg_pi_div_two EuclideanGeometry.left_ne_right_of_oangle_eq_neg_pi_div_two

/-- If the sign of the angle between three points is nonzero, the first two points are not
equal. -/
theorem left_ne_of_oangle_sign_ne_zero {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign ≠ 0) : p₁ ≠ p₂ :=
  left_ne_of_oangle_ne_zero (Real.Angle.sign_ne_zero_iff.1 h).1
#align
  euclidean_geometry.left_ne_of_oangle_sign_ne_zero EuclideanGeometry.left_ne_of_oangle_sign_ne_zero

/-- If the sign of the angle between three points is nonzero, the last two points are not
equal. -/
theorem right_ne_of_oangle_sign_ne_zero {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign ≠ 0) : p₃ ≠ p₂ :=
  right_ne_of_oangle_ne_zero (Real.Angle.sign_ne_zero_iff.1 h).1
#align
  euclidean_geometry.right_ne_of_oangle_sign_ne_zero EuclideanGeometry.right_ne_of_oangle_sign_ne_zero

/-- If the sign of the angle between three points is nonzero, the first and third points are not
equal. -/
theorem left_ne_right_of_oangle_sign_ne_zero {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign ≠ 0) : p₁ ≠ p₃ :=
  left_ne_right_of_oangle_ne_zero (Real.Angle.sign_ne_zero_iff.1 h).1
#align
  euclidean_geometry.left_ne_right_of_oangle_sign_ne_zero EuclideanGeometry.left_ne_right_of_oangle_sign_ne_zero

/-- If the sign of the angle between three points is positive, the first two points are not
equal. -/
theorem left_ne_of_oangle_sign_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : p₁ ≠ p₂ :=
  left_ne_of_oangle_sign_ne_zero (h.symm ▸ by decide : (∡ p₁ p₂ p₃).sign ≠ 0)
#align
  euclidean_geometry.left_ne_of_oangle_sign_eq_one EuclideanGeometry.left_ne_of_oangle_sign_eq_one

/-- If the sign of the angle between three points is positive, the last two points are not
equal. -/
theorem right_ne_of_oangle_sign_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : p₃ ≠ p₂ :=
  right_ne_of_oangle_sign_ne_zero (h.symm ▸ by decide : (∡ p₁ p₂ p₃).sign ≠ 0)
#align
  euclidean_geometry.right_ne_of_oangle_sign_eq_one EuclideanGeometry.right_ne_of_oangle_sign_eq_one

/-- If the sign of the angle between three points is positive, the first and third points are not
equal. -/
theorem left_ne_right_of_oangle_sign_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : p₁ ≠ p₃ :=
  left_ne_right_of_oangle_sign_ne_zero (h.symm ▸ by decide : (∡ p₁ p₂ p₃).sign ≠ 0)
#align
  euclidean_geometry.left_ne_right_of_oangle_sign_eq_one EuclideanGeometry.left_ne_right_of_oangle_sign_eq_one

/-- If the sign of the angle between three points is negative, the first two points are not
equal. -/
theorem left_ne_of_oangle_sign_eq_neg_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = -1) : p₁ ≠ p₂ :=
  left_ne_of_oangle_sign_ne_zero (h.symm ▸ by decide : (∡ p₁ p₂ p₃).sign ≠ 0)
#align
  euclidean_geometry.left_ne_of_oangle_sign_eq_neg_one EuclideanGeometry.left_ne_of_oangle_sign_eq_neg_one

/-- If the sign of the angle between three points is negative, the last two points are not equal.
-/
theorem right_ne_of_oangle_sign_eq_neg_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = -1) : p₃ ≠ p₂ :=
  right_ne_of_oangle_sign_ne_zero (h.symm ▸ by decide : (∡ p₁ p₂ p₃).sign ≠ 0)
#align
  euclidean_geometry.right_ne_of_oangle_sign_eq_neg_one EuclideanGeometry.right_ne_of_oangle_sign_eq_neg_one

/-- If the sign of the angle between three points is negative, the first and third points are not
equal. -/
theorem left_ne_right_of_oangle_sign_eq_neg_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = -1) :
    p₁ ≠ p₃ :=
  left_ne_right_of_oangle_sign_ne_zero (h.symm ▸ by decide : (∡ p₁ p₂ p₃).sign ≠ 0)
#align
  euclidean_geometry.left_ne_right_of_oangle_sign_eq_neg_one EuclideanGeometry.left_ne_right_of_oangle_sign_eq_neg_one

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Reversing the order of the points passed to `oangle` negates the angle. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `oangle_rev [])
      (Command.declSig
       [(Term.explicitBinder "(" [`p₁ `p₂ `p₃] [":" `P] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
          [`p₃ `p₂ `p₁])
         "="
         («term-_»
          "-"
          (Term.app
           (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
           [`p₁ `p₂ `p₃])))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
         "."
         `oangle_rev)
        [(Term.hole "_") (Term.hole "_")])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
        "."
        `oangle_rev)
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
       (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
       "."
       `oangle_rev)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo._@.Geometry.Euclidean.Angle.Oriented.Affine._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Reversing the order of the points passed to `oangle` negates the angle. -/
  theorem oangle_rev ( p₁ p₂ p₃ : P ) : ∡ p₃ p₂ p₁ = - ∡ p₁ p₂ p₃ := o . oangle_rev _ _
#align euclidean_geometry.oangle_rev EuclideanGeometry.oangle_rev

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Adding an angle to that with the order of the points reversed results in 0. -/")]
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `oangle_add_oangle_rev [])
      (Command.declSig
       [(Term.explicitBinder "(" [`p₁ `p₂ `p₃] [":" `P] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_+_»
          (Term.app
           (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
           [`p₁ `p₂ `p₃])
          "+"
          (Term.app
           (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
           [`p₃ `p₂ `p₁]))
         "="
         (num "0"))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
         "."
         `oangle_add_oangle_rev)
        [(Term.hole "_") (Term.hole "_")])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
        "."
        `oangle_add_oangle_rev)
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
       (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
       "."
       `oangle_add_oangle_rev)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo._@.Geometry.Euclidean.Angle.Oriented.Affine._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Adding an angle to that with the order of the points reversed results in 0. -/ @[ simp ]
  theorem
    oangle_add_oangle_rev
    ( p₁ p₂ p₃ : P ) : ∡ p₁ p₂ p₃ + ∡ p₃ p₂ p₁ = 0
    := o . oangle_add_oangle_rev _ _
#align euclidean_geometry.oangle_add_oangle_rev EuclideanGeometry.oangle_add_oangle_rev

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "An oriented angle is zero if and only if the angle with the order of the points reversed is\nzero. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `oangle_eq_zero_iff_oangle_rev_eq_zero [])
      (Command.declSig
       [(Term.implicitBinder "{" [`p₁ `p₂ `p₃] [":" `P] "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_=_»
          (Term.app
           (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
           [`p₁ `p₂ `p₃])
          "="
          (num "0"))
         "↔"
         («term_=_»
          (Term.app
           (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
           [`p₃ `p₂ `p₁])
          "="
          (num "0")))))
      (Command.declValSimple
       ":="
       (Term.proj
        (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
        "."
        `oangle_eq_zero_iff_oangle_rev_eq_zero)
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
       "."
       `oangle_eq_zero_iff_oangle_rev_eq_zero)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo._@.Geometry.Euclidean.Angle.Oriented.Affine._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    An oriented angle is zero if and only if the angle with the order of the points reversed is
    zero. -/
  theorem
    oangle_eq_zero_iff_oangle_rev_eq_zero
    { p₁ p₂ p₃ : P } : ∡ p₁ p₂ p₃ = 0 ↔ ∡ p₃ p₂ p₁ = 0
    := o . oangle_eq_zero_iff_oangle_rev_eq_zero
#align
  euclidean_geometry.oangle_eq_zero_iff_oangle_rev_eq_zero EuclideanGeometry.oangle_eq_zero_iff_oangle_rev_eq_zero

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "An oriented angle is `π` if and only if the angle with the order of the points reversed is\n`π`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `oangle_eq_pi_iff_oangle_rev_eq_pi [])
      (Command.declSig
       [(Term.implicitBinder "{" [`p₁ `p₂ `p₃] [":" `P] "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_=_»
          (Term.app
           (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
           [`p₁ `p₂ `p₃])
          "="
          (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))
         "↔"
         («term_=_»
          (Term.app
           (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
           [`p₃ `p₂ `p₁])
          "="
          (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π")))))
      (Command.declValSimple
       ":="
       (Term.proj
        (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
        "."
        `oangle_eq_pi_iff_oangle_rev_eq_pi)
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
       "."
       `oangle_eq_pi_iff_oangle_rev_eq_pi)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo._@.Geometry.Euclidean.Angle.Oriented.Affine._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    An oriented angle is `π` if and only if the angle with the order of the points reversed is
    `π`. -/
  theorem
    oangle_eq_pi_iff_oangle_rev_eq_pi
    { p₁ p₂ p₃ : P } : ∡ p₁ p₂ p₃ = π ↔ ∡ p₃ p₂ p₁ = π
    := o . oangle_eq_pi_iff_oangle_rev_eq_pi
#align
  euclidean_geometry.oangle_eq_pi_iff_oangle_rev_eq_pi EuclideanGeometry.oangle_eq_pi_iff_oangle_rev_eq_pi

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "An oriented angle is not zero or `π` if and only if the three points are affinely\nindependent. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `oangle_ne_zero_and_ne_pi_iff_affine_independent [])
      (Command.declSig
       [(Term.implicitBinder "{" [`p₁ `p₂ `p₃] [":" `P] "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_∧_»
          («term_≠_»
           (Term.app
            (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
            [`p₁ `p₂ `p₃])
           "≠"
           (num "0"))
          "∧"
          («term_≠_»
           (Term.app
            (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
            [`p₁ `p₂ `p₃])
           "≠"
           (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π")))
         "↔"
         (Term.app
          `AffineIndependent
          [(Data.Real.Basic.termℝ "ℝ")
           (Matrix.Data.Fin.VecNotation.«term![_,» "![" [`p₁ "," `p₂ "," `p₃] "]")]))))
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
             [(Tactic.rwRule [] `oangle)
              ","
              (Tactic.rwRule
               []
               (Term.proj
                (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
                "."
                `oangle_ne_zero_and_ne_pi_iff_linear_independent))
              ","
              (Tactic.rwRule
               []
               (Term.app
                `affine_independent_iff_linear_independent_vsub
                [(Data.Real.Basic.termℝ "ℝ")
                 (Term.hole "_")
                 (Term.typeAscription "(" (num "1") ":" [(Term.app `Fin [(num "3")])] ")")]))
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app
                `linear_independent_equiv
                [(Term.proj
                  (Term.app
                   `finSuccAboveEquiv
                   [(Term.typeAscription "(" (num "1") ":" [(Term.app `Fin [(num "3")])] ")")])
                  "."
                  `toEquiv)]))]
             "]")
            [])
           []
           (convert "convert" [] `Iff.rfl [])
           []
           (Std.Tactic.Ext.«tacticExt___:_»
            "ext"
            [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))]
            [])
           []
           (Tactic.«tactic_<;>_»
            (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
            "<;>"
            (Tactic.tacticRfl "rfl"))])))
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
            [(Tactic.rwRule [] `oangle)
             ","
             (Tactic.rwRule
              []
              (Term.proj
               (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
               "."
               `oangle_ne_zero_and_ne_pi_iff_linear_independent))
             ","
             (Tactic.rwRule
              []
              (Term.app
               `affine_independent_iff_linear_independent_vsub
               [(Data.Real.Basic.termℝ "ℝ")
                (Term.hole "_")
                (Term.typeAscription "(" (num "1") ":" [(Term.app `Fin [(num "3")])] ")")]))
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app
               `linear_independent_equiv
               [(Term.proj
                 (Term.app
                  `finSuccAboveEquiv
                  [(Term.typeAscription "(" (num "1") ":" [(Term.app `Fin [(num "3")])] ")")])
                 "."
                 `toEquiv)]))]
            "]")
           [])
          []
          (convert "convert" [] `Iff.rfl [])
          []
          (Std.Tactic.Ext.«tacticExt___:_»
           "ext"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))]
           [])
          []
          (Tactic.«tactic_<;>_»
           (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
           "<;>"
           (Tactic.tacticRfl "rfl"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
       "<;>"
       (Tactic.tacticRfl "rfl"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'token.«*»'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_»
       "ext"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `i))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert "convert" [] `Iff.rfl [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Iff.rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `oangle)
         ","
         (Tactic.rwRule
          []
          (Term.proj
           (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
           "."
           `oangle_ne_zero_and_ne_pi_iff_linear_independent))
         ","
         (Tactic.rwRule
          []
          (Term.app
           `affine_independent_iff_linear_independent_vsub
           [(Data.Real.Basic.termℝ "ℝ")
            (Term.hole "_")
            (Term.typeAscription "(" (num "1") ":" [(Term.app `Fin [(num "3")])] ")")]))
         ","
         (Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app
           `linear_independent_equiv
           [(Term.proj
             (Term.app
              `finSuccAboveEquiv
              [(Term.typeAscription "(" (num "1") ":" [(Term.app `Fin [(num "3")])] ")")])
             "."
             `toEquiv)]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `linear_independent_equiv
       [(Term.proj
         (Term.app
          `finSuccAboveEquiv
          [(Term.typeAscription "(" (num "1") ":" [(Term.app `Fin [(num "3")])] ")")])
         "."
         `toEquiv)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        `finSuccAboveEquiv
        [(Term.typeAscription "(" (num "1") ":" [(Term.app `Fin [(num "3")])] ")")])
       "."
       `toEquiv)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `finSuccAboveEquiv
       [(Term.typeAscription "(" (num "1") ":" [(Term.app `Fin [(num "3")])] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" (num "1") ":" [(Term.app `Fin [(num "3")])] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Fin [(num "3")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "3")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `finSuccAboveEquiv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `finSuccAboveEquiv
      [(Term.typeAscription "(" (num "1") ":" [(Term.app `Fin [(num "3")])] ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `linear_independent_equiv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `affine_independent_iff_linear_independent_vsub
       [(Data.Real.Basic.termℝ "ℝ")
        (Term.hole "_")
        (Term.typeAscription "(" (num "1") ":" [(Term.app `Fin [(num "3")])] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" (num "1") ":" [(Term.app `Fin [(num "3")])] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Fin [(num "3")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "3")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `affine_independent_iff_linear_independent_vsub
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
       "."
       `oangle_ne_zero_and_ne_pi_iff_linear_independent)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo._@.Geometry.Euclidean.Angle.Oriented.Affine._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    An oriented angle is not zero or `π` if and only if the three points are affinely
    independent. -/
  theorem
    oangle_ne_zero_and_ne_pi_iff_affine_independent
    { p₁ p₂ p₃ : P } : ∡ p₁ p₂ p₃ ≠ 0 ∧ ∡ p₁ p₂ p₃ ≠ π ↔ AffineIndependent ℝ ![ p₁ , p₂ , p₃ ]
    :=
      by
        rw
            [
              oangle
                ,
                o . oangle_ne_zero_and_ne_pi_iff_linear_independent
                ,
                affine_independent_iff_linear_independent_vsub ℝ _ ( 1 : Fin 3 )
                ,
                ← linear_independent_equiv finSuccAboveEquiv ( 1 : Fin 3 ) . toEquiv
              ]
          convert Iff.rfl
          ext i
          fin_cases i <;> rfl
#align
  euclidean_geometry.oangle_ne_zero_and_ne_pi_iff_affine_independent EuclideanGeometry.oangle_ne_zero_and_ne_pi_iff_affine_independent

/-- An oriented angle is zero or `π` if and only if the three points are collinear. -/
theorem oangle_eq_zero_or_eq_pi_iff_collinear {p₁ p₂ p₃ : P} :
    ∡ p₁ p₂ p₃ = 0 ∨ ∡ p₁ p₂ p₃ = π ↔ Collinear ℝ ({p₁, p₂, p₃} : Set P) := by
  rw [← not_iff_not, not_or, oangle_ne_zero_and_ne_pi_iff_affine_independent,
    affine_independent_iff_not_collinear_set]
#align
  euclidean_geometry.oangle_eq_zero_or_eq_pi_iff_collinear EuclideanGeometry.oangle_eq_zero_or_eq_pi_iff_collinear

/-- If twice the oriented angles between two triples of points are equal, one triple is affinely
independent if and only if the other is. -/
theorem affine_independent_iff_of_two_zsmul_oangle_eq {p₁ p₂ p₃ p₄ p₅ p₆ : P}
    (h : (2 : ℤ) • ∡ p₁ p₂ p₃ = (2 : ℤ) • ∡ p₄ p₅ p₆) :
    AffineIndependent ℝ ![p₁, p₂, p₃] ↔ AffineIndependent ℝ ![p₄, p₅, p₆] := by
  simp_rw [← oangle_ne_zero_and_ne_pi_iff_affine_independent, ← Real.Angle.two_zsmul_ne_zero_iff, h]
#align
  euclidean_geometry.affine_independent_iff_of_two_zsmul_oangle_eq EuclideanGeometry.affine_independent_iff_of_two_zsmul_oangle_eq

/-- If twice the oriented angles between two triples of points are equal, one triple is collinear
if and only if the other is. -/
theorem collinear_iff_of_two_zsmul_oangle_eq {p₁ p₂ p₃ p₄ p₅ p₆ : P}
    (h : (2 : ℤ) • ∡ p₁ p₂ p₃ = (2 : ℤ) • ∡ p₄ p₅ p₆) :
    Collinear ℝ ({p₁, p₂, p₃} : Set P) ↔ Collinear ℝ ({p₄, p₅, p₆} : Set P) := by
  simp_rw [← oangle_eq_zero_or_eq_pi_iff_collinear, ← Real.Angle.two_zsmul_eq_zero_iff, h]
#align
  euclidean_geometry.collinear_iff_of_two_zsmul_oangle_eq EuclideanGeometry.collinear_iff_of_two_zsmul_oangle_eq

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "If corresponding pairs of points in two angles have the same vector span, twice those angles\nare equal. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `two_zsmul_oangle_of_vector_span_eq [])
      (Command.declSig
       [(Term.implicitBinder "{" [`p₁ `p₂ `p₃ `p₄ `p₅ `p₆] [":" `P] "}")
        (Term.explicitBinder
         "("
         [`h₁₂₄₅]
         [":"
          («term_=_»
           (Term.app
            `vectorSpan
            [(Data.Real.Basic.termℝ "ℝ")
             (Term.typeAscription
              "("
              («term{_}» "{" [`p₁ "," `p₂] "}")
              ":"
              [(Term.app `Set [`P])]
              ")")])
           "="
           (Term.app
            `vectorSpan
            [(Data.Real.Basic.termℝ "ℝ")
             (Term.typeAscription
              "("
              («term{_}» "{" [`p₄ "," `p₅] "}")
              ":"
              [(Term.app `Set [`P])]
              ")")]))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`h₃₂₆₅]
         [":"
          («term_=_»
           (Term.app
            `vectorSpan
            [(Data.Real.Basic.termℝ "ℝ")
             (Term.typeAscription
              "("
              («term{_}» "{" [`p₃ "," `p₂] "}")
              ":"
              [(Term.app `Set [`P])]
              ")")])
           "="
           (Term.app
            `vectorSpan
            [(Data.Real.Basic.termℝ "ℝ")
             (Term.typeAscription
              "("
              («term{_}» "{" [`p₆ "," `p₅] "}")
              ":"
              [(Term.app `Set [`P])]
              ")")]))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Algebra.Group.Defs.«term_•_»
          (Term.typeAscription "(" (num "2") ":" [(termℤ "ℤ")] ")")
          " • "
          (Term.app
           (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
           [`p₁ `p₂ `p₃]))
         "="
         (Algebra.Group.Defs.«term_•_»
          (Term.typeAscription "(" (num "2") ":" [(termℤ "ℤ")] ")")
          " • "
          (Term.app
           (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
           [`p₄ `p₅ `p₆])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Mathlib.Tactic.tacticSimp_rw__
            "simp_rw"
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `vector_span_pair)] "]")
            [(Tactic.location "at" (Tactic.locationHyp [`h₁₂₄₅ `h₃₂₆₅] []))])
           []
           (Tactic.exact
            "exact"
            (Term.app
             (Term.proj
              (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
              "."
              `two_zsmul_oangle_of_span_eq_of_span_eq)
             [`h₁₂₄₅ `h₃₂₆₅]))])))
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
         [(Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `vector_span_pair)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`h₁₂₄₅ `h₃₂₆₅] []))])
          []
          (Tactic.exact
           "exact"
           (Term.app
            (Term.proj
             (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
             "."
             `two_zsmul_oangle_of_span_eq_of_span_eq)
            [`h₁₂₄₅ `h₃₂₆₅]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        (Term.proj
         (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
         "."
         `two_zsmul_oangle_of_span_eq_of_span_eq)
        [`h₁₂₄₅ `h₃₂₆₅]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
        "."
        `two_zsmul_oangle_of_span_eq_of_span_eq)
       [`h₁₂₄₅ `h₃₂₆₅])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₃₂₆₅
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₁₂₄₅
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
       "."
       `two_zsmul_oangle_of_span_eq_of_span_eq)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo._@.Geometry.Euclidean.Angle.Oriented.Affine._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    If corresponding pairs of points in two angles have the same vector span, twice those angles
    are equal. -/
  theorem
    two_zsmul_oangle_of_vector_span_eq
    { p₁ p₂ p₃ p₄ p₅ p₆ : P }
        ( h₁₂₄₅ : vectorSpan ℝ ( { p₁ , p₂ } : Set P ) = vectorSpan ℝ ( { p₄ , p₅ } : Set P ) )
        ( h₃₂₆₅ : vectorSpan ℝ ( { p₃ , p₂ } : Set P ) = vectorSpan ℝ ( { p₆ , p₅ } : Set P ) )
      : ( 2 : ℤ ) • ∡ p₁ p₂ p₃ = ( 2 : ℤ ) • ∡ p₄ p₅ p₆
    :=
      by
        simp_rw [ vector_span_pair ] at h₁₂₄₅ h₃₂₆₅
          exact o . two_zsmul_oangle_of_span_eq_of_span_eq h₁₂₄₅ h₃₂₆₅
#align
  euclidean_geometry.two_zsmul_oangle_of_vector_span_eq EuclideanGeometry.two_zsmul_oangle_of_vector_span_eq

/-- If the lines determined by corresponding pairs of points in two angles are parallel, twice
those angles are equal. -/
theorem two_zsmul_oangle_of_parallel {p₁ p₂ p₃ p₄ p₅ p₆ : P}
    (h₁₂₄₅ : line[ℝ, p₁, p₂] ∥ line[ℝ, p₄, p₅]) (h₃₂₆₅ : line[ℝ, p₃, p₂] ∥ line[ℝ, p₆, p₅]) :
    (2 : ℤ) • ∡ p₁ p₂ p₃ = (2 : ℤ) • ∡ p₄ p₅ p₆ :=
  by
  rw [AffineSubspace.affine_span_pair_parallel_iff_vector_span_eq] at h₁₂₄₅ h₃₂₆₅
  exact two_zsmul_oangle_of_vector_span_eq h₁₂₄₅ h₃₂₆₅
#align
  euclidean_geometry.two_zsmul_oangle_of_parallel EuclideanGeometry.two_zsmul_oangle_of_parallel

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Given three points not equal to `p`, the angle between the first and the second at `p` plus\nthe angle between the second and the third equals the angle between the first and the third. -/")]
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `oangle_add [])
      (Command.declSig
       [(Term.implicitBinder "{" [`p `p₁ `p₂ `p₃] [":" `P] "}")
        (Term.explicitBinder "(" [`hp₁] [":" («term_≠_» `p₁ "≠" `p)] [] ")")
        (Term.explicitBinder "(" [`hp₂] [":" («term_≠_» `p₂ "≠" `p)] [] ")")
        (Term.explicitBinder "(" [`hp₃] [":" («term_≠_» `p₃ "≠" `p)] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_+_»
          (Term.app
           (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
           [`p₁ `p `p₂])
          "+"
          (Term.app
           (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
           [`p₂ `p `p₃]))
         "="
         (Term.app
          (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
          [`p₁ `p `p₃]))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
         "."
         `oangle_add)
        [(Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
         (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₂])
         (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₃])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
        "."
        `oangle_add)
       [(Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
        (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₂])
        (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₃])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₃])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp₃
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `vsub_ne_zero "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `vsub_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₃])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `vsub_ne_zero "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `vsub_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₂])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `vsub_ne_zero "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `vsub_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
       "."
       `oangle_add)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo._@.Geometry.Euclidean.Angle.Oriented.Affine._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      Given three points not equal to `p`, the angle between the first and the second at `p` plus
      the angle between the second and the third equals the angle between the first and the third. -/
    @[ simp ]
  theorem
    oangle_add
    { p p₁ p₂ p₃ : P } ( hp₁ : p₁ ≠ p ) ( hp₂ : p₂ ≠ p ) ( hp₃ : p₃ ≠ p )
      : ∡ p₁ p p₂ + ∡ p₂ p p₃ = ∡ p₁ p p₃
    := o . oangle_add vsub_ne_zero . 2 hp₁ vsub_ne_zero . 2 hp₂ vsub_ne_zero . 2 hp₃
#align euclidean_geometry.oangle_add EuclideanGeometry.oangle_add

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Given three points not equal to `p`, the angle between the second and the third at `p` plus\nthe angle between the first and the second equals the angle between the first and the third. -/")]
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `oangle_add_swap [])
      (Command.declSig
       [(Term.implicitBinder "{" [`p `p₁ `p₂ `p₃] [":" `P] "}")
        (Term.explicitBinder "(" [`hp₁] [":" («term_≠_» `p₁ "≠" `p)] [] ")")
        (Term.explicitBinder "(" [`hp₂] [":" («term_≠_» `p₂ "≠" `p)] [] ")")
        (Term.explicitBinder "(" [`hp₃] [":" («term_≠_» `p₃ "≠" `p)] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_+_»
          (Term.app
           (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
           [`p₂ `p `p₃])
          "+"
          (Term.app
           (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
           [`p₁ `p `p₂]))
         "="
         (Term.app
          (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
          [`p₁ `p `p₃]))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
         "."
         `oangle_add_swap)
        [(Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
         (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₂])
         (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₃])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
        "."
        `oangle_add_swap)
       [(Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
        (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₂])
        (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₃])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₃])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp₃
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `vsub_ne_zero "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `vsub_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₃])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `vsub_ne_zero "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `vsub_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₂])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `vsub_ne_zero "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `vsub_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
       "."
       `oangle_add_swap)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo._@.Geometry.Euclidean.Angle.Oriented.Affine._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      Given three points not equal to `p`, the angle between the second and the third at `p` plus
      the angle between the first and the second equals the angle between the first and the third. -/
    @[ simp ]
  theorem
    oangle_add_swap
    { p p₁ p₂ p₃ : P } ( hp₁ : p₁ ≠ p ) ( hp₂ : p₂ ≠ p ) ( hp₃ : p₃ ≠ p )
      : ∡ p₂ p p₃ + ∡ p₁ p p₂ = ∡ p₁ p p₃
    := o . oangle_add_swap vsub_ne_zero . 2 hp₁ vsub_ne_zero . 2 hp₂ vsub_ne_zero . 2 hp₃
#align euclidean_geometry.oangle_add_swap EuclideanGeometry.oangle_add_swap

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Given three points not equal to `p`, the angle between the first and the third at `p` minus\nthe angle between the first and the second equals the angle between the second and the third. -/")]
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `oangle_sub_left [])
      (Command.declSig
       [(Term.implicitBinder "{" [`p `p₁ `p₂ `p₃] [":" `P] "}")
        (Term.explicitBinder "(" [`hp₁] [":" («term_≠_» `p₁ "≠" `p)] [] ")")
        (Term.explicitBinder "(" [`hp₂] [":" («term_≠_» `p₂ "≠" `p)] [] ")")
        (Term.explicitBinder "(" [`hp₃] [":" («term_≠_» `p₃ "≠" `p)] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_-_»
          (Term.app
           (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
           [`p₁ `p `p₃])
          "-"
          (Term.app
           (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
           [`p₁ `p `p₂]))
         "="
         (Term.app
          (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
          [`p₂ `p `p₃]))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
         "."
         `oangle_sub_left)
        [(Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
         (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₂])
         (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₃])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
        "."
        `oangle_sub_left)
       [(Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
        (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₂])
        (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₃])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₃])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp₃
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `vsub_ne_zero "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `vsub_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₃])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `vsub_ne_zero "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `vsub_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₂])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `vsub_ne_zero "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `vsub_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
       "."
       `oangle_sub_left)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo._@.Geometry.Euclidean.Angle.Oriented.Affine._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      Given three points not equal to `p`, the angle between the first and the third at `p` minus
      the angle between the first and the second equals the angle between the second and the third. -/
    @[ simp ]
  theorem
    oangle_sub_left
    { p p₁ p₂ p₃ : P } ( hp₁ : p₁ ≠ p ) ( hp₂ : p₂ ≠ p ) ( hp₃ : p₃ ≠ p )
      : ∡ p₁ p p₃ - ∡ p₁ p p₂ = ∡ p₂ p p₃
    := o . oangle_sub_left vsub_ne_zero . 2 hp₁ vsub_ne_zero . 2 hp₂ vsub_ne_zero . 2 hp₃
#align euclidean_geometry.oangle_sub_left EuclideanGeometry.oangle_sub_left

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Given three points not equal to `p`, the angle between the first and the third at `p` minus\nthe angle between the second and the third equals the angle between the first and the second. -/")]
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `oangle_sub_right [])
      (Command.declSig
       [(Term.implicitBinder "{" [`p `p₁ `p₂ `p₃] [":" `P] "}")
        (Term.explicitBinder "(" [`hp₁] [":" («term_≠_» `p₁ "≠" `p)] [] ")")
        (Term.explicitBinder "(" [`hp₂] [":" («term_≠_» `p₂ "≠" `p)] [] ")")
        (Term.explicitBinder "(" [`hp₃] [":" («term_≠_» `p₃ "≠" `p)] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_-_»
          (Term.app
           (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
           [`p₁ `p `p₃])
          "-"
          (Term.app
           (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
           [`p₂ `p `p₃]))
         "="
         (Term.app
          (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
          [`p₁ `p `p₂]))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
         "."
         `oangle_sub_right)
        [(Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
         (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₂])
         (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₃])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
        "."
        `oangle_sub_right)
       [(Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
        (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₂])
        (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₃])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₃])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp₃
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `vsub_ne_zero "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `vsub_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₃])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `vsub_ne_zero "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `vsub_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₂])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `vsub_ne_zero "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `vsub_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
       "."
       `oangle_sub_right)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo._@.Geometry.Euclidean.Angle.Oriented.Affine._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      Given three points not equal to `p`, the angle between the first and the third at `p` minus
      the angle between the second and the third equals the angle between the first and the second. -/
    @[ simp ]
  theorem
    oangle_sub_right
    { p p₁ p₂ p₃ : P } ( hp₁ : p₁ ≠ p ) ( hp₂ : p₂ ≠ p ) ( hp₃ : p₃ ≠ p )
      : ∡ p₁ p p₃ - ∡ p₂ p p₃ = ∡ p₁ p p₂
    := o . oangle_sub_right vsub_ne_zero . 2 hp₁ vsub_ne_zero . 2 hp₂ vsub_ne_zero . 2 hp₃
#align euclidean_geometry.oangle_sub_right EuclideanGeometry.oangle_sub_right

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Given three points not equal to `p`, adding the angles between them at `p` in cyclic order\nresults in 0. -/")]
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `oangle_add_cyc3 [])
      (Command.declSig
       [(Term.implicitBinder "{" [`p `p₁ `p₂ `p₃] [":" `P] "}")
        (Term.explicitBinder "(" [`hp₁] [":" («term_≠_» `p₁ "≠" `p)] [] ")")
        (Term.explicitBinder "(" [`hp₂] [":" («term_≠_» `p₂ "≠" `p)] [] ")")
        (Term.explicitBinder "(" [`hp₃] [":" («term_≠_» `p₃ "≠" `p)] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_+_»
          («term_+_»
           (Term.app
            (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
            [`p₁ `p `p₂])
           "+"
           (Term.app
            (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
            [`p₂ `p `p₃]))
          "+"
          (Term.app
           (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
           [`p₃ `p `p₁]))
         "="
         (num "0"))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
         "."
         `oangle_add_cyc3)
        [(Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
         (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₂])
         (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₃])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
        "."
        `oangle_add_cyc3)
       [(Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
        (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₂])
        (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₃])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₃])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp₃
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `vsub_ne_zero "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `vsub_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₃])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `vsub_ne_zero "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `vsub_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₂])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `vsub_ne_zero "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `vsub_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
       "."
       `oangle_add_cyc3)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo._@.Geometry.Euclidean.Angle.Oriented.Affine._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      Given three points not equal to `p`, adding the angles between them at `p` in cyclic order
      results in 0. -/
    @[ simp ]
  theorem
    oangle_add_cyc3
    { p p₁ p₂ p₃ : P } ( hp₁ : p₁ ≠ p ) ( hp₂ : p₂ ≠ p ) ( hp₃ : p₃ ≠ p )
      : ∡ p₁ p p₂ + ∡ p₂ p p₃ + ∡ p₃ p p₁ = 0
    := o . oangle_add_cyc3 vsub_ne_zero . 2 hp₁ vsub_ne_zero . 2 hp₂ vsub_ne_zero . 2 hp₃
#align euclidean_geometry.oangle_add_cyc3 EuclideanGeometry.oangle_add_cyc3

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "Pons asinorum, oriented angle-at-point form. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `oangle_eq_oangle_of_dist_eq [])
      (Command.declSig
       [(Term.implicitBinder "{" [`p₁ `p₂ `p₃] [":" `P] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":" («term_=_» (Term.app `dist [`p₁ `p₂]) "=" (Term.app `dist [`p₁ `p₃]))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
          [`p₁ `p₂ `p₃])
         "="
         (Term.app
          (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
          [`p₂ `p₃ `p₁]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Mathlib.Tactic.tacticSimp_rw__
            "simp_rw"
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dist_eq_norm_vsub)] "]")
            [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `oangle)
              ","
              (Tactic.rwRule [] `oangle)
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app `vsub_sub_vsub_cancel_left [`p₃ `p₂ `p₁]))
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app `vsub_sub_vsub_cancel_left [`p₂ `p₃ `p₁]))
              ","
              (Tactic.rwRule
               []
               (Term.app
                (Term.proj
                 (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
                 "."
                 `oangle_sub_eq_oangle_sub_rev_of_norm_eq)
                [`h]))]
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
         [(Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dist_eq_norm_vsub)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `oangle)
             ","
             (Tactic.rwRule [] `oangle)
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app `vsub_sub_vsub_cancel_left [`p₃ `p₂ `p₁]))
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app `vsub_sub_vsub_cancel_left [`p₂ `p₃ `p₁]))
             ","
             (Tactic.rwRule
              []
              (Term.app
               (Term.proj
                (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
                "."
                `oangle_sub_eq_oangle_sub_rev_of_norm_eq)
               [`h]))]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `oangle)
         ","
         (Tactic.rwRule [] `oangle)
         ","
         (Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app `vsub_sub_vsub_cancel_left [`p₃ `p₂ `p₁]))
         ","
         (Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app `vsub_sub_vsub_cancel_left [`p₂ `p₃ `p₁]))
         ","
         (Tactic.rwRule
          []
          (Term.app
           (Term.proj
            (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
            "."
            `oangle_sub_eq_oangle_sub_rev_of_norm_eq)
           [`h]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
        "."
        `oangle_sub_eq_oangle_sub_rev_of_norm_eq)
       [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
       "."
       `oangle_sub_eq_oangle_sub_rev_of_norm_eq)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo._@.Geometry.Euclidean.Angle.Oriented.Affine._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Pons asinorum, oriented angle-at-point form. -/
  theorem
    oangle_eq_oangle_of_dist_eq
    { p₁ p₂ p₃ : P } ( h : dist p₁ p₂ = dist p₁ p₃ ) : ∡ p₁ p₂ p₃ = ∡ p₂ p₃ p₁
    :=
      by
        simp_rw [ dist_eq_norm_vsub ] at h
          rw
            [
              oangle
                ,
                oangle
                ,
                ← vsub_sub_vsub_cancel_left p₃ p₂ p₁
                ,
                ← vsub_sub_vsub_cancel_left p₂ p₃ p₁
                ,
                o . oangle_sub_eq_oangle_sub_rev_of_norm_eq h
              ]
#align euclidean_geometry.oangle_eq_oangle_of_dist_eq EuclideanGeometry.oangle_eq_oangle_of_dist_eq

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The angle at the apex of an isosceles triangle is `π` minus twice a base angle, oriented\nangle-at-point form. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `oangle_eq_pi_sub_two_zsmul_oangle_of_dist_eq [])
      (Command.declSig
       [(Term.implicitBinder "{" [`p₁ `p₂ `p₃] [":" `P] "}")
        (Term.explicitBinder "(" [`hn] [":" («term_≠_» `p₂ "≠" `p₃)] [] ")")
        (Term.explicitBinder
         "("
         [`h]
         [":" («term_=_» (Term.app `dist [`p₁ `p₂]) "=" (Term.app `dist [`p₁ `p₃]))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
          [`p₃ `p₁ `p₂])
         "="
         («term_-_»
          (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π")
          "-"
          (Algebra.Group.Defs.«term_•_»
           (Term.typeAscription "(" (num "2") ":" [(termℤ "ℤ")] ")")
           " • "
           (Term.app
            (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
            [`p₁ `p₂ `p₃]))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Mathlib.Tactic.tacticSimp_rw__
            "simp_rw"
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dist_eq_norm_vsub)] "]")
            [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `oangle) "," (Tactic.rwRule [] `oangle)] "]")
            [])
           []
           (convert
            "convert"
            []
            (Term.app
             (Term.proj
              (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
              "."
              `oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq)
             [(Term.hole "_") `h])
            ["using" (num "1")])
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
                 (Term.app `neg_vsub_eq_vsub_rev [`p₁ `p₃]))
                ","
                (Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 (Term.app `neg_vsub_eq_vsub_rev [`p₁ `p₂]))
                ","
                (Tactic.rwRule
                 []
                 (Term.proj
                  (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
                  "."
                  `oangle_neg_neg))]
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
               [(Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 (Term.app
                  (Term.proj
                   (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
                   "."
                   `oangle_sub_eq_oangle_sub_rev_of_norm_eq)
                  [`h]))]
               "]")
              [])
             []
             (Tactic.simp "simp" [] [] [] [] [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hn]))])])))
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
         [(Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dist_eq_norm_vsub)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `oangle) "," (Tactic.rwRule [] `oangle)] "]")
           [])
          []
          (convert
           "convert"
           []
           (Term.app
            (Term.proj
             (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
             "."
             `oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq)
            [(Term.hole "_") `h])
           ["using" (num "1")])
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
                (Term.app `neg_vsub_eq_vsub_rev [`p₁ `p₃]))
               ","
               (Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.app `neg_vsub_eq_vsub_rev [`p₁ `p₂]))
               ","
               (Tactic.rwRule
                []
                (Term.proj
                 (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
                 "."
                 `oangle_neg_neg))]
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
              [(Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.app
                 (Term.proj
                  (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
                  "."
                  `oangle_sub_eq_oangle_sub_rev_of_norm_eq)
                 [`h]))]
              "]")
             [])
            []
            (Tactic.simp "simp" [] [] [] [] [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.Simpa.simpa
             "simpa"
             []
             []
             (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hn]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.Simpa.simpa
         "simpa"
         []
         []
         (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hn]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hn]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hn
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
          [(Tactic.rwRule
            [(patternIgnore (token.«← » "←"))]
            (Term.app
             (Term.proj
              (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
              "."
              `oangle_sub_eq_oangle_sub_rev_of_norm_eq)
             [`h]))]
          "]")
         [])
        []
        (Tactic.simp "simp" [] [] [] [] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app
           (Term.proj
            (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
            "."
            `oangle_sub_eq_oangle_sub_rev_of_norm_eq)
           [`h]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
        "."
        `oangle_sub_eq_oangle_sub_rev_of_norm_eq)
       [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
       "."
       `oangle_sub_eq_oangle_sub_rev_of_norm_eq)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo._@.Geometry.Euclidean.Angle.Oriented.Affine._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The angle at the apex of an isosceles triangle is `π` minus twice a base angle, oriented
    angle-at-point form. -/
  theorem
    oangle_eq_pi_sub_two_zsmul_oangle_of_dist_eq
    { p₁ p₂ p₃ : P } ( hn : p₂ ≠ p₃ ) ( h : dist p₁ p₂ = dist p₁ p₃ )
      : ∡ p₃ p₁ p₂ = π - ( 2 : ℤ ) • ∡ p₁ p₂ p₃
    :=
      by
        simp_rw [ dist_eq_norm_vsub ] at h
          rw [ oangle , oangle ]
          convert o . oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq _ h using 1
          · rw [ ← neg_vsub_eq_vsub_rev p₁ p₃ , ← neg_vsub_eq_vsub_rev p₁ p₂ , o . oangle_neg_neg ]
          · rw [ ← o . oangle_sub_eq_oangle_sub_rev_of_norm_eq h ] simp
          · simpa using hn
#align
  euclidean_geometry.oangle_eq_pi_sub_two_zsmul_oangle_of_dist_eq EuclideanGeometry.oangle_eq_pi_sub_two_zsmul_oangle_of_dist_eq

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "A base angle of an isosceles triangle is acute, oriented angle-at-point form. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `abs_oangle_right_to_real_lt_pi_div_two_of_dist_eq [])
      (Command.declSig
       [(Term.implicitBinder "{" [`p₁ `p₂ `p₃] [":" `P] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":" («term_=_» (Term.app `dist [`p₁ `p₂]) "=" (Term.app `dist [`p₁ `p₃]))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_<_»
         («term|___|»
          (group "|")
          (Term.proj
           (Term.app
            (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
            [`p₁ `p₂ `p₃])
           "."
           `toReal)
          (group)
          "|")
         "<"
         («term_/_»
          (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π")
          "/"
          (num "2")))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Mathlib.Tactic.tacticSimp_rw__
            "simp_rw"
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dist_eq_norm_vsub)] "]")
            [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `oangle)
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app `vsub_sub_vsub_cancel_left [`p₃ `p₂ `p₁]))]
             "]")
            [])
           []
           (Tactic.exact
            "exact"
            (Term.app
             (Term.proj
              (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
              "."
              `abs_oangle_sub_right_to_real_lt_pi_div_two)
             [`h]))])))
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
         [(Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dist_eq_norm_vsub)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `oangle)
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app `vsub_sub_vsub_cancel_left [`p₃ `p₂ `p₁]))]
            "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            (Term.proj
             (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
             "."
             `abs_oangle_sub_right_to_real_lt_pi_div_two)
            [`h]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        (Term.proj
         (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
         "."
         `abs_oangle_sub_right_to_real_lt_pi_div_two)
        [`h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
        "."
        `abs_oangle_sub_right_to_real_lt_pi_div_two)
       [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
       "."
       `abs_oangle_sub_right_to_real_lt_pi_div_two)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo._@.Geometry.Euclidean.Angle.Oriented.Affine._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- A base angle of an isosceles triangle is acute, oriented angle-at-point form. -/
  theorem
    abs_oangle_right_to_real_lt_pi_div_two_of_dist_eq
    { p₁ p₂ p₃ : P } ( h : dist p₁ p₂ = dist p₁ p₃ ) : | ∡ p₁ p₂ p₃ . toReal | < π / 2
    :=
      by
        simp_rw [ dist_eq_norm_vsub ] at h
          rw [ oangle , ← vsub_sub_vsub_cancel_left p₃ p₂ p₁ ]
          exact o . abs_oangle_sub_right_to_real_lt_pi_div_two h
#align
  euclidean_geometry.abs_oangle_right_to_real_lt_pi_div_two_of_dist_eq EuclideanGeometry.abs_oangle_right_to_real_lt_pi_div_two_of_dist_eq

/-- A base angle of an isosceles triangle is acute, oriented angle-at-point form. -/
theorem abs_oangle_left_to_real_lt_pi_div_two_of_dist_eq {p₁ p₂ p₃ : P}
    (h : dist p₁ p₂ = dist p₁ p₃) : |(∡ p₂ p₃ p₁).toReal| < π / 2 :=
  oangle_eq_oangle_of_dist_eq h ▸ abs_oangle_right_to_real_lt_pi_div_two_of_dist_eq h
#align
  euclidean_geometry.abs_oangle_left_to_real_lt_pi_div_two_of_dist_eq EuclideanGeometry.abs_oangle_left_to_real_lt_pi_div_two_of_dist_eq

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The cosine of the oriented angle at `p` between two points not equal to `p` equals that of the\nunoriented angle. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `cos_oangle_eq_cos_angle [])
      (Command.declSig
       [(Term.implicitBinder "{" [`p `p₁ `p₂] [":" `P] "}")
        (Term.explicitBinder "(" [`hp₁] [":" («term_≠_» `p₁ "≠" `p)] [] ")")
        (Term.explicitBinder "(" [`hp₂] [":" («term_≠_» `p₂ "≠" `p)] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          `Real.Angle.cos
          [(Term.app
            (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
            [`p₁ `p `p₂])])
         "="
         (Term.app
          `Real.cos
          [(Term.app
            (EuclideanGeometry.Geometry.Euclidean.Angle.Unoriented.Affine.angle "∠")
            [`p₁ `p `p₂])]))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
         "."
         `cos_oangle_eq_cos_angle)
        [(Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
         (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₂])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
        "."
        `cos_oangle_eq_cos_angle)
       [(Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
        (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₂])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `vsub_ne_zero "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `vsub_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₂])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `vsub_ne_zero "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `vsub_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
       "."
       `cos_oangle_eq_cos_angle)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo._@.Geometry.Euclidean.Angle.Oriented.Affine._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The cosine of the oriented angle at `p` between two points not equal to `p` equals that of the
    unoriented angle. -/
  theorem
    cos_oangle_eq_cos_angle
    { p p₁ p₂ : P } ( hp₁ : p₁ ≠ p ) ( hp₂ : p₂ ≠ p )
      : Real.Angle.cos ∡ p₁ p p₂ = Real.cos ∠ p₁ p p₂
    := o . cos_oangle_eq_cos_angle vsub_ne_zero . 2 hp₁ vsub_ne_zero . 2 hp₂
#align euclidean_geometry.cos_oangle_eq_cos_angle EuclideanGeometry.cos_oangle_eq_cos_angle

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The oriented angle at `p` between two points not equal to `p` is plus or minus the unoriented\nangle. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `oangle_eq_angle_or_eq_neg_angle [])
      (Command.declSig
       [(Term.implicitBinder "{" [`p `p₁ `p₂] [":" `P] "}")
        (Term.explicitBinder "(" [`hp₁] [":" («term_≠_» `p₁ "≠" `p)] [] ")")
        (Term.explicitBinder "(" [`hp₂] [":" («term_≠_» `p₂ "≠" `p)] [] ")")]
       (Term.typeSpec
        ":"
        («term_∨_»
         («term_=_»
          (Term.app
           (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
           [`p₁ `p `p₂])
          "="
          (Term.app
           (EuclideanGeometry.Geometry.Euclidean.Angle.Unoriented.Affine.angle "∠")
           [`p₁ `p `p₂]))
         "∨"
         («term_=_»
          (Term.app
           (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
           [`p₁ `p `p₂])
          "="
          («term-_»
           "-"
           (Term.app
            (EuclideanGeometry.Geometry.Euclidean.Angle.Unoriented.Affine.angle "∠")
            [`p₁ `p `p₂]))))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
         "."
         `oangle_eq_angle_or_eq_neg_angle)
        [(Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
         (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₂])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
        "."
        `oangle_eq_angle_or_eq_neg_angle)
       [(Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
        (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₂])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `vsub_ne_zero "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `vsub_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₂])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `vsub_ne_zero "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `vsub_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
       "."
       `oangle_eq_angle_or_eq_neg_angle)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo._@.Geometry.Euclidean.Angle.Oriented.Affine._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The oriented angle at `p` between two points not equal to `p` is plus or minus the unoriented
    angle. -/
  theorem
    oangle_eq_angle_or_eq_neg_angle
    { p p₁ p₂ : P } ( hp₁ : p₁ ≠ p ) ( hp₂ : p₂ ≠ p )
      : ∡ p₁ p p₂ = ∠ p₁ p p₂ ∨ ∡ p₁ p p₂ = - ∠ p₁ p p₂
    := o . oangle_eq_angle_or_eq_neg_angle vsub_ne_zero . 2 hp₁ vsub_ne_zero . 2 hp₂
#align
  euclidean_geometry.oangle_eq_angle_or_eq_neg_angle EuclideanGeometry.oangle_eq_angle_or_eq_neg_angle

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The unoriented angle at `p` between two points not equal to `p` is the absolute value of the\noriented angle. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `angle_eq_abs_oangle_to_real [])
      (Command.declSig
       [(Term.implicitBinder "{" [`p `p₁ `p₂] [":" `P] "}")
        (Term.explicitBinder "(" [`hp₁] [":" («term_≠_» `p₁ "≠" `p)] [] ")")
        (Term.explicitBinder "(" [`hp₂] [":" («term_≠_» `p₂ "≠" `p)] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (EuclideanGeometry.Geometry.Euclidean.Angle.Unoriented.Affine.angle "∠")
          [`p₁ `p `p₂])
         "="
         («term|___|»
          (group "|")
          (Term.proj
           (Term.app
            (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
            [`p₁ `p `p₂])
           "."
           `toReal)
          (group)
          "|"))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
         "."
         `angle_eq_abs_oangle_to_real)
        [(Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
         (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₂])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
        "."
        `angle_eq_abs_oangle_to_real)
       [(Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
        (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₂])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `vsub_ne_zero "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `vsub_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₂])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `vsub_ne_zero "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `vsub_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
       "."
       `angle_eq_abs_oangle_to_real)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo._@.Geometry.Euclidean.Angle.Oriented.Affine._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The unoriented angle at `p` between two points not equal to `p` is the absolute value of the
    oriented angle. -/
  theorem
    angle_eq_abs_oangle_to_real
    { p p₁ p₂ : P } ( hp₁ : p₁ ≠ p ) ( hp₂ : p₂ ≠ p ) : ∠ p₁ p p₂ = | ∡ p₁ p p₂ . toReal |
    := o . angle_eq_abs_oangle_to_real vsub_ne_zero . 2 hp₁ vsub_ne_zero . 2 hp₂
#align euclidean_geometry.angle_eq_abs_oangle_to_real EuclideanGeometry.angle_eq_abs_oangle_to_real

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "If the sign of the oriented angle at `p` between two points is zero, either one of the points\nequals `p` or the unoriented angle is 0 or π. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero [])
      (Command.declSig
       [(Term.implicitBinder "{" [`p `p₁ `p₂] [":" `P] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          («term_=_»
           (Term.proj
            (Term.app
             (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
             [`p₁ `p `p₂])
            "."
            `sign)
           "="
           (num "0"))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_∨_»
         («term_=_» `p₁ "=" `p)
         "∨"
         («term_∨_»
          («term_=_» `p₂ "=" `p)
          "∨"
          («term_∨_»
           («term_=_»
            (Term.app
             (EuclideanGeometry.Geometry.Euclidean.Angle.Unoriented.Affine.angle "∠")
             [`p₁ `p `p₂])
            "="
            (num "0"))
           "∨"
           («term_=_»
            (Term.app
             (EuclideanGeometry.Geometry.Euclidean.Angle.Unoriented.Affine.angle "∠")
             [`p₁ `p `p₂])
            "="
            (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π")))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (convert
             "convert"
             []
             (Term.app
              (Term.proj
               (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
               "."
               `eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero)
              [`h])
             [])
            "<;>"
            (Tactic.simp "simp" [] [] [] [] []))])))
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
         [(Tactic.«tactic_<;>_»
           (convert
            "convert"
            []
            (Term.app
             (Term.proj
              (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
              "."
              `eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero)
             [`h])
            [])
           "<;>"
           (Tactic.simp "simp" [] [] [] [] []))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (convert
        "convert"
        []
        (Term.app
         (Term.proj
          (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
          "."
          `eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero)
         [`h])
        [])
       "<;>"
       (Tactic.simp "simp" [] [] [] [] []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (convert
       "convert"
       []
       (Term.app
        (Term.proj
         (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
         "."
         `eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero)
        [`h])
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
        "."
        `eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero)
       [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
       "."
       `eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo._@.Geometry.Euclidean.Angle.Oriented.Affine._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    If the sign of the oriented angle at `p` between two points is zero, either one of the points
    equals `p` or the unoriented angle is 0 or π. -/
  theorem
    eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero
    { p p₁ p₂ : P } ( h : ∡ p₁ p p₂ . sign = 0 ) : p₁ = p ∨ p₂ = p ∨ ∠ p₁ p p₂ = 0 ∨ ∠ p₁ p p₂ = π
    := by convert o . eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero h <;> simp
#align
  euclidean_geometry.eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero EuclideanGeometry.eq_zero_or_angle_eq_zero_or_pi_of_sign_oangle_eq_zero

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "If two unoriented angles are equal, and the signs of the corresponding oriented angles are\nequal, then the oriented angles are equal (even in degenerate cases). -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `oangle_eq_of_angle_eq_of_sign_eq [])
      (Command.declSig
       [(Term.implicitBinder "{" [`p₁ `p₂ `p₃ `p₄ `p₅ `p₆] [":" `P] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          («term_=_»
           (Term.app
            (EuclideanGeometry.Geometry.Euclidean.Angle.Unoriented.Affine.angle "∠")
            [`p₁ `p₂ `p₃])
           "="
           (Term.app
            (EuclideanGeometry.Geometry.Euclidean.Angle.Unoriented.Affine.angle "∠")
            [`p₄ `p₅ `p₆]))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hs]
         [":"
          («term_=_»
           (Term.proj
            (Term.app
             (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
             [`p₁ `p₂ `p₃])
            "."
            `sign)
           "="
           (Term.proj
            (Term.app
             (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
             [`p₄ `p₅ `p₆])
            "."
            `sign))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
          [`p₁ `p₂ `p₃])
         "="
         (Term.app
          (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
          [`p₄ `p₅ `p₆]))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
         "."
         `oangle_eq_of_angle_eq_of_sign_eq)
        [`h `hs])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
        "."
        `oangle_eq_of_angle_eq_of_sign_eq)
       [`h `hs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
       "."
       `oangle_eq_of_angle_eq_of_sign_eq)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo._@.Geometry.Euclidean.Angle.Oriented.Affine._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    If two unoriented angles are equal, and the signs of the corresponding oriented angles are
    equal, then the oriented angles are equal (even in degenerate cases). -/
  theorem
    oangle_eq_of_angle_eq_of_sign_eq
    { p₁ p₂ p₃ p₄ p₅ p₆ : P }
        ( h : ∠ p₁ p₂ p₃ = ∠ p₄ p₅ p₆ )
        ( hs : ∡ p₁ p₂ p₃ . sign = ∡ p₄ p₅ p₆ . sign )
      : ∡ p₁ p₂ p₃ = ∡ p₄ p₅ p₆
    := o . oangle_eq_of_angle_eq_of_sign_eq h hs
#align
  euclidean_geometry.oangle_eq_of_angle_eq_of_sign_eq EuclideanGeometry.oangle_eq_of_angle_eq_of_sign_eq

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "If the signs of two nondegenerate oriented angles between points are equal, the oriented\nangles are equal if and only if the unoriented angles are equal. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `angle_eq_iff_oangle_eq_of_sign_eq [])
      (Command.declSig
       [(Term.implicitBinder "{" [`p₁ `p₂ `p₃ `p₄ `p₅ `p₆] [":" `P] "}")
        (Term.explicitBinder "(" [`hp₁] [":" («term_≠_» `p₁ "≠" `p₂)] [] ")")
        (Term.explicitBinder "(" [`hp₃] [":" («term_≠_» `p₃ "≠" `p₂)] [] ")")
        (Term.explicitBinder "(" [`hp₄] [":" («term_≠_» `p₄ "≠" `p₅)] [] ")")
        (Term.explicitBinder "(" [`hp₆] [":" («term_≠_» `p₆ "≠" `p₅)] [] ")")
        (Term.explicitBinder
         "("
         [`hs]
         [":"
          («term_=_»
           (Term.proj
            (Term.app
             (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
             [`p₁ `p₂ `p₃])
            "."
            `sign)
           "="
           (Term.proj
            (Term.app
             (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
             [`p₄ `p₅ `p₆])
            "."
            `sign))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_=_»
          (Term.app
           (EuclideanGeometry.Geometry.Euclidean.Angle.Unoriented.Affine.angle "∠")
           [`p₁ `p₂ `p₃])
          "="
          (Term.app
           (EuclideanGeometry.Geometry.Euclidean.Angle.Unoriented.Affine.angle "∠")
           [`p₄ `p₅ `p₆]))
         "↔"
         («term_=_»
          (Term.app
           (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
           [`p₁ `p₂ `p₃])
          "="
          (Term.app
           (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
           [`p₄ `p₅ `p₆])))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
         "."
         `angle_eq_iff_oangle_eq_of_sign_eq)
        [(Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
         (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₃])
         (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₄])
         (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₆])
         `hs])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
        "."
        `angle_eq_iff_oangle_eq_of_sign_eq)
       [(Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
        (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₃])
        (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₄])
        (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₆])
        `hs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₆])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp₆
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `vsub_ne_zero "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `vsub_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₆])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₄])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp₄
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `vsub_ne_zero "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `vsub_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₄])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₃])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp₃
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `vsub_ne_zero "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `vsub_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₃])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `vsub_ne_zero "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `vsub_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
       "."
       `angle_eq_iff_oangle_eq_of_sign_eq)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo._@.Geometry.Euclidean.Angle.Oriented.Affine._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    If the signs of two nondegenerate oriented angles between points are equal, the oriented
    angles are equal if and only if the unoriented angles are equal. -/
  theorem
    angle_eq_iff_oangle_eq_of_sign_eq
    { p₁ p₂ p₃ p₄ p₅ p₆ : P }
        ( hp₁ : p₁ ≠ p₂ )
        ( hp₃ : p₃ ≠ p₂ )
        ( hp₄ : p₄ ≠ p₅ )
        ( hp₆ : p₆ ≠ p₅ )
        ( hs : ∡ p₁ p₂ p₃ . sign = ∡ p₄ p₅ p₆ . sign )
      : ∠ p₁ p₂ p₃ = ∠ p₄ p₅ p₆ ↔ ∡ p₁ p₂ p₃ = ∡ p₄ p₅ p₆
    :=
      o . angle_eq_iff_oangle_eq_of_sign_eq
        vsub_ne_zero . 2 hp₁ vsub_ne_zero . 2 hp₃ vsub_ne_zero . 2 hp₄ vsub_ne_zero . 2 hp₆ hs
#align
  euclidean_geometry.angle_eq_iff_oangle_eq_of_sign_eq EuclideanGeometry.angle_eq_iff_oangle_eq_of_sign_eq

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The oriented angle between three points equals the unoriented angle if the sign is\npositive. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `oangle_eq_angle_of_sign_eq_one [])
      (Command.declSig
       [(Term.implicitBinder "{" [`p₁ `p₂ `p₃] [":" `P] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          («term_=_»
           (Term.proj
            (Term.app
             (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
             [`p₁ `p₂ `p₃])
            "."
            `sign)
           "="
           (num "1"))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
          [`p₁ `p₂ `p₃])
         "="
         (Term.app
          (EuclideanGeometry.Geometry.Euclidean.Angle.Unoriented.Affine.angle "∠")
          [`p₁ `p₂ `p₃]))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
         "."
         `oangle_eq_angle_of_sign_eq_one)
        [`h])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
        "."
        `oangle_eq_angle_of_sign_eq_one)
       [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
       "."
       `oangle_eq_angle_of_sign_eq_one)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo._@.Geometry.Euclidean.Angle.Oriented.Affine._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The oriented angle between three points equals the unoriented angle if the sign is
    positive. -/
  theorem
    oangle_eq_angle_of_sign_eq_one
    { p₁ p₂ p₃ : P } ( h : ∡ p₁ p₂ p₃ . sign = 1 ) : ∡ p₁ p₂ p₃ = ∠ p₁ p₂ p₃
    := o . oangle_eq_angle_of_sign_eq_one h
#align
  euclidean_geometry.oangle_eq_angle_of_sign_eq_one EuclideanGeometry.oangle_eq_angle_of_sign_eq_one

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The oriented angle between three points equals minus the unoriented angle if the sign is\nnegative. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `oangle_eq_neg_angle_of_sign_eq_neg_one [])
      (Command.declSig
       [(Term.implicitBinder "{" [`p₁ `p₂ `p₃] [":" `P] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          («term_=_»
           (Term.proj
            (Term.app
             (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
             [`p₁ `p₂ `p₃])
            "."
            `sign)
           "="
           («term-_» "-" (num "1")))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
          [`p₁ `p₂ `p₃])
         "="
         («term-_»
          "-"
          (Term.app
           (EuclideanGeometry.Geometry.Euclidean.Angle.Unoriented.Affine.angle "∠")
           [`p₁ `p₂ `p₃])))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
         "."
         `oangle_eq_neg_angle_of_sign_eq_neg_one)
        [`h])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
        "."
        `oangle_eq_neg_angle_of_sign_eq_neg_one)
       [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
       "."
       `oangle_eq_neg_angle_of_sign_eq_neg_one)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo._@.Geometry.Euclidean.Angle.Oriented.Affine._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The oriented angle between three points equals minus the unoriented angle if the sign is
    negative. -/
  theorem
    oangle_eq_neg_angle_of_sign_eq_neg_one
    { p₁ p₂ p₃ : P } ( h : ∡ p₁ p₂ p₃ . sign = - 1 ) : ∡ p₁ p₂ p₃ = - ∠ p₁ p₂ p₃
    := o . oangle_eq_neg_angle_of_sign_eq_neg_one h
#align
  euclidean_geometry.oangle_eq_neg_angle_of_sign_eq_neg_one EuclideanGeometry.oangle_eq_neg_angle_of_sign_eq_neg_one

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The unoriented angle at `p` between two points not equal to `p` is zero if and only if the\nunoriented angle is zero. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `oangle_eq_zero_iff_angle_eq_zero [])
      (Command.declSig
       [(Term.implicitBinder "{" [`p `p₁ `p₂] [":" `P] "}")
        (Term.explicitBinder "(" [`hp₁] [":" («term_≠_» `p₁ "≠" `p)] [] ")")
        (Term.explicitBinder "(" [`hp₂] [":" («term_≠_» `p₂ "≠" `p)] [] ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_=_»
          (Term.app
           (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
           [`p₁ `p `p₂])
          "="
          (num "0"))
         "↔"
         («term_=_»
          (Term.app
           (EuclideanGeometry.Geometry.Euclidean.Angle.Unoriented.Affine.angle "∠")
           [`p₁ `p `p₂])
          "="
          (num "0")))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
         "."
         `oangle_eq_zero_iff_angle_eq_zero)
        [(Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
         (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₂])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
        "."
        `oangle_eq_zero_iff_angle_eq_zero)
       [(Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
        (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₂])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `vsub_ne_zero "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `vsub_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₂])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `vsub_ne_zero "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `vsub_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`hp₁])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
       "."
       `oangle_eq_zero_iff_angle_eq_zero)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo._@.Geometry.Euclidean.Angle.Oriented.Affine._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The unoriented angle at `p` between two points not equal to `p` is zero if and only if the
    unoriented angle is zero. -/
  theorem
    oangle_eq_zero_iff_angle_eq_zero
    { p p₁ p₂ : P } ( hp₁ : p₁ ≠ p ) ( hp₂ : p₂ ≠ p ) : ∡ p₁ p p₂ = 0 ↔ ∠ p₁ p p₂ = 0
    := o . oangle_eq_zero_iff_angle_eq_zero vsub_ne_zero . 2 hp₁ vsub_ne_zero . 2 hp₂
#align
  euclidean_geometry.oangle_eq_zero_iff_angle_eq_zero EuclideanGeometry.oangle_eq_zero_iff_angle_eq_zero

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The oriented angle between three points is `π` if and only if the unoriented angle is `π`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `oangle_eq_pi_iff_angle_eq_pi [])
      (Command.declSig
       [(Term.implicitBinder "{" [`p₁ `p₂ `p₃] [":" `P] "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_=_»
          (Term.app
           (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
           [`p₁ `p₂ `p₃])
          "="
          (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))
         "↔"
         («term_=_»
          (Term.app
           (EuclideanGeometry.Geometry.Euclidean.Angle.Unoriented.Affine.angle "∠")
           [`p₁ `p₂ `p₃])
          "="
          (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π")))))
      (Command.declValSimple
       ":="
       (Term.proj
        (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
        "."
        `oangle_eq_pi_iff_angle_eq_pi)
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
       "."
       `oangle_eq_pi_iff_angle_eq_pi)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo._@.Geometry.Euclidean.Angle.Oriented.Affine._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The oriented angle between three points is `π` if and only if the unoriented angle is `π`. -/
  theorem
    oangle_eq_pi_iff_angle_eq_pi
    { p₁ p₂ p₃ : P } : ∡ p₁ p₂ p₃ = π ↔ ∠ p₁ p₂ p₃ = π
    := o . oangle_eq_pi_iff_angle_eq_pi
#align
  euclidean_geometry.oangle_eq_pi_iff_angle_eq_pi EuclideanGeometry.oangle_eq_pi_iff_angle_eq_pi

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "If the oriented angle between three points is `π / 2`, so is the unoriented angle. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `angle_eq_pi_div_two_of_oangle_eq_pi_div_two [])
      (Command.declSig
       [(Term.implicitBinder "{" [`p₁ `p₂ `p₃] [":" `P] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          («term_=_»
           (Term.app
            (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
            [`p₁ `p₂ `p₃])
           "="
           (coeNotation
            "↑"
            («term_/_»
             (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π")
             "/"
             (num "2"))))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (EuclideanGeometry.Geometry.Euclidean.Angle.Unoriented.Affine.angle "∠")
          [`p₁ `p₂ `p₃])
         "="
         («term_/_»
          (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π")
          "/"
          (num "2")))))
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
             [(Tactic.rwRule [] `angle)
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               `InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two)]
             "]")
            [])
           []
           (Tactic.exact
            "exact"
            (Term.app
             (Term.proj
              (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
              "."
              `inner_eq_zero_of_oangle_eq_pi_div_two)
             [`h]))])))
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
            [(Tactic.rwRule [] `angle)
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              `InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two)]
            "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            (Term.proj
             (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
             "."
             `inner_eq_zero_of_oangle_eq_pi_div_two)
            [`h]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        (Term.proj
         (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
         "."
         `inner_eq_zero_of_oangle_eq_pi_div_two)
        [`h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
        "."
        `inner_eq_zero_of_oangle_eq_pi_div_two)
       [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
       "."
       `inner_eq_zero_of_oangle_eq_pi_div_two)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo._@.Geometry.Euclidean.Angle.Oriented.Affine._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- If the oriented angle between three points is `π / 2`, so is the unoriented angle. -/
  theorem
    angle_eq_pi_div_two_of_oangle_eq_pi_div_two
    { p₁ p₂ p₃ : P } ( h : ∡ p₁ p₂ p₃ = ↑ π / 2 ) : ∠ p₁ p₂ p₃ = π / 2
    :=
      by
        rw [ angle , ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two ]
          exact o . inner_eq_zero_of_oangle_eq_pi_div_two h
#align
  euclidean_geometry.angle_eq_pi_div_two_of_oangle_eq_pi_div_two EuclideanGeometry.angle_eq_pi_div_two_of_oangle_eq_pi_div_two

/-- If the oriented angle between three points is `π / 2`, so is the unoriented angle
(reversed). -/
theorem angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    ∠ p₃ p₂ p₁ = π / 2 := by
  rw [angle_comm]
  exact angle_eq_pi_div_two_of_oangle_eq_pi_div_two h
#align
  euclidean_geometry.angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two EuclideanGeometry.angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "If the oriented angle between three points is `-π / 2`, the unoriented angle is `π / 2`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `angle_eq_pi_div_two_of_oangle_eq_neg_pi_div_two [])
      (Command.declSig
       [(Term.implicitBinder "{" [`p₁ `p₂ `p₃] [":" `P] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          («term_=_»
           (Term.app
            (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
            [`p₁ `p₂ `p₃])
           "="
           (coeNotation
            "↑"
            («term_/_»
             («term-_» "-" (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π"))
             "/"
             (num "2"))))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (EuclideanGeometry.Geometry.Euclidean.Angle.Unoriented.Affine.angle "∠")
          [`p₁ `p₂ `p₃])
         "="
         («term_/_»
          (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π")
          "/"
          (num "2")))))
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
             [(Tactic.rwRule [] `angle)
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               `InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two)]
             "]")
            [])
           []
           (Tactic.exact
            "exact"
            (Term.app
             (Term.proj
              (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
              "."
              `inner_eq_zero_of_oangle_eq_neg_pi_div_two)
             [`h]))])))
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
            [(Tactic.rwRule [] `angle)
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              `InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two)]
            "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            (Term.proj
             (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
             "."
             `inner_eq_zero_of_oangle_eq_neg_pi_div_two)
            [`h]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        (Term.proj
         (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
         "."
         `inner_eq_zero_of_oangle_eq_neg_pi_div_two)
        [`h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
        "."
        `inner_eq_zero_of_oangle_eq_neg_pi_div_two)
       [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
       "."
       `inner_eq_zero_of_oangle_eq_neg_pi_div_two)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo._@.Geometry.Euclidean.Angle.Oriented.Affine._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- If the oriented angle between three points is `-π / 2`, the unoriented angle is `π / 2`. -/
  theorem
    angle_eq_pi_div_two_of_oangle_eq_neg_pi_div_two
    { p₁ p₂ p₃ : P } ( h : ∡ p₁ p₂ p₃ = ↑ - π / 2 ) : ∠ p₁ p₂ p₃ = π / 2
    :=
      by
        rw [ angle , ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two ]
          exact o . inner_eq_zero_of_oangle_eq_neg_pi_div_two h
#align
  euclidean_geometry.angle_eq_pi_div_two_of_oangle_eq_neg_pi_div_two EuclideanGeometry.angle_eq_pi_div_two_of_oangle_eq_neg_pi_div_two

/-- If the oriented angle between three points is `-π / 2`, the unoriented angle (reversed) is
`π / 2`. -/
theorem angle_rev_eq_pi_div_two_of_oangle_eq_neg_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(-π / 2)) : ∠ p₃ p₂ p₁ = π / 2 :=
  by
  rw [angle_comm]
  exact angle_eq_pi_div_two_of_oangle_eq_neg_pi_div_two h
#align
  euclidean_geometry.angle_rev_eq_pi_div_two_of_oangle_eq_neg_pi_div_two EuclideanGeometry.angle_rev_eq_pi_div_two_of_oangle_eq_neg_pi_div_two

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Swapping the first and second points in an oriented angle negates the sign of that angle. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `oangle_swap₁₂_sign [])
      (Command.declSig
       [(Term.explicitBinder "(" [`p₁ `p₂ `p₃] [":" `P] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term-_»
          "-"
          (Term.proj
           (Term.app
            (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
            [`p₁ `p₂ `p₃])
           "."
           `sign))
         "="
         (Term.proj
          (Term.app
           (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
           [`p₂ `p₁ `p₃])
          "."
          `sign))))
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
             [(Tactic.rwRule [] `eq_comm)
              ","
              (Tactic.rwRule [] `oangle)
              ","
              (Tactic.rwRule [] `oangle)
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.proj
                (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
                "."
                `oangle_neg_neg))
              ","
              (Tactic.rwRule [] `neg_vsub_eq_vsub_rev)
              ","
              (Tactic.rwRule [] `neg_vsub_eq_vsub_rev)
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app `vsub_sub_vsub_cancel_left [`p₁ `p₃ `p₂]))
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app `neg_vsub_eq_vsub_rev [`p₃ `p₂]))
              ","
              (Tactic.rwRule [] `sub_eq_add_neg)
              ","
              (Tactic.rwRule [] (Term.app `neg_vsub_eq_vsub_rev [`p₂ `p₁]))
              ","
              (Tactic.rwRule [] `add_comm)
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app (Term.explicit "@" `neg_one_smul) [(Data.Real.Basic.termℝ "ℝ")]))]
             "]")
            [])
           []
           (Mathlib.Tactic.nthRwSeq
            "nth_rw"
            []
            (num "2")
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app
                `one_smul
                [(Data.Real.Basic.termℝ "ℝ") (Algebra.Group.Defs.«term_-ᵥ_» `p₁ " -ᵥ " `p₂)]))]
             "]")
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               []
               (Term.proj
                (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
                "."
                `oangle_sign_smul_add_smul_right))]
             "]")
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
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `eq_comm)
             ","
             (Tactic.rwRule [] `oangle)
             ","
             (Tactic.rwRule [] `oangle)
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.proj
               (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
               "."
               `oangle_neg_neg))
             ","
             (Tactic.rwRule [] `neg_vsub_eq_vsub_rev)
             ","
             (Tactic.rwRule [] `neg_vsub_eq_vsub_rev)
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app `vsub_sub_vsub_cancel_left [`p₁ `p₃ `p₂]))
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app `neg_vsub_eq_vsub_rev [`p₃ `p₂]))
             ","
             (Tactic.rwRule [] `sub_eq_add_neg)
             ","
             (Tactic.rwRule [] (Term.app `neg_vsub_eq_vsub_rev [`p₂ `p₁]))
             ","
             (Tactic.rwRule [] `add_comm)
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app (Term.explicit "@" `neg_one_smul) [(Data.Real.Basic.termℝ "ℝ")]))]
            "]")
           [])
          []
          (Mathlib.Tactic.nthRwSeq
           "nth_rw"
           []
           (num "2")
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app
               `one_smul
               [(Data.Real.Basic.termℝ "ℝ") (Algebra.Group.Defs.«term_-ᵥ_» `p₁ " -ᵥ " `p₂)]))]
            "]")
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.proj
               (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
               "."
               `oangle_sign_smul_add_smul_right))]
            "]")
           [])
          []
          (Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          []
          (Term.proj
           (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
           "."
           `oangle_sign_smul_add_smul_right))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
       "."
       `oangle_sign_smul_add_smul_right)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo._@.Geometry.Euclidean.Angle.Oriented.Affine._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Swapping the first and second points in an oriented angle negates the sign of that angle. -/
  theorem
    oangle_swap₁₂_sign
    ( p₁ p₂ p₃ : P ) : - ∡ p₁ p₂ p₃ . sign = ∡ p₂ p₁ p₃ . sign
    :=
      by
        rw
            [
              eq_comm
                ,
                oangle
                ,
                oangle
                ,
                ← o . oangle_neg_neg
                ,
                neg_vsub_eq_vsub_rev
                ,
                neg_vsub_eq_vsub_rev
                ,
                ← vsub_sub_vsub_cancel_left p₁ p₃ p₂
                ,
                ← neg_vsub_eq_vsub_rev p₃ p₂
                ,
                sub_eq_add_neg
                ,
                neg_vsub_eq_vsub_rev p₂ p₁
                ,
                add_comm
                ,
                ← @ neg_one_smul ℝ
              ]
          nth_rw 2 [ ← one_smul ℝ p₁ -ᵥ p₂ ]
          rw [ o . oangle_sign_smul_add_smul_right ]
          simp
#align euclidean_geometry.oangle_swap₁₂_sign EuclideanGeometry.oangle_swap₁₂_sign

/-- Swapping the first and third points in an oriented angle negates the sign of that angle. -/
theorem oangle_swap₁₃_sign (p₁ p₂ p₃ : P) : -(∡ p₁ p₂ p₃).sign = (∡ p₃ p₂ p₁).sign := by
  rw [oangle_rev, Real.Angle.sign_neg, neg_neg]
#align euclidean_geometry.oangle_swap₁₃_sign EuclideanGeometry.oangle_swap₁₃_sign

/-- Swapping the second and third points in an oriented angle negates the sign of that angle. -/
theorem oangle_swap₂₃_sign (p₁ p₂ p₃ : P) : -(∡ p₁ p₂ p₃).sign = (∡ p₁ p₃ p₂).sign := by
  rw [oangle_swap₁₃_sign, ← oangle_swap₁₂_sign, oangle_swap₁₃_sign]
#align euclidean_geometry.oangle_swap₂₃_sign EuclideanGeometry.oangle_swap₂₃_sign

/-- Rotating the points in an oriented angle does not change the sign of that angle. -/
theorem oangle_rotate_sign (p₁ p₂ p₃ : P) : (∡ p₂ p₃ p₁).sign = (∡ p₁ p₂ p₃).sign := by
  rw [← oangle_swap₁₂_sign, oangle_swap₁₃_sign]
#align euclidean_geometry.oangle_rotate_sign EuclideanGeometry.oangle_rotate_sign

/-- The oriented angle between three points is π if and only if the second point is strictly
between the other two. -/
theorem oangle_eq_pi_iff_sbtw {p₁ p₂ p₃ : P} : ∡ p₁ p₂ p₃ = π ↔ Sbtw ℝ p₁ p₂ p₃ := by
  rw [oangle_eq_pi_iff_angle_eq_pi, angle_eq_pi_iff_sbtw]
#align euclidean_geometry.oangle_eq_pi_iff_sbtw EuclideanGeometry.oangle_eq_pi_iff_sbtw

/-- If the second of three points is strictly between the other two, the oriented angle at that
point is π. -/
theorem Sbtw.oangle₁₂₃_eq_pi {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∡ p₁ p₂ p₃ = π :=
  oangle_eq_pi_iff_sbtw.2 h
#align sbtw.oangle₁₂₃_eq_pi Sbtw.oangle₁₂₃_eq_pi

/-- If the second of three points is strictly between the other two, the oriented angle at that
point (reversed) is π. -/
theorem Sbtw.oangle₃₂₁_eq_pi {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∡ p₃ p₂ p₁ = π := by
  rw [oangle_eq_pi_iff_oangle_rev_eq_pi, ← h.oangle₁₂₃_eq_pi]
#align sbtw.oangle₃₂₁_eq_pi Sbtw.oangle₃₂₁_eq_pi

/-- If the second of three points is weakly between the other two, the oriented angle at the
first point is zero. -/
theorem Wbtw.oangle₂₁₃_eq_zero {p₁ p₂ p₃ : P} (h : Wbtw ℝ p₁ p₂ p₃) : ∡ p₂ p₁ p₃ = 0 :=
  by
  by_cases hp₂p₁ : p₂ = p₁; · simp [hp₂p₁]
  by_cases hp₃p₁ : p₃ = p₁; · simp [hp₃p₁]
  rw [oangle_eq_zero_iff_angle_eq_zero hp₂p₁ hp₃p₁]
  exact h.angle₂₁₃_eq_zero_of_ne hp₂p₁
#align wbtw.oangle₂₁₃_eq_zero Wbtw.oangle₂₁₃_eq_zero

/-- If the second of three points is strictly between the other two, the oriented angle at the
first point is zero. -/
theorem Sbtw.oangle₂₁₃_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∡ p₂ p₁ p₃ = 0 :=
  h.Wbtw.oangle₂₁₃_eq_zero
#align sbtw.oangle₂₁₃_eq_zero Sbtw.oangle₂₁₃_eq_zero

/-- If the second of three points is weakly between the other two, the oriented angle at the
first point (reversed) is zero. -/
theorem Wbtw.oangle₃₁₂_eq_zero {p₁ p₂ p₃ : P} (h : Wbtw ℝ p₁ p₂ p₃) : ∡ p₃ p₁ p₂ = 0 := by
  rw [oangle_eq_zero_iff_oangle_rev_eq_zero, h.oangle₂₁₃_eq_zero]
#align wbtw.oangle₃₁₂_eq_zero Wbtw.oangle₃₁₂_eq_zero

/-- If the second of three points is strictly between the other two, the oriented angle at the
first point (reversed) is zero. -/
theorem Sbtw.oangle₃₁₂_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∡ p₃ p₁ p₂ = 0 :=
  h.Wbtw.oangle₃₁₂_eq_zero
#align sbtw.oangle₃₁₂_eq_zero Sbtw.oangle₃₁₂_eq_zero

/-- If the second of three points is weakly between the other two, the oriented angle at the
third point is zero. -/
theorem Wbtw.oangle₂₃₁_eq_zero {p₁ p₂ p₃ : P} (h : Wbtw ℝ p₁ p₂ p₃) : ∡ p₂ p₃ p₁ = 0 :=
  h.symm.oangle₂₁₃_eq_zero
#align wbtw.oangle₂₃₁_eq_zero Wbtw.oangle₂₃₁_eq_zero

/-- If the second of three points is strictly between the other two, the oriented angle at the
third point is zero. -/
theorem Sbtw.oangle₂₃₁_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∡ p₂ p₃ p₁ = 0 :=
  h.Wbtw.oangle₂₃₁_eq_zero
#align sbtw.oangle₂₃₁_eq_zero Sbtw.oangle₂₃₁_eq_zero

/-- If the second of three points is weakly between the other two, the oriented angle at the
third point (reversed) is zero. -/
theorem Wbtw.oangle₁₃₂_eq_zero {p₁ p₂ p₃ : P} (h : Wbtw ℝ p₁ p₂ p₃) : ∡ p₁ p₃ p₂ = 0 :=
  h.symm.oangle₃₁₂_eq_zero
#align wbtw.oangle₁₃₂_eq_zero Wbtw.oangle₁₃₂_eq_zero

/-- If the second of three points is strictly between the other two, the oriented angle at the
third point (reversed) is zero. -/
theorem Sbtw.oangle₁₃₂_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∡ p₁ p₃ p₂ = 0 :=
  h.Wbtw.oangle₁₃₂_eq_zero
#align sbtw.oangle₁₃₂_eq_zero Sbtw.oangle₁₃₂_eq_zero

/-- The oriented angle between three points is zero if and only if one of the first and third
points is weakly between the other two. -/
theorem oangle_eq_zero_iff_wbtw {p₁ p₂ p₃ : P} :
    ∡ p₁ p₂ p₃ = 0 ↔ Wbtw ℝ p₂ p₁ p₃ ∨ Wbtw ℝ p₂ p₃ p₁ :=
  by
  by_cases hp₁p₂ : p₁ = p₂; · simp [hp₁p₂]
  by_cases hp₃p₂ : p₃ = p₂; · simp [hp₃p₂]
  rw [oangle_eq_zero_iff_angle_eq_zero hp₁p₂ hp₃p₂, angle_eq_zero_iff_ne_and_wbtw]
  simp [hp₁p₂, hp₃p₂]
#align euclidean_geometry.oangle_eq_zero_iff_wbtw EuclideanGeometry.oangle_eq_zero_iff_wbtw

/-- An oriented angle is unchanged by replacing the first point by one weakly further away on the
same ray. -/
theorem Wbtw.oangle_eq_left {p₁ p₁' p₂ p₃ : P} (h : Wbtw ℝ p₂ p₁ p₁') (hp₁p₂ : p₁ ≠ p₂) :
    ∡ p₁ p₂ p₃ = ∡ p₁' p₂ p₃ := by
  by_cases hp₃p₂ : p₃ = p₂; · simp [hp₃p₂]
  by_cases hp₁'p₂ : p₁' = p₂;
  · rw [hp₁'p₂, wbtw_self_iff] at h
    exact False.elim (hp₁p₂ h)
  rw [← oangle_add hp₁'p₂ hp₁p₂ hp₃p₂, h.oangle₃₁₂_eq_zero, zero_add]
#align wbtw.oangle_eq_left Wbtw.oangle_eq_left

/-- An oriented angle is unchanged by replacing the first point by one strictly further away on
the same ray. -/
theorem Sbtw.oangle_eq_left {p₁ p₁' p₂ p₃ : P} (h : Sbtw ℝ p₂ p₁ p₁') : ∡ p₁ p₂ p₃ = ∡ p₁' p₂ p₃ :=
  h.Wbtw.oangle_eq_left h.ne_left
#align sbtw.oangle_eq_left Sbtw.oangle_eq_left

/-- An oriented angle is unchanged by replacing the third point by one weakly further away on the
same ray. -/
theorem Wbtw.oangle_eq_right {p₁ p₂ p₃ p₃' : P} (h : Wbtw ℝ p₂ p₃ p₃') (hp₃p₂ : p₃ ≠ p₂) :
    ∡ p₁ p₂ p₃ = ∡ p₁ p₂ p₃' := by rw [oangle_rev, h.oangle_eq_left hp₃p₂, ← oangle_rev]
#align wbtw.oangle_eq_right Wbtw.oangle_eq_right

/-- An oriented angle is unchanged by replacing the third point by one strictly further away on
the same ray. -/
theorem Sbtw.oangle_eq_right {p₁ p₂ p₃ p₃' : P} (h : Sbtw ℝ p₂ p₃ p₃') : ∡ p₁ p₂ p₃ = ∡ p₁ p₂ p₃' :=
  h.Wbtw.oangle_eq_right h.ne_left
#align sbtw.oangle_eq_right Sbtw.oangle_eq_right

/-- An oriented angle is unchanged by replacing the first point with the midpoint of the segment
between it and the second point. -/
@[simp]
theorem oangle_midpoint_left (p₁ p₂ p₃ : P) : ∡ (midpoint ℝ p₁ p₂) p₂ p₃ = ∡ p₁ p₂ p₃ :=
  by
  by_cases h : p₁ = p₂; · simp [h]
  exact (sbtw_midpoint_of_ne ℝ h).symm.oangle_eq_left
#align euclidean_geometry.oangle_midpoint_left EuclideanGeometry.oangle_midpoint_left

/-- An oriented angle is unchanged by replacing the first point with the midpoint of the segment
between the second point and that point. -/
@[simp]
theorem oangle_midpoint_rev_left (p₁ p₂ p₃ : P) : ∡ (midpoint ℝ p₂ p₁) p₂ p₃ = ∡ p₁ p₂ p₃ := by
  rw [midpoint_comm, oangle_midpoint_left]
#align euclidean_geometry.oangle_midpoint_rev_left EuclideanGeometry.oangle_midpoint_rev_left

/-- An oriented angle is unchanged by replacing the third point with the midpoint of the segment
between it and the second point. -/
@[simp]
theorem oangle_midpoint_right (p₁ p₂ p₃ : P) : ∡ p₁ p₂ (midpoint ℝ p₃ p₂) = ∡ p₁ p₂ p₃ :=
  by
  by_cases h : p₃ = p₂; · simp [h]
  exact (sbtw_midpoint_of_ne ℝ h).symm.oangle_eq_right
#align euclidean_geometry.oangle_midpoint_right EuclideanGeometry.oangle_midpoint_right

/-- An oriented angle is unchanged by replacing the third point with the midpoint of the segment
between the second point and that point. -/
@[simp]
theorem oangle_midpoint_rev_right (p₁ p₂ p₃ : P) : ∡ p₁ p₂ (midpoint ℝ p₂ p₃) = ∡ p₁ p₂ p₃ := by
  rw [midpoint_comm, oangle_midpoint_right]
#align euclidean_geometry.oangle_midpoint_rev_right EuclideanGeometry.oangle_midpoint_rev_right

/-- Replacing the first point by one on the same line but the opposite ray adds π to the oriented
angle. -/
theorem Sbtw.oangle_eq_add_pi_left {p₁ p₁' p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₁') (hp₃p₂ : p₃ ≠ p₂) :
    ∡ p₁ p₂ p₃ = ∡ p₁' p₂ p₃ + π := by
  rw [← h.oangle₁₂₃_eq_pi, oangle_add_swap h.left_ne h.right_ne hp₃p₂]
#align sbtw.oangle_eq_add_pi_left Sbtw.oangle_eq_add_pi_left

/-- Replacing the third point by one on the same line but the opposite ray adds π to the oriented
angle. -/
theorem Sbtw.oangle_eq_add_pi_right {p₁ p₂ p₃ p₃' : P} (h : Sbtw ℝ p₃ p₂ p₃') (hp₁p₂ : p₁ ≠ p₂) :
    ∡ p₁ p₂ p₃ = ∡ p₁ p₂ p₃' + π := by
  rw [← h.oangle₃₂₁_eq_pi, oangle_add hp₁p₂ h.right_ne h.left_ne]
#align sbtw.oangle_eq_add_pi_right Sbtw.oangle_eq_add_pi_right

/-- Replacing both the first and third points by ones on the same lines but the opposite rays
does not change the oriented angle (vertically opposite angles). -/
theorem Sbtw.oangle_eq_left_right {p₁ p₁' p₂ p₃ p₃' : P} (h₁ : Sbtw ℝ p₁ p₂ p₁')
    (h₃ : Sbtw ℝ p₃ p₂ p₃') : ∡ p₁ p₂ p₃ = ∡ p₁' p₂ p₃' := by
  rw [h₁.oangle_eq_add_pi_left h₃.left_ne, h₃.oangle_eq_add_pi_right h₁.right_ne, add_assoc,
    Real.Angle.coe_pi_add_coe_pi, add_zero]
#align sbtw.oangle_eq_left_right Sbtw.oangle_eq_left_right

/-- Replacing the first point by one on the same line does not change twice the oriented angle. -/
theorem Collinear.two_zsmul_oangle_eq_left {p₁ p₁' p₂ p₃ : P}
    (h : Collinear ℝ ({p₁, p₂, p₁'} : Set P)) (hp₁p₂ : p₁ ≠ p₂) (hp₁'p₂ : p₁' ≠ p₂) :
    (2 : ℤ) • ∡ p₁ p₂ p₃ = (2 : ℤ) • ∡ p₁' p₂ p₃ :=
  by
  by_cases hp₃p₂ : p₃ = p₂; · simp [hp₃p₂]
  rcases h.wbtw_or_wbtw_or_wbtw with (hw | hw | hw)
  · have hw' : Sbtw ℝ p₁ p₂ p₁' := ⟨hw, hp₁p₂.symm, hp₁'p₂.symm⟩
    rw [hw'.oangle_eq_add_pi_left hp₃p₂, smul_add, Real.Angle.two_zsmul_coe_pi, add_zero]
  · rw [hw.oangle_eq_left hp₁'p₂]
  · rw [hw.symm.oangle_eq_left hp₁p₂]
#align collinear.two_zsmul_oangle_eq_left Collinear.two_zsmul_oangle_eq_left

/-- Replacing the third point by one on the same line does not change twice the oriented angle. -/
theorem Collinear.two_zsmul_oangle_eq_right {p₁ p₂ p₃ p₃' : P}
    (h : Collinear ℝ ({p₃, p₂, p₃'} : Set P)) (hp₃p₂ : p₃ ≠ p₂) (hp₃'p₂ : p₃' ≠ p₂) :
    (2 : ℤ) • ∡ p₁ p₂ p₃ = (2 : ℤ) • ∡ p₁ p₂ p₃' := by
  rw [oangle_rev, smul_neg, h.two_zsmul_oangle_eq_left hp₃p₂ hp₃'p₂, ← smul_neg, ← oangle_rev]
#align collinear.two_zsmul_oangle_eq_right Collinear.two_zsmul_oangle_eq_right

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Two different points are equidistant from a third point if and only if that third point\nequals some multiple of a `π / 2` rotation of the vector between those points, plus the midpoint\nof those points. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `dist_eq_iff_eq_smul_rotation_pi_div_two_vadd_midpoint [])
      (Command.declSig
       [(Term.implicitBinder "{" [`p₁ `p₂ `p] [":" `P] "}")
        (Term.explicitBinder "(" [`h] [":" («term_≠_» `p₁ "≠" `p₂)] [] ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_=_» (Term.app `dist [`p₁ `p]) "=" (Term.app `dist [`p₂ `p]))
         "↔"
         («term∃_,_»
          "∃"
          (Lean.explicitBinders
           (Lean.unbracketedExplicitBinders
            [(Lean.binderIdent `r)]
            [":" (Data.Real.Basic.termℝ "ℝ")]))
          ","
          («term_=_»
           (Algebra.Group.Defs.«term_+ᵥ_»
            (Algebra.Group.Defs.«term_•_»
             `r
             " • "
             (Term.app
              (Term.proj
               (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
               "."
               `rotation)
              [(Term.typeAscription
                "("
                («term_/_»
                 (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π")
                 "/"
                 (num "2"))
                ":"
                [(Data.Real.Basic.termℝ "ℝ")]
                ")")
               (Algebra.Group.Defs.«term_-ᵥ_» `p₂ " -ᵥ " `p₁)]))
            " +ᵥ "
            (Term.app `midpoint [(Data.Real.Basic.termℝ "ℝ") `p₁ `p₂]))
           "="
           `p)))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.anonymousCtor
             "⟨"
             [(Term.fun "fun" (Term.basicFun [`hd] [] "=>" (Term.hole "_")))
              ","
              (Term.fun "fun" (Term.basicFun [`hr] [] "=>" (Term.hole "_")))]
             "⟩"))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`hi []]
                [(Term.typeSpec
                  ":"
                  («term_=_»
                   (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real
                    "⟪"
                    (Algebra.Group.Defs.«term_-ᵥ_» `p₂ " -ᵥ " `p₁)
                    ", "
                    (Algebra.Group.Defs.«term_-ᵥ_»
                     `p
                     " -ᵥ "
                     (Term.app `midpoint [(Data.Real.Basic.termℝ "ℝ") `p₁ `p₂]))
                    "⟫")
                   "="
                   (num "0")))]
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
                      [(Tactic.rwRule [] (Term.app (Term.explicit "@" `dist_eq_norm_vsub') [`V]))
                       ","
                       (Tactic.rwRule [] (Term.app (Term.explicit "@" `dist_eq_norm_vsub') [`V]))
                       ","
                       (Tactic.rwRule
                        [(patternIgnore (token.«← » "←"))]
                        (Term.app
                         `mul_self_inj
                         [(Term.app `norm_nonneg [(Term.hole "_")])
                          (Term.app `norm_nonneg [(Term.hole "_")])]))
                       ","
                       (Tactic.rwRule
                        [(patternIgnore (token.«← » "←"))]
                        `real_inner_self_eq_norm_mul_norm)
                       ","
                       (Tactic.rwRule
                        [(patternIgnore (token.«← » "←"))]
                        `real_inner_self_eq_norm_mul_norm)]
                      "]")
                     [(Tactic.location "at" (Tactic.locationHyp [`hd] []))])
                    []
                    (Mathlib.Tactic.tacticSimp_rw__
                     "simp_rw"
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] `vsub_midpoint)
                       ","
                       (Tactic.rwRule
                        [(patternIgnore (token.«← » "←"))]
                        (Term.app `vsub_sub_vsub_cancel_left [`p₂ `p₁ `p]))
                       ","
                       (Tactic.rwRule [] `inner_sub_left)
                       ","
                       (Tactic.rwRule [] `inner_add_right)
                       ","
                       (Tactic.rwRule [] `inner_smul_right)
                       ","
                       (Tactic.rwRule [] `hd)
                       ","
                       (Tactic.rwRule
                        []
                        (Term.app
                         `real_inner_comm
                         [(Algebra.Group.Defs.«term_-ᵥ_» `p " -ᵥ " `p₁)]))]
                      "]")
                     [])
                    []
                    (Tactic.abel "abel" [] [])]))))))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 []
                 (Term.app
                  (Term.explicit
                   "@"
                   `Orientation.inner_eq_zero_iff_eq_zero_or_eq_smul_rotation_pi_div_two)
                  [`V
                   (Term.hole "_")
                   (Term.hole "_")
                   (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")]))
                ","
                (Tactic.rwRule
                 []
                 (Term.app
                  `or_iff_right
                  [(Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`h.symm])]))]
               "]")
              [(Tactic.location "at" (Tactic.locationHyp [`hi] []))])
             []
             (Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] `hi)]
              ["with"
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr)])
                     [])]
                   "⟩")])
                [])])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `eq_comm)
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eq_vadd_iff_vsub_eq)]
               "]")
              [(Tactic.location "at" (Tactic.locationHyp [`hr] []))])
             []
             (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`r "," `hr.symm] "⟩"))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] `hr)]
              ["with"
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                     [])]
                   "⟩")])
                [])])
             []
             (Mathlib.Tactic.tacticSimp_rw__
              "simp_rw"
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] (Term.app (Term.explicit "@" `dist_eq_norm_vsub) [`V]))
                ","
                (Tactic.rwRule [] `vsub_vadd_eq_vsub_sub)
                ","
                (Tactic.rwRule [] `left_vsub_midpoint)
                ","
                (Tactic.rwRule [] `right_vsub_midpoint)
                ","
                (Tactic.rwRule [] `invOf_eq_inv)
                ","
                (Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 (Term.app `neg_vsub_eq_vsub_rev [`p₂ `p₁]))
                ","
                (Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 (Term.app
                  `mul_self_inj
                  [(Term.app `norm_nonneg [(Term.hole "_")])
                   (Term.app `norm_nonneg [(Term.hole "_")])]))
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `real_inner_self_eq_norm_mul_norm)
                ","
                (Tactic.rwRule [] `inner_sub_sub_self)]
               "]")
              [])
             []
             (Tactic.simp
              "simp"
              []
              []
              []
              ["[" [(Tactic.simpErase "-" `neg_vsub_eq_vsub_rev)] "]"]
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
         [(Tactic.refine'
           "refine'"
           (Term.anonymousCtor
            "⟨"
            [(Term.fun "fun" (Term.basicFun [`hd] [] "=>" (Term.hole "_")))
             ","
             (Term.fun "fun" (Term.basicFun [`hr] [] "=>" (Term.hole "_")))]
            "⟩"))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`hi []]
               [(Term.typeSpec
                 ":"
                 («term_=_»
                  (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real
                   "⟪"
                   (Algebra.Group.Defs.«term_-ᵥ_» `p₂ " -ᵥ " `p₁)
                   ", "
                   (Algebra.Group.Defs.«term_-ᵥ_»
                    `p
                    " -ᵥ "
                    (Term.app `midpoint [(Data.Real.Basic.termℝ "ℝ") `p₁ `p₂]))
                   "⟫")
                  "="
                  (num "0")))]
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
                     [(Tactic.rwRule [] (Term.app (Term.explicit "@" `dist_eq_norm_vsub') [`V]))
                      ","
                      (Tactic.rwRule [] (Term.app (Term.explicit "@" `dist_eq_norm_vsub') [`V]))
                      ","
                      (Tactic.rwRule
                       [(patternIgnore (token.«← » "←"))]
                       (Term.app
                        `mul_self_inj
                        [(Term.app `norm_nonneg [(Term.hole "_")])
                         (Term.app `norm_nonneg [(Term.hole "_")])]))
                      ","
                      (Tactic.rwRule
                       [(patternIgnore (token.«← » "←"))]
                       `real_inner_self_eq_norm_mul_norm)
                      ","
                      (Tactic.rwRule
                       [(patternIgnore (token.«← » "←"))]
                       `real_inner_self_eq_norm_mul_norm)]
                     "]")
                    [(Tactic.location "at" (Tactic.locationHyp [`hd] []))])
                   []
                   (Mathlib.Tactic.tacticSimp_rw__
                    "simp_rw"
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] `vsub_midpoint)
                      ","
                      (Tactic.rwRule
                       [(patternIgnore (token.«← » "←"))]
                       (Term.app `vsub_sub_vsub_cancel_left [`p₂ `p₁ `p]))
                      ","
                      (Tactic.rwRule [] `inner_sub_left)
                      ","
                      (Tactic.rwRule [] `inner_add_right)
                      ","
                      (Tactic.rwRule [] `inner_smul_right)
                      ","
                      (Tactic.rwRule [] `hd)
                      ","
                      (Tactic.rwRule
                       []
                       (Term.app `real_inner_comm [(Algebra.Group.Defs.«term_-ᵥ_» `p " -ᵥ " `p₁)]))]
                     "]")
                    [])
                   []
                   (Tactic.abel "abel" [] [])]))))))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                []
                (Term.app
                 (Term.explicit
                  "@"
                  `Orientation.inner_eq_zero_iff_eq_zero_or_eq_smul_rotation_pi_div_two)
                 [`V
                  (Term.hole "_")
                  (Term.hole "_")
                  (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")]))
               ","
               (Tactic.rwRule
                []
                (Term.app
                 `or_iff_right
                 [(Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`h.symm])]))]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`hi] []))])
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] `hi)]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr)])
                    [])]
                  "⟩")])
               [])])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `eq_comm)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eq_vadd_iff_vsub_eq)]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`hr] []))])
            []
            (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`r "," `hr.symm] "⟩"))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] `hr)]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                    [])]
                  "⟩")])
               [])])
            []
            (Mathlib.Tactic.tacticSimp_rw__
             "simp_rw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] (Term.app (Term.explicit "@" `dist_eq_norm_vsub) [`V]))
               ","
               (Tactic.rwRule [] `vsub_vadd_eq_vsub_sub)
               ","
               (Tactic.rwRule [] `left_vsub_midpoint)
               ","
               (Tactic.rwRule [] `right_vsub_midpoint)
               ","
               (Tactic.rwRule [] `invOf_eq_inv)
               ","
               (Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.app `neg_vsub_eq_vsub_rev [`p₂ `p₁]))
               ","
               (Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.app
                 `mul_self_inj
                 [(Term.app `norm_nonneg [(Term.hole "_")])
                  (Term.app `norm_nonneg [(Term.hole "_")])]))
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `real_inner_self_eq_norm_mul_norm)
               ","
               (Tactic.rwRule [] `inner_sub_sub_self)]
              "]")
             [])
            []
            (Tactic.simp
             "simp"
             []
             []
             []
             ["[" [(Tactic.simpErase "-" `neg_vsub_eq_vsub_rev)] "]"]
             [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] `hr)]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                [])]
              "⟩")])
           [])])
        []
        (Mathlib.Tactic.tacticSimp_rw__
         "simp_rw"
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] (Term.app (Term.explicit "@" `dist_eq_norm_vsub) [`V]))
           ","
           (Tactic.rwRule [] `vsub_vadd_eq_vsub_sub)
           ","
           (Tactic.rwRule [] `left_vsub_midpoint)
           ","
           (Tactic.rwRule [] `right_vsub_midpoint)
           ","
           (Tactic.rwRule [] `invOf_eq_inv)
           ","
           (Tactic.rwRule
            [(patternIgnore (token.«← » "←"))]
            (Term.app `neg_vsub_eq_vsub_rev [`p₂ `p₁]))
           ","
           (Tactic.rwRule
            [(patternIgnore (token.«← » "←"))]
            (Term.app
             `mul_self_inj
             [(Term.app `norm_nonneg [(Term.hole "_")]) (Term.app `norm_nonneg [(Term.hole "_")])]))
           ","
           (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `real_inner_self_eq_norm_mul_norm)
           ","
           (Tactic.rwRule [] `inner_sub_sub_self)]
          "]")
         [])
        []
        (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpErase "-" `neg_vsub_eq_vsub_rev)] "]"] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpErase "-" `neg_vsub_eq_vsub_rev)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpErase', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `neg_vsub_eq_vsub_rev
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] (Term.app (Term.explicit "@" `dist_eq_norm_vsub) [`V]))
         ","
         (Tactic.rwRule [] `vsub_vadd_eq_vsub_sub)
         ","
         (Tactic.rwRule [] `left_vsub_midpoint)
         ","
         (Tactic.rwRule [] `right_vsub_midpoint)
         ","
         (Tactic.rwRule [] `invOf_eq_inv)
         ","
         (Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app `neg_vsub_eq_vsub_rev [`p₂ `p₁]))
         ","
         (Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app
           `mul_self_inj
           [(Term.app `norm_nonneg [(Term.hole "_")]) (Term.app `norm_nonneg [(Term.hole "_")])]))
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `real_inner_self_eq_norm_mul_norm)
         ","
         (Tactic.rwRule [] `inner_sub_sub_self)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner_sub_sub_self
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `real_inner_self_eq_norm_mul_norm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mul_self_inj
       [(Term.app `norm_nonneg [(Term.hole "_")]) (Term.app `norm_nonneg [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `norm_nonneg [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `norm_nonneg [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `norm_nonneg [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `norm_nonneg [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_self_inj
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `neg_vsub_eq_vsub_rev [`p₂ `p₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `neg_vsub_eq_vsub_rev
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `invOf_eq_inv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `right_vsub_midpoint
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `left_vsub_midpoint
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `vsub_vadd_eq_vsub_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.explicit "@" `dist_eq_norm_vsub) [`V])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `V
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `dist_eq_norm_vsub)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `dist_eq_norm_vsub
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] `hr)]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hr
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hi []]
           [(Term.typeSpec
             ":"
             («term_=_»
              (RealInnerProductSpace.Analysis.InnerProductSpace.Basic.inner.real
               "⟪"
               (Algebra.Group.Defs.«term_-ᵥ_» `p₂ " -ᵥ " `p₁)
               ", "
               (Algebra.Group.Defs.«term_-ᵥ_»
                `p
                " -ᵥ "
                (Term.app `midpoint [(Data.Real.Basic.termℝ "ℝ") `p₁ `p₂]))
               "⟫")
              "="
              (num "0")))]
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
                 [(Tactic.rwRule [] (Term.app (Term.explicit "@" `dist_eq_norm_vsub') [`V]))
                  ","
                  (Tactic.rwRule [] (Term.app (Term.explicit "@" `dist_eq_norm_vsub') [`V]))
                  ","
                  (Tactic.rwRule
                   [(patternIgnore (token.«← » "←"))]
                   (Term.app
                    `mul_self_inj
                    [(Term.app `norm_nonneg [(Term.hole "_")])
                     (Term.app `norm_nonneg [(Term.hole "_")])]))
                  ","
                  (Tactic.rwRule
                   [(patternIgnore (token.«← » "←"))]
                   `real_inner_self_eq_norm_mul_norm)
                  ","
                  (Tactic.rwRule
                   [(patternIgnore (token.«← » "←"))]
                   `real_inner_self_eq_norm_mul_norm)]
                 "]")
                [(Tactic.location "at" (Tactic.locationHyp [`hd] []))])
               []
               (Mathlib.Tactic.tacticSimp_rw__
                "simp_rw"
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `vsub_midpoint)
                  ","
                  (Tactic.rwRule
                   [(patternIgnore (token.«← » "←"))]
                   (Term.app `vsub_sub_vsub_cancel_left [`p₂ `p₁ `p]))
                  ","
                  (Tactic.rwRule [] `inner_sub_left)
                  ","
                  (Tactic.rwRule [] `inner_add_right)
                  ","
                  (Tactic.rwRule [] `inner_smul_right)
                  ","
                  (Tactic.rwRule [] `hd)
                  ","
                  (Tactic.rwRule
                   []
                   (Term.app `real_inner_comm [(Algebra.Group.Defs.«term_-ᵥ_» `p " -ᵥ " `p₁)]))]
                 "]")
                [])
               []
               (Tactic.abel "abel" [] [])]))))))
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            []
            (Term.app
             (Term.explicit
              "@"
              `Orientation.inner_eq_zero_iff_eq_zero_or_eq_smul_rotation_pi_div_two)
             [`V
              (Term.hole "_")
              (Term.hole "_")
              (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")]))
           ","
           (Tactic.rwRule
            []
            (Term.app
             `or_iff_right
             [(Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`h.symm])]))]
          "]")
         [(Tactic.location "at" (Tactic.locationHyp [`hi] []))])
        []
        (Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] `hi)]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr)])
                [])]
              "⟩")])
           [])])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `eq_comm)
           ","
           (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eq_vadd_iff_vsub_eq)]
          "]")
         [(Tactic.location "at" (Tactic.locationHyp [`hr] []))])
        []
        (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`r "," `hr.symm] "⟩"))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`r "," `hr.symm] "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`r "," `hr.symm] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hr.symm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `eq_comm)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eq_vadd_iff_vsub_eq)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`hr] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq_vadd_iff_vsub_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] `hi)]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hi
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          []
          (Term.app
           (Term.explicit "@" `Orientation.inner_eq_zero_iff_eq_zero_or_eq_smul_rotation_pi_div_two)
           [`V
            (Term.hole "_")
            (Term.hole "_")
            (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")]))
         ","
         (Tactic.rwRule
          []
          (Term.app
           `or_iff_right
           [(Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`h.symm])]))]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`hi] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hi
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `or_iff_right [(Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`h.symm])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`h.symm])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h.symm
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `vsub_ne_zero "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `vsub_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `vsub_ne_zero "." (fieldIdx "2")) [`h.symm])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `or_iff_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicit "@" `Orientation.inner_eq_zero_iff_eq_zero_or_eq_smul_rotation_pi_div_two)
       [`V
        (Term.hole "_")
        (Term.hole "_")
        (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.termo._@.Geometry.Euclidean.Angle.Oriented.Affine._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    Two different points are equidistant from a third point if and only if that third point
    equals some multiple of a `π / 2` rotation of the vector between those points, plus the midpoint
    of those points. -/
  theorem
    dist_eq_iff_eq_smul_rotation_pi_div_two_vadd_midpoint
    { p₁ p₂ p : P } ( h : p₁ ≠ p₂ )
      :
        dist p₁ p = dist p₂ p
          ↔
          ∃ r : ℝ , r • o . rotation ( π / 2 : ℝ ) p₂ -ᵥ p₁ +ᵥ midpoint ℝ p₁ p₂ = p
    :=
      by
        refine' ⟨ fun hd => _ , fun hr => _ ⟩
          ·
            have
                hi
                  : ⟪ p₂ -ᵥ p₁ , p -ᵥ midpoint ℝ p₁ p₂ ⟫ = 0
                  :=
                  by
                    rw
                        [
                          @ dist_eq_norm_vsub' V
                            ,
                            @ dist_eq_norm_vsub' V
                            ,
                            ← mul_self_inj norm_nonneg _ norm_nonneg _
                            ,
                            ← real_inner_self_eq_norm_mul_norm
                            ,
                            ← real_inner_self_eq_norm_mul_norm
                          ]
                        at hd
                      simp_rw
                        [
                          vsub_midpoint
                            ,
                            ← vsub_sub_vsub_cancel_left p₂ p₁ p
                            ,
                            inner_sub_left
                            ,
                            inner_add_right
                            ,
                            inner_smul_right
                            ,
                            hd
                            ,
                            real_inner_comm p -ᵥ p₁
                          ]
                      abel
              rw
                [
                  @ Orientation.inner_eq_zero_iff_eq_zero_or_eq_smul_rotation_pi_div_two V _ _ o
                    ,
                    or_iff_right vsub_ne_zero . 2 h.symm
                  ]
                at hi
              rcases hi with ⟨ r , hr ⟩
              rw [ eq_comm , ← eq_vadd_iff_vsub_eq ] at hr
              exact ⟨ r , hr.symm ⟩
          ·
            rcases hr with ⟨ r , rfl ⟩
              simp_rw
                [
                  @ dist_eq_norm_vsub V
                    ,
                    vsub_vadd_eq_vsub_sub
                    ,
                    left_vsub_midpoint
                    ,
                    right_vsub_midpoint
                    ,
                    invOf_eq_inv
                    ,
                    ← neg_vsub_eq_vsub_rev p₂ p₁
                    ,
                    ← mul_self_inj norm_nonneg _ norm_nonneg _
                    ,
                    ← real_inner_self_eq_norm_mul_norm
                    ,
                    inner_sub_sub_self
                  ]
              simp [ - neg_vsub_eq_vsub_rev ]
#align
  euclidean_geometry.dist_eq_iff_eq_smul_rotation_pi_div_two_vadd_midpoint EuclideanGeometry.dist_eq_iff_eq_smul_rotation_pi_div_two_vadd_midpoint

open AffineSubspace

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Given two pairs of distinct points on the same line, such that the vectors between those
pairs of points are on the same ray (oriented in the same direction on that line), and a fifth
point, the angles at the fifth point between each of those two pairs of points have the same
sign. -/
theorem Collinear.oangle_sign_of_same_ray_vsub {p₁ p₂ p₃ p₄ : P} (p₅ : P) (hp₁p₂ : p₁ ≠ p₂)
    (hp₃p₄ : p₃ ≠ p₄) (hc : Collinear ℝ ({p₁, p₂, p₃, p₄} : Set P))
    (hr : SameRay ℝ (p₂ -ᵥ p₁) (p₄ -ᵥ p₃)) : (∡ p₁ p₅ p₂).sign = (∡ p₃ p₅ p₄).sign :=
  by
  by_cases hc₅₁₂ : Collinear ℝ ({p₅, p₁, p₂} : Set P)
  · have hc₅₁₂₃₄ : Collinear ℝ ({p₅, p₁, p₂, p₃, p₄} : Set P) :=
      (hc.collinear_insert_iff_of_ne (Set.mem_insert _ _)
            (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) hp₁p₂).2
        hc₅₁₂
    have hc₅₃₄ : Collinear ℝ ({p₅, p₃, p₄} : Set P) :=
      (hc.collinear_insert_iff_of_ne
            (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
            (Set.mem_insert_of_mem _
              (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
            hp₃p₄).1
        hc₅₁₂₃₄
    rw [Set.insert_comm] at hc₅₁₂ hc₅₃₄
    have hs₁₅₂ := oangle_eq_zero_or_eq_pi_iff_collinear.2 hc₅₁₂
    have hs₃₅₄ := oangle_eq_zero_or_eq_pi_iff_collinear.2 hc₅₃₄
    rw [← Real.Angle.sign_eq_zero_iff] at hs₁₅₂ hs₃₅₄
    rw [hs₁₅₂, hs₃₅₄]
  · let s : Set (P × P × P) :=
      (fun x : line[ℝ, p₁, p₂] × V => (x.1, p₅, x.2 +ᵥ x.1)) ''
        Set.univ ×ˢ { v | SameRay ℝ (p₂ -ᵥ p₁) v ∧ v ≠ 0 }
    have hco : IsConnected s :=
      haveI : ConnectedSpace line[ℝ, p₁, p₂] := AddTorsor.connected_space _ _
      (is_connected_univ.prod
            (is_connected_set_of_same_ray_and_ne_zero (vsub_ne_zero.2 hp₁p₂.symm))).image
        _
        (continuous_fst.subtype_coe.prod_mk
            (continuous_const.prod_mk
              (continuous_snd.vadd continuous_fst.subtype_coe))).ContinuousOn
    have hf : ContinuousOn (fun p : P × P × P => ∡ p.1 p.2.1 p.2.2) s :=
      by
      refine' ContinuousAt.continuous_on fun p hp => continuous_at_oangle _ _
      all_goals
        simp_rw [s, Set.mem_image, Set.mem_prod, Set.mem_univ, true_and_iff, Prod.ext_iff] at hp
        obtain ⟨q₁, q₅, q₂⟩ := p
        dsimp only at hp⊢
        obtain ⟨⟨⟨q, hq⟩, v⟩, hv, rfl, rfl, rfl⟩ := hp
        dsimp only [Subtype.coe_mk, Set.mem_setOf] at hv⊢
        obtain ⟨hvr, -⟩ := hv
        rintro rfl
        refine' hc₅₁₂ ((collinear_insert_iff_of_mem_affine_span _).2 (collinear_pair _ _ _))
      · exact hq
      · refine' vadd_mem_of_mem_direction _ hq
        rw [← exists_nonneg_left_iff_same_ray (vsub_ne_zero.2 hp₁p₂.symm)] at hvr
        obtain ⟨r, -, rfl⟩ := hvr
        rw [direction_affine_span]
        exact smul_vsub_rev_mem_vector_span_pair _ _ _
    have hsp : ∀ p : P × P × P, p ∈ s → ∡ p.1 p.2.1 p.2.2 ≠ 0 ∧ ∡ p.1 p.2.1 p.2.2 ≠ π :=
      by
      intro p hp
      simp_rw [s, Set.mem_image, Set.mem_prod, Set.mem_setOf, Set.mem_univ, true_and_iff,
        Prod.ext_iff] at hp
      obtain ⟨q₁, q₅, q₂⟩ := p
      dsimp only at hp⊢
      obtain ⟨⟨⟨q, hq⟩, v⟩, hv, rfl, rfl, rfl⟩ := hp
      dsimp only [Subtype.coe_mk, Set.mem_setOf] at hv⊢
      obtain ⟨hvr, hv0⟩ := hv
      rw [← exists_nonneg_left_iff_same_ray (vsub_ne_zero.2 hp₁p₂.symm)] at hvr
      obtain ⟨r, -, rfl⟩ := hvr
      change q ∈ line[ℝ, p₁, p₂] at hq
      rw [oangle_ne_zero_and_ne_pi_iff_affine_independent]
      refine'
        affine_independent_of_ne_of_mem_of_not_mem_of_mem _ hq
          (fun h => hc₅₁₂ ((collinear_insert_iff_of_mem_affine_span h).2 (collinear_pair _ _ _))) _
      · rwa [← @vsub_ne_zero V, vsub_vadd_eq_vsub_sub, vsub_self, zero_sub, neg_ne_zero]
      · refine' vadd_mem_of_mem_direction _ hq
        rw [direction_affine_span]
        exact smul_vsub_rev_mem_vector_span_pair _ _ _
    have hp₁p₂s : (p₁, p₅, p₂) ∈ s :=
      by
      simp_rw [s, Set.mem_image, Set.mem_prod, Set.mem_setOf, Set.mem_univ, true_and_iff,
        Prod.ext_iff]
      refine'
        ⟨⟨⟨p₁, left_mem_affine_span_pair _ _ _⟩, p₂ -ᵥ p₁⟩,
          ⟨SameRay.rfl, vsub_ne_zero.2 hp₁p₂.symm⟩, _⟩
      simp
    have hp₃p₄s : (p₃, p₅, p₄) ∈ s :=
      by
      simp_rw [s, Set.mem_image, Set.mem_prod, Set.mem_setOf, Set.mem_univ, true_and_iff,
        Prod.ext_iff]
      refine'
        ⟨⟨⟨p₃,
              hc.mem_affine_span_of_mem_of_ne (Set.mem_insert _ _)
                (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
                (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) hp₁p₂⟩,
            p₄ -ᵥ p₃⟩,
          ⟨hr, vsub_ne_zero.2 hp₃p₄.symm⟩, _⟩
      simp
    convert Real.Angle.sign_eq_of_continuous_on hco hf hsp hp₃p₄s hp₁p₂s
#align collinear.oangle_sign_of_same_ray_vsub Collinear.oangle_sign_of_same_ray_vsub

/-- Given three points in strict order on the same line, and a fourth point, the angles at the
fourth point between the first and second or second and third points have the same sign. -/
theorem Sbtw.oangle_sign_eq {p₁ p₂ p₃ : P} (p₄ : P) (h : Sbtw ℝ p₁ p₂ p₃) :
    (∡ p₁ p₄ p₂).sign = (∡ p₂ p₄ p₃).sign :=
  haveI hc : Collinear ℝ ({p₁, p₂, p₂, p₃} : Set P) := by simpa using h.wbtw.collinear
  hc.oangle_sign_of_same_ray_vsub _ h.left_ne h.ne_right h.wbtw.same_ray_vsub
#align sbtw.oangle_sign_eq Sbtw.oangle_sign_eq

/-- Given three points in weak order on the same line, with the first not equal to the second,
and a fourth point, the angles at the fourth point between the first and second or first and
third points have the same sign. -/
theorem Wbtw.oangle_sign_eq_of_ne_left {p₁ p₂ p₃ : P} (p₄ : P) (h : Wbtw ℝ p₁ p₂ p₃)
    (hne : p₁ ≠ p₂) : (∡ p₁ p₄ p₂).sign = (∡ p₁ p₄ p₃).sign :=
  haveI hc : Collinear ℝ ({p₁, p₂, p₁, p₃} : Set P) := by
    simpa [Set.insert_comm p₂] using h.collinear
  hc.oangle_sign_of_same_ray_vsub _ hne (h.left_ne_right_of_ne_left hne.symm) h.same_ray_vsub_left
#align wbtw.oangle_sign_eq_of_ne_left Wbtw.oangle_sign_eq_of_ne_left

/-- Given three points in strict order on the same line, and a fourth point, the angles at the
fourth point between the first and second or first and third points have the same sign. -/
theorem Sbtw.oangle_sign_eq_left {p₁ p₂ p₃ : P} (p₄ : P) (h : Sbtw ℝ p₁ p₂ p₃) :
    (∡ p₁ p₄ p₂).sign = (∡ p₁ p₄ p₃).sign :=
  h.Wbtw.oangle_sign_eq_of_ne_left _ h.left_ne
#align sbtw.oangle_sign_eq_left Sbtw.oangle_sign_eq_left

/-- Given three points in weak order on the same line, with the second not equal to the third,
and a fourth point, the angles at the fourth point between the second and third or first and
third points have the same sign. -/
theorem Wbtw.oangle_sign_eq_of_ne_right {p₁ p₂ p₃ : P} (p₄ : P) (h : Wbtw ℝ p₁ p₂ p₃)
    (hne : p₂ ≠ p₃) : (∡ p₂ p₄ p₃).sign = (∡ p₁ p₄ p₃).sign := by
  simp_rw [oangle_rev p₃, Real.Angle.sign_neg, h.symm.oangle_sign_eq_of_ne_left _ hne.symm]
#align wbtw.oangle_sign_eq_of_ne_right Wbtw.oangle_sign_eq_of_ne_right

/-- Given three points in strict order on the same line, and a fourth point, the angles at the
fourth point between the second and third or first and third points have the same sign. -/
theorem Sbtw.oangle_sign_eq_right {p₁ p₂ p₃ : P} (p₄ : P) (h : Sbtw ℝ p₁ p₂ p₃) :
    (∡ p₂ p₄ p₃).sign = (∡ p₁ p₄ p₃).sign :=
  h.Wbtw.oangle_sign_eq_of_ne_right _ h.ne_right
#align sbtw.oangle_sign_eq_right Sbtw.oangle_sign_eq_right

/-- Given two points in an affine subspace, the angles between those two points at two other
points on the same side of that subspace have the same sign. -/
theorem AffineSubspace.SSameSide.oangle_sign_eq {s : AffineSubspace ℝ P} {p₁ p₂ p₃ p₄ : P}
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₃p₄ : s.SSameSide p₃ p₄) :
    (∡ p₁ p₄ p₂).sign = (∡ p₁ p₃ p₂).sign :=
  by
  by_cases h : p₁ = p₂
  · simp [h]
  let sp : Set (P × P × P) := (fun p : P => (p₁, p, p₂)) '' { p | s.s_same_side p₃ p }
  have hc : IsConnected sp :=
    (is_connected_set_of_s_same_side hp₃p₄.2.1 hp₃p₄.nonempty).image _
      (continuous_const.prod_mk (Continuous.Prod.mk_left _)).ContinuousOn
  have hf : ContinuousOn (fun p : P × P × P => ∡ p.1 p.2.1 p.2.2) sp :=
    by
    refine' ContinuousAt.continuous_on fun p hp => continuous_at_oangle _ _
    all_goals
      simp_rw [sp, Set.mem_image, Set.mem_setOf] at hp
      obtain ⟨p', hp', rfl⟩ := hp
      dsimp only
      rintro rfl
    · exact hp'.2.2 hp₁
    · exact hp'.2.2 hp₂
  have hsp : ∀ p : P × P × P, p ∈ sp → ∡ p.1 p.2.1 p.2.2 ≠ 0 ∧ ∡ p.1 p.2.1 p.2.2 ≠ π :=
    by
    intro p hp
    simp_rw [sp, Set.mem_image, Set.mem_setOf] at hp
    obtain ⟨p', hp', rfl⟩ := hp
    dsimp only
    rw [oangle_ne_zero_and_ne_pi_iff_affine_independent]
    exact affine_independent_of_ne_of_mem_of_not_mem_of_mem h hp₁ hp'.2.2 hp₂
  have hp₃ : (p₁, p₃, p₂) ∈ sp :=
    Set.mem_image_of_mem _ (s_same_side_self_iff.2 ⟨hp₃p₄.nonempty, hp₃p₄.2.1⟩)
  have hp₄ : (p₁, p₄, p₂) ∈ sp := Set.mem_image_of_mem _ hp₃p₄
  convert Real.Angle.sign_eq_of_continuous_on hc hf hsp hp₃ hp₄
#align affine_subspace.s_same_side.oangle_sign_eq AffineSubspace.SSameSide.oangle_sign_eq

/-- Given two points in an affine subspace, the angles between those two points at two other
points on opposite sides of that subspace have opposite signs. -/
theorem AffineSubspace.SOppSide.oangle_sign_eq_neg {s : AffineSubspace ℝ P} {p₁ p₂ p₃ p₄ : P}
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₃p₄ : s.SOppSide p₃ p₄) :
    (∡ p₁ p₄ p₂).sign = -(∡ p₁ p₃ p₂).sign :=
  by
  have hp₁p₃ : p₁ ≠ p₃ := by
    rintro rfl
    exact hp₃p₄.left_not_mem hp₁
  rw [←
    (hp₃p₄.symm.trans (s_opp_side_point_reflection hp₁ hp₃p₄.left_not_mem)).oangle_sign_eq hp₁ hp₂,
    ← oangle_rotate_sign p₁, ← oangle_rotate_sign p₁, oangle_swap₁₃_sign,
    (sbtw_point_reflection_of_ne ℝ hp₁p₃).symm.oangle_sign_eq _]
#align affine_subspace.s_opp_side.oangle_sign_eq_neg AffineSubspace.SOppSide.oangle_sign_eq_neg

end EuclideanGeometry

