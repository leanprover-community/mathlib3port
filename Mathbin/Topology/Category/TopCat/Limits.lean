/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison, Mario Carneiro, Andrew Yang

! This file was ported from Lean 3 source module topology.category.Top.limits
! leanprover-community/mathlib commit 6d0adfa76594f304b4650d098273d4366edeb61b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Category.TopCat.EpiMono
import Mathbin.CategoryTheory.Category.Ulift
import Mathbin.CategoryTheory.Limits.ConcreteCategory
import Mathbin.CategoryTheory.ConcreteCategory.Elementwise

/-!
# The category of topological spaces has all limits and colimits

Further, these limits and colimits are preserved by the forgetful functor --- that is, the
underlying types are just the limits in the category of types.
-/


open TopologicalSpace

open CategoryTheory

open CategoryTheory.Limits

open Opposite

universe u v w

noncomputable section

namespace TopCat

variable {J : Type v} [SmallCategory J]

-- mathport name: exprforget
local notation "forget" => forget TopCat

/-- A choice of limit cone for a functor `F : J ⥤ Top`.
Generally you should just use `limit.cone F`, unless you need the actual definition
(which is in terms of `types.limit_cone`).
-/
def limitCone (F : J ⥤ TopCat.{max v u}) : Cone F
    where
  x := TopCat.of { u : ∀ j : J, F.obj j | ∀ {i j : J} (f : i ⟶ j), F.map f (u i) = u j }
  π :=
    {
      app := fun j =>
        { toFun := fun u => u.val j
          continuous_to_fun :=
            show Continuous ((fun u : ∀ j : J, F.obj j => u j) ∘ Subtype.val) by continuity } }
#align Top.limit_cone TopCat.limitCone

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "A choice of limit cone for a functor `F : J ⥤ Top` whose topology is defined as an\ninfimum of topologies infimum.\nGenerally you should just use `limit.cone F`, unless you need the actual definition\n(which is in terms of `types.limit_cone`).\n-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `limitConeInfi [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`F]
         [":"
          (CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
           `J
           " ⥤ "
           (Term.explicitUniv `TopCat ".{" [(Level.max "max" [`v `u])] "}"))]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `Cone [`F]))])
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `x
           []
           []
           ":="
           (Term.anonymousCtor
            "⟨"
            [(Term.proj
              (Term.app
               `Types.limitCone
               [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
                 `F
                 " ⋙ "
                 (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))])
              "."
              `x)
             ","
             (Order.CompleteLattice.«term⨅_,_»
              "⨅"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
              ", "
              (Term.app
               (Term.proj (Term.proj (Term.app (Term.proj `F "." `obj) [`j]) "." `str) "." `induced)
               [(Term.app
                 (Term.proj
                  (Term.proj
                   (Term.app
                    `Types.limitCone
                    [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
                      `F
                      " ⋙ "
                      (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))])
                   "."
                   `π)
                  "."
                  `app)
                 [`j])]))]
            "⟩"))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `π
           []
           []
           ":="
           (Term.structInst
            "{"
            []
            [(Term.structInstField
              (Term.structInstLVal `app [])
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`j]
                []
                "=>"
                (Term.anonymousCtor
                 "⟨"
                 [(Term.app
                   (Term.proj
                    (Term.proj
                     (Term.app
                      `Types.limitCone
                      [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
                        `F
                        " ⋙ "
                        (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))])
                     "."
                     `π)
                    "."
                    `app)
                   [`j])
                  ","
                  (Term.app
                   (Term.proj `continuous_iff_le_induced "." `mpr)
                   [(Term.app `infᵢ_le [(Term.hole "_") (Term.hole "_")])])]
                 "⟩"))))
             []
             (Term.structInstField
              (Term.structInstLVal `naturality' [])
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`j `j' `f]
                []
                "=>"
                (Term.app
                 `ContinuousMap.coe_injective
                 [(Term.app
                   (Term.proj
                    (Term.proj
                     (Term.app
                      `Types.limitCone
                      [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
                        `F
                        " ⋙ "
                        (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))])
                     "."
                     `π)
                    "."
                    `naturality)
                   [`f])]))))]
            (Term.optEllipsis [])
            []
            "}"))))]
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       []
       [(Term.structInstField
         (Term.structInstLVal `app [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`j]
           []
           "=>"
           (Term.anonymousCtor
            "⟨"
            [(Term.app
              (Term.proj
               (Term.proj
                (Term.app
                 `Types.limitCone
                 [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
                   `F
                   " ⋙ "
                   (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))])
                "."
                `π)
               "."
               `app)
              [`j])
             ","
             (Term.app
              (Term.proj `continuous_iff_le_induced "." `mpr)
              [(Term.app `infᵢ_le [(Term.hole "_") (Term.hole "_")])])]
            "⟩"))))
        []
        (Term.structInstField
         (Term.structInstLVal `naturality' [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`j `j' `f]
           []
           "=>"
           (Term.app
            `ContinuousMap.coe_injective
            [(Term.app
              (Term.proj
               (Term.proj
                (Term.app
                 `Types.limitCone
                 [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
                   `F
                   " ⋙ "
                   (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))])
                "."
                `π)
               "."
               `naturality)
              [`f])]))))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`j `j' `f]
        []
        "=>"
        (Term.app
         `ContinuousMap.coe_injective
         [(Term.app
           (Term.proj
            (Term.proj
             (Term.app
              `Types.limitCone
              [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
                `F
                " ⋙ "
                (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))])
             "."
             `π)
            "."
            `naturality)
           [`f])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `ContinuousMap.coe_injective
       [(Term.app
         (Term.proj
          (Term.proj
           (Term.app
            `Types.limitCone
            [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
              `F
              " ⋙ "
              (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))])
           "."
           `π)
          "."
          `naturality)
         [`f])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.proj
         (Term.app
          `Types.limitCone
          [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
            `F
            " ⋙ "
            (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))])
         "."
         `π)
        "."
        `naturality)
       [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.proj
        (Term.app
         `Types.limitCone
         [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
           `F
           " ⋙ "
           (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))])
        "."
        `π)
       "."
       `naturality)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.app
        `Types.limitCone
        [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
          `F
          " ⋙ "
          (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))])
       "."
       `π)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `Types.limitCone
       [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
         `F
         " ⋙ "
         (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
       `F
       " ⋙ "
       (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (TopCat.Topology.Category.TopCat.Limits.termforget "forget")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'TopCat.Topology.Category.TopCat.Limits.termforget', expected 'TopCat.Topology.Category.TopCat.Limits.termforget._@.Topology.Category.TopCat.Limits._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
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
/--
    A choice of limit cone for a functor `F : J ⥤ Top` whose topology is defined as an
    infimum of topologies infimum.
    Generally you should just use `limit.cone F`, unless you need the actual definition
    (which is in terms of `types.limit_cone`).
    -/
  def
    limitConeInfi
    ( F : J ⥤ TopCat .{ max v u } ) : Cone F
    where
      x
          :=
          ⟨
            Types.limitCone F ⋙ forget . x
              ,
              ⨅ j , F . obj j . str . induced Types.limitCone F ⋙ forget . π . app j
            ⟩
        π
          :=
          {
            app
                :=
                fun
                  j
                    =>
                    ⟨
                      Types.limitCone F ⋙ forget . π . app j
                        ,
                        continuous_iff_le_induced . mpr infᵢ_le _ _
                      ⟩
              naturality'
                :=
                fun
                  j j' f
                    =>
                    ContinuousMap.coe_injective Types.limitCone F ⋙ forget . π . naturality f
            }
#align Top.limit_cone_infi TopCat.limitConeInfi

/-- The chosen cone `Top.limit_cone F` for a functor `F : J ⥤ Top` is a limit cone.
Generally you should just use `limit.is_limit F`, unless you need the actual definition
(which is in terms of `types.limit_cone_is_limit`).
-/
def limitConeIsLimit (F : J ⥤ TopCat.{max v u}) : IsLimit (limitCone F)
    where
  lift S :=
    {
      toFun := fun x =>
        ⟨fun j => S.π.app _ x, fun i j f => by
          dsimp
          erw [← S.w f]
          rfl⟩ }
  uniq' S m h := by
    ext : 3
    simpa [← h]
#align Top.limit_cone_is_limit TopCat.limitConeIsLimit

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The chosen cone `Top.limit_cone_infi F` for a functor `F : J ⥤ Top` is a limit cone.\nGenerally you should just use `limit.is_limit F`, unless you need the actual definition\n(which is in terms of `types.limit_cone_is_limit`).\n-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `limitConeInfiIsLimit [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`F]
         [":"
          (CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
           `J
           " ⥤ "
           (Term.explicitUniv `TopCat ".{" [(Level.max "max" [`v `u])] "}"))]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `IsLimit [(Term.app `limitConeInfi [`F])]))])
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.app
             `is_limit.of_faithful
             [(TopCat.Topology.Category.TopCat.Limits.termforget "forget")
              (Term.app `types.limit_cone_is_limit [(Term.hole "_")])
              (Term.fun
               "fun"
               (Term.basicFun
                [`s]
                []
                "=>"
                (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")))
              (Term.fun "fun" (Term.basicFun [`s] [] "=>" `rfl))]))
           []
           (Tactic.exact
            "exact"
            (Term.app
             `continuous_iff_coinduced_le.mpr
             [(Term.app
               `le_infᵢ
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [`j]
                  []
                  "=>"
                  («term_<|_»
                   `coinduced_le_iff_le_induced.mp
                   "<|"
                   (Term.typeAscription
                    "("
                    (Term.app
                     `continuous_iff_coinduced_le.mp
                     [(Term.proj (Term.app `s.π.app [`j]) "." `Continuous)])
                    ":"
                    [(Term.hole "_")]
                    ")"))))])]))])))
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
            `is_limit.of_faithful
            [(TopCat.Topology.Category.TopCat.Limits.termforget "forget")
             (Term.app `types.limit_cone_is_limit [(Term.hole "_")])
             (Term.fun
              "fun"
              (Term.basicFun
               [`s]
               []
               "=>"
               (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")))
             (Term.fun "fun" (Term.basicFun [`s] [] "=>" `rfl))]))
          []
          (Tactic.exact
           "exact"
           (Term.app
            `continuous_iff_coinduced_le.mpr
            [(Term.app
              `le_infᵢ
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`j]
                 []
                 "=>"
                 («term_<|_»
                  `coinduced_le_iff_le_induced.mp
                  "<|"
                  (Term.typeAscription
                   "("
                   (Term.app
                    `continuous_iff_coinduced_le.mp
                    [(Term.proj (Term.app `s.π.app [`j]) "." `Continuous)])
                   ":"
                   [(Term.hole "_")]
                   ")"))))])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `continuous_iff_coinduced_le.mpr
        [(Term.app
          `le_infᵢ
          [(Term.fun
            "fun"
            (Term.basicFun
             [`j]
             []
             "=>"
             («term_<|_»
              `coinduced_le_iff_le_induced.mp
              "<|"
              (Term.typeAscription
               "("
               (Term.app
                `continuous_iff_coinduced_le.mp
                [(Term.proj (Term.app `s.π.app [`j]) "." `Continuous)])
               ":"
               [(Term.hole "_")]
               ")"))))])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `continuous_iff_coinduced_le.mpr
       [(Term.app
         `le_infᵢ
         [(Term.fun
           "fun"
           (Term.basicFun
            [`j]
            []
            "=>"
            («term_<|_»
             `coinduced_le_iff_le_induced.mp
             "<|"
             (Term.typeAscription
              "("
              (Term.app
               `continuous_iff_coinduced_le.mp
               [(Term.proj (Term.app `s.π.app [`j]) "." `Continuous)])
              ":"
              [(Term.hole "_")]
              ")"))))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le_infᵢ
       [(Term.fun
         "fun"
         (Term.basicFun
          [`j]
          []
          "=>"
          («term_<|_»
           `coinduced_le_iff_le_induced.mp
           "<|"
           (Term.typeAscription
            "("
            (Term.app
             `continuous_iff_coinduced_le.mp
             [(Term.proj (Term.app `s.π.app [`j]) "." `Continuous)])
            ":"
            [(Term.hole "_")]
            ")"))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`j]
        []
        "=>"
        («term_<|_»
         `coinduced_le_iff_le_induced.mp
         "<|"
         (Term.typeAscription
          "("
          (Term.app
           `continuous_iff_coinduced_le.mp
           [(Term.proj (Term.app `s.π.app [`j]) "." `Continuous)])
          ":"
          [(Term.hole "_")]
          ")"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       `coinduced_le_iff_le_induced.mp
       "<|"
       (Term.typeAscription
        "("
        (Term.app
         `continuous_iff_coinduced_le.mp
         [(Term.proj (Term.app `s.π.app [`j]) "." `Continuous)])
        ":"
        [(Term.hole "_")]
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.app
        `continuous_iff_coinduced_le.mp
        [(Term.proj (Term.app `s.π.app [`j]) "." `Continuous)])
       ":"
       [(Term.hole "_")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `continuous_iff_coinduced_le.mp
       [(Term.proj (Term.app `s.π.app [`j]) "." `Continuous)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `s.π.app [`j]) "." `Continuous)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `s.π.app [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `s.π.app
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `s.π.app [`j]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `continuous_iff_coinduced_le.mp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `coinduced_le_iff_le_induced.mp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_infᵢ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `le_infᵢ
      [(Term.fun
        "fun"
        (Term.basicFun
         [`j]
         []
         "=>"
         («term_<|_»
          `coinduced_le_iff_le_induced.mp
          "<|"
          (Term.typeAscription
           "("
           (Term.app
            `continuous_iff_coinduced_le.mp
            [(Term.proj (Term.paren "(" (Term.app `s.π.app [`j]) ")") "." `Continuous)])
           ":"
           [(Term.hole "_")]
           ")"))))])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `continuous_iff_coinduced_le.mpr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `is_limit.of_faithful
        [(TopCat.Topology.Category.TopCat.Limits.termforget "forget")
         (Term.app `types.limit_cone_is_limit [(Term.hole "_")])
         (Term.fun
          "fun"
          (Term.basicFun
           [`s]
           []
           "=>"
           (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")))
         (Term.fun "fun" (Term.basicFun [`s] [] "=>" `rfl))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `is_limit.of_faithful
       [(TopCat.Topology.Category.TopCat.Limits.termforget "forget")
        (Term.app `types.limit_cone_is_limit [(Term.hole "_")])
        (Term.fun
         "fun"
         (Term.basicFun
          [`s]
          []
          "=>"
          (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")))
        (Term.fun "fun" (Term.basicFun [`s] [] "=>" `rfl))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`s] [] "=>" `rfl))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`s]
        []
        "=>"
        (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`s]
       []
       "=>"
       (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `types.limit_cone_is_limit [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `types.limit_cone_is_limit
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `types.limit_cone_is_limit [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'TopCat.Topology.Category.TopCat.Limits.termforget', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'TopCat.Topology.Category.TopCat.Limits.termforget', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (TopCat.Topology.Category.TopCat.Limits.termforget "forget")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'TopCat.Topology.Category.TopCat.Limits.termforget', expected 'TopCat.Topology.Category.TopCat.Limits.termforget._@.Topology.Category.TopCat.Limits._hyg.10'
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
    The chosen cone `Top.limit_cone_infi F` for a functor `F : J ⥤ Top` is a limit cone.
    Generally you should just use `limit.is_limit F`, unless you need the actual definition
    (which is in terms of `types.limit_cone_is_limit`).
    -/
  def
    limitConeInfiIsLimit
    ( F : J ⥤ TopCat .{ max v u } ) : IsLimit limitConeInfi F
    :=
      by
        refine'
            is_limit.of_faithful forget types.limit_cone_is_limit _ fun s => ⟨ _ , _ ⟩ fun s => rfl
          exact
            continuous_iff_coinduced_le.mpr
              le_infᵢ
                fun
                  j
                    =>
                    coinduced_le_iff_le_induced.mp
                      <|
                      ( continuous_iff_coinduced_le.mp s.π.app j . Continuous : _ )
#align Top.limit_cone_infi_is_limit TopCat.limitConeInfiIsLimit

instance topHasLimitsOfSize : HasLimitsOfSize.{v} TopCat.{max v u}
    where HasLimitsOfShape J 𝒥 :=
    {
      HasLimit := fun F =>
        has_limit.mk
          { Cone := limit_cone F
            IsLimit := limit_cone_is_limit F } }
#align Top.Top_has_limits_of_size TopCat.topHasLimitsOfSize

instance Top_has_limits : HasLimits TopCat.{u} :=
  TopCat.topHasLimitsOfSize.{u, u}
#align Top.Top_has_limits TopCat.Top_has_limits

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `forgetPreservesLimitsOfSize [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         (Term.explicitUniv `PreservesLimitsOfSize ".{" [`v "," `v] "}")
         [(Term.typeAscription
           "("
           (TopCat.Topology.Category.TopCat.Limits.termforget "forget")
           ":"
           [(CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
             (Term.explicitUniv `TopCat ".{" [(Level.max "max" [`v `u])] "}")
             " ⥤ "
             (Term.type "Type" [(Level.max "max" [`v `u])]))]
           ")")])))
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `PreservesLimitsOfShape
           [`J `𝒥]
           []
           ":="
           (Term.structInst
            "{"
            []
            [(Term.structInstField
              (Term.structInstLVal `PreservesLimit [])
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`F]
                []
                "=>"
                (Term.app
                 `preserves_limit_of_preserves_limit_cone
                 [(Term.app `limit_cone_is_limit [`F])
                  (Term.app
                   `types.limit_cone_is_limit
                   [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
                     `F
                     " ⋙ "
                     (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))])]))))]
            (Term.optEllipsis [])
            []
            "}"))))]
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
      (Term.structInst
       "{"
       []
       [(Term.structInstField
         (Term.structInstLVal `PreservesLimit [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`F]
           []
           "=>"
           (Term.app
            `preserves_limit_of_preserves_limit_cone
            [(Term.app `limit_cone_is_limit [`F])
             (Term.app
              `types.limit_cone_is_limit
              [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
                `F
                " ⋙ "
                (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))])]))))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`F]
        []
        "=>"
        (Term.app
         `preserves_limit_of_preserves_limit_cone
         [(Term.app `limit_cone_is_limit [`F])
          (Term.app
           `types.limit_cone_is_limit
           [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
             `F
             " ⋙ "
             (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `preserves_limit_of_preserves_limit_cone
       [(Term.app `limit_cone_is_limit [`F])
        (Term.app
         `types.limit_cone_is_limit
         [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
           `F
           " ⋙ "
           (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `types.limit_cone_is_limit
       [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
         `F
         " ⋙ "
         (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
       `F
       " ⋙ "
       (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (TopCat.Topology.Category.TopCat.Limits.termforget "forget")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'TopCat.Topology.Category.TopCat.Limits.termforget', expected 'TopCat.Topology.Category.TopCat.Limits.termforget._@.Topology.Category.TopCat.Limits._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  forgetPreservesLimitsOfSize
  : PreservesLimitsOfSize .{ v , v } ( forget : TopCat .{ max v u } ⥤ Type max v u )
  where
    PreservesLimitsOfShape
      J 𝒥
      :=
      {
        PreservesLimit
          :=
          fun
            F
              =>
              preserves_limit_of_preserves_limit_cone
                limit_cone_is_limit F types.limit_cone_is_limit F ⋙ forget
        }
#align Top.forget_preserves_limits_of_size TopCat.forgetPreservesLimitsOfSize

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `forgetPreservesLimits [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `PreservesLimits
         [(Term.typeAscription
           "("
           (TopCat.Topology.Category.TopCat.Limits.termforget "forget")
           ":"
           [(CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
             (Term.explicitUniv `TopCat ".{" [`u] "}")
             " ⥤ "
             (Term.type "Type" [`u]))]
           ")")])))
      (Command.declValSimple
       ":="
       (Term.explicitUniv `TopCat.forgetPreservesLimitsOfSize ".{" [`u "," `u] "}")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.explicitUniv `TopCat.forgetPreservesLimitsOfSize ".{" [`u "," `u] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `TopCat.forgetPreservesLimitsOfSize
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `PreservesLimits
       [(Term.typeAscription
         "("
         (TopCat.Topology.Category.TopCat.Limits.termforget "forget")
         ":"
         [(CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
           (Term.explicitUniv `TopCat ".{" [`u] "}")
           " ⥤ "
           (Term.type "Type" [`u]))]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (TopCat.Topology.Category.TopCat.Limits.termforget "forget")
       ":"
       [(CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
         (Term.explicitUniv `TopCat ".{" [`u] "}")
         " ⥤ "
         (Term.type "Type" [`u]))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
       (Term.explicitUniv `TopCat ".{" [`u] "}")
       " ⥤ "
       (Term.type "Type" [`u]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.type "Type" [`u])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 26 >? 1022, (some 1024,
     level) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 26, term))
      (Term.explicitUniv `TopCat ".{" [`u] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `TopCat
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 27 >? 1024, (none, [anonymous]) <=? (some 26, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 26, (some 26, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (TopCat.Topology.Category.TopCat.Limits.termforget "forget")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'TopCat.Topology.Category.TopCat.Limits.termforget', expected 'TopCat.Topology.Category.TopCat.Limits.termforget._@.Topology.Category.TopCat.Limits._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  forgetPreservesLimits
  : PreservesLimits ( forget : TopCat .{ u } ⥤ Type u )
  := TopCat.forgetPreservesLimitsOfSize .{ u , u }
#align Top.forget_preserves_limits TopCat.forgetPreservesLimits

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "A choice of colimit cocone for a functor `F : J ⥤ Top`.\nGenerally you should just use `colimit.coone F`, unless you need the actual definition\n(which is in terms of `types.colimit_cocone`).\n-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `colimitCocone [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`F]
         [":"
          (CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
           `J
           " ⥤ "
           (Term.explicitUniv `TopCat ".{" [(Level.max "max" [`v `u])] "}"))]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `Cocone [`F]))])
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `x
           []
           []
           ":="
           (Term.anonymousCtor
            "⟨"
            [(Term.proj
              (Term.app
               `Types.colimitCocone
               [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
                 `F
                 " ⋙ "
                 (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))])
              "."
              `x)
             ","
             (Order.CompleteLattice.«term⨆_,_»
              "⨆"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
              ", "
              (Term.app
               (Term.proj
                (Term.proj (Term.app (Term.proj `F "." `obj) [`j]) "." `str)
                "."
                `coinduced)
               [(Term.app
                 (Term.proj
                  (Term.proj
                   (Term.app
                    `Types.colimitCocone
                    [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
                      `F
                      " ⋙ "
                      (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))])
                   "."
                   `ι)
                  "."
                  `app)
                 [`j])]))]
            "⟩"))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `ι
           []
           []
           ":="
           (Term.structInst
            "{"
            []
            [(Term.structInstField
              (Term.structInstLVal `app [])
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`j]
                []
                "=>"
                (Term.anonymousCtor
                 "⟨"
                 [(Term.app
                   (Term.proj
                    (Term.proj
                     (Term.app
                      `Types.colimitCocone
                      [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
                        `F
                        " ⋙ "
                        (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))])
                     "."
                     `ι)
                    "."
                    `app)
                   [`j])
                  ","
                  (Term.app
                   (Term.proj `continuous_iff_coinduced_le "." `mpr)
                   [(Term.app `le_supᵢ [(Term.hole "_") `j])])]
                 "⟩"))))
             []
             (Term.structInstField
              (Term.structInstLVal `naturality' [])
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`j `j' `f]
                []
                "=>"
                (Term.app
                 `ContinuousMap.coe_injective
                 [(Term.app
                   (Term.proj
                    (Term.proj
                     (Term.app
                      `Types.colimitCocone
                      [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
                        `F
                        " ⋙ "
                        (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))])
                     "."
                     `ι)
                    "."
                    `naturality)
                   [`f])]))))]
            (Term.optEllipsis [])
            []
            "}"))))]
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       []
       [(Term.structInstField
         (Term.structInstLVal `app [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`j]
           []
           "=>"
           (Term.anonymousCtor
            "⟨"
            [(Term.app
              (Term.proj
               (Term.proj
                (Term.app
                 `Types.colimitCocone
                 [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
                   `F
                   " ⋙ "
                   (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))])
                "."
                `ι)
               "."
               `app)
              [`j])
             ","
             (Term.app
              (Term.proj `continuous_iff_coinduced_le "." `mpr)
              [(Term.app `le_supᵢ [(Term.hole "_") `j])])]
            "⟩"))))
        []
        (Term.structInstField
         (Term.structInstLVal `naturality' [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`j `j' `f]
           []
           "=>"
           (Term.app
            `ContinuousMap.coe_injective
            [(Term.app
              (Term.proj
               (Term.proj
                (Term.app
                 `Types.colimitCocone
                 [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
                   `F
                   " ⋙ "
                   (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))])
                "."
                `ι)
               "."
               `naturality)
              [`f])]))))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`j `j' `f]
        []
        "=>"
        (Term.app
         `ContinuousMap.coe_injective
         [(Term.app
           (Term.proj
            (Term.proj
             (Term.app
              `Types.colimitCocone
              [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
                `F
                " ⋙ "
                (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))])
             "."
             `ι)
            "."
            `naturality)
           [`f])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `ContinuousMap.coe_injective
       [(Term.app
         (Term.proj
          (Term.proj
           (Term.app
            `Types.colimitCocone
            [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
              `F
              " ⋙ "
              (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))])
           "."
           `ι)
          "."
          `naturality)
         [`f])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.proj
         (Term.app
          `Types.colimitCocone
          [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
            `F
            " ⋙ "
            (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))])
         "."
         `ι)
        "."
        `naturality)
       [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.proj
        (Term.app
         `Types.colimitCocone
         [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
           `F
           " ⋙ "
           (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))])
        "."
        `ι)
       "."
       `naturality)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.app
        `Types.colimitCocone
        [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
          `F
          " ⋙ "
          (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))])
       "."
       `ι)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `Types.colimitCocone
       [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
         `F
         " ⋙ "
         (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
       `F
       " ⋙ "
       (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (TopCat.Topology.Category.TopCat.Limits.termforget "forget")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'TopCat.Topology.Category.TopCat.Limits.termforget', expected 'TopCat.Topology.Category.TopCat.Limits.termforget._@.Topology.Category.TopCat.Limits._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
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
/--
    A choice of colimit cocone for a functor `F : J ⥤ Top`.
    Generally you should just use `colimit.coone F`, unless you need the actual definition
    (which is in terms of `types.colimit_cocone`).
    -/
  def
    colimitCocone
    ( F : J ⥤ TopCat .{ max v u } ) : Cocone F
    where
      x
          :=
          ⟨
            Types.colimitCocone F ⋙ forget . x
              ,
              ⨆ j , F . obj j . str . coinduced Types.colimitCocone F ⋙ forget . ι . app j
            ⟩
        ι
          :=
          {
            app
                :=
                fun
                  j
                    =>
                    ⟨
                      Types.colimitCocone F ⋙ forget . ι . app j
                        ,
                        continuous_iff_coinduced_le . mpr le_supᵢ _ j
                      ⟩
              naturality'
                :=
                fun
                  j j' f
                    =>
                    ContinuousMap.coe_injective Types.colimitCocone F ⋙ forget . ι . naturality f
            }
#align Top.colimit_cocone TopCat.colimitCocone

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The chosen cocone `Top.colimit_cocone F` for a functor `F : J ⥤ Top` is a colimit cocone.\nGenerally you should just use `colimit.is_colimit F`, unless you need the actual definition\n(which is in terms of `types.colimit_cocone_is_colimit`).\n-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `colimitCoconeIsColimit [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`F]
         [":"
          (CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
           `J
           " ⥤ "
           (Term.explicitUniv `TopCat ".{" [(Level.max "max" [`v `u])] "}"))]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `IsColimit [(Term.app `colimitCocone [`F])]))])
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.app
             `is_colimit.of_faithful
             [(TopCat.Topology.Category.TopCat.Limits.termforget "forget")
              (Term.app `types.colimit_cocone_is_colimit [(Term.hole "_")])
              (Term.fun
               "fun"
               (Term.basicFun
                [`s]
                []
                "=>"
                (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")))
              (Term.fun "fun" (Term.basicFun [`s] [] "=>" `rfl))]))
           []
           (Tactic.exact
            "exact"
            (Term.app
             `continuous_iff_le_induced.mpr
             [(Term.app
               `supᵢ_le
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [`j]
                  []
                  "=>"
                  («term_<|_»
                   `coinduced_le_iff_le_induced.mp
                   "<|"
                   (Term.typeAscription
                    "("
                    (Term.app
                     `continuous_iff_coinduced_le.mp
                     [(Term.proj (Term.app `s.ι.app [`j]) "." `Continuous)])
                    ":"
                    [(Term.hole "_")]
                    ")"))))])]))])))
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
            `is_colimit.of_faithful
            [(TopCat.Topology.Category.TopCat.Limits.termforget "forget")
             (Term.app `types.colimit_cocone_is_colimit [(Term.hole "_")])
             (Term.fun
              "fun"
              (Term.basicFun
               [`s]
               []
               "=>"
               (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")))
             (Term.fun "fun" (Term.basicFun [`s] [] "=>" `rfl))]))
          []
          (Tactic.exact
           "exact"
           (Term.app
            `continuous_iff_le_induced.mpr
            [(Term.app
              `supᵢ_le
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`j]
                 []
                 "=>"
                 («term_<|_»
                  `coinduced_le_iff_le_induced.mp
                  "<|"
                  (Term.typeAscription
                   "("
                   (Term.app
                    `continuous_iff_coinduced_le.mp
                    [(Term.proj (Term.app `s.ι.app [`j]) "." `Continuous)])
                   ":"
                   [(Term.hole "_")]
                   ")"))))])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `continuous_iff_le_induced.mpr
        [(Term.app
          `supᵢ_le
          [(Term.fun
            "fun"
            (Term.basicFun
             [`j]
             []
             "=>"
             («term_<|_»
              `coinduced_le_iff_le_induced.mp
              "<|"
              (Term.typeAscription
               "("
               (Term.app
                `continuous_iff_coinduced_le.mp
                [(Term.proj (Term.app `s.ι.app [`j]) "." `Continuous)])
               ":"
               [(Term.hole "_")]
               ")"))))])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `continuous_iff_le_induced.mpr
       [(Term.app
         `supᵢ_le
         [(Term.fun
           "fun"
           (Term.basicFun
            [`j]
            []
            "=>"
            («term_<|_»
             `coinduced_le_iff_le_induced.mp
             "<|"
             (Term.typeAscription
              "("
              (Term.app
               `continuous_iff_coinduced_le.mp
               [(Term.proj (Term.app `s.ι.app [`j]) "." `Continuous)])
              ":"
              [(Term.hole "_")]
              ")"))))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `supᵢ_le
       [(Term.fun
         "fun"
         (Term.basicFun
          [`j]
          []
          "=>"
          («term_<|_»
           `coinduced_le_iff_le_induced.mp
           "<|"
           (Term.typeAscription
            "("
            (Term.app
             `continuous_iff_coinduced_le.mp
             [(Term.proj (Term.app `s.ι.app [`j]) "." `Continuous)])
            ":"
            [(Term.hole "_")]
            ")"))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`j]
        []
        "=>"
        («term_<|_»
         `coinduced_le_iff_le_induced.mp
         "<|"
         (Term.typeAscription
          "("
          (Term.app
           `continuous_iff_coinduced_le.mp
           [(Term.proj (Term.app `s.ι.app [`j]) "." `Continuous)])
          ":"
          [(Term.hole "_")]
          ")"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       `coinduced_le_iff_le_induced.mp
       "<|"
       (Term.typeAscription
        "("
        (Term.app
         `continuous_iff_coinduced_le.mp
         [(Term.proj (Term.app `s.ι.app [`j]) "." `Continuous)])
        ":"
        [(Term.hole "_")]
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.app
        `continuous_iff_coinduced_le.mp
        [(Term.proj (Term.app `s.ι.app [`j]) "." `Continuous)])
       ":"
       [(Term.hole "_")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `continuous_iff_coinduced_le.mp
       [(Term.proj (Term.app `s.ι.app [`j]) "." `Continuous)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `s.ι.app [`j]) "." `Continuous)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `s.ι.app [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `s.ι.app
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `s.ι.app [`j]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `continuous_iff_coinduced_le.mp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `coinduced_le_iff_le_induced.mp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `supᵢ_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `supᵢ_le
      [(Term.fun
        "fun"
        (Term.basicFun
         [`j]
         []
         "=>"
         («term_<|_»
          `coinduced_le_iff_le_induced.mp
          "<|"
          (Term.typeAscription
           "("
           (Term.app
            `continuous_iff_coinduced_le.mp
            [(Term.proj (Term.paren "(" (Term.app `s.ι.app [`j]) ")") "." `Continuous)])
           ":"
           [(Term.hole "_")]
           ")"))))])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `continuous_iff_le_induced.mpr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `is_colimit.of_faithful
        [(TopCat.Topology.Category.TopCat.Limits.termforget "forget")
         (Term.app `types.colimit_cocone_is_colimit [(Term.hole "_")])
         (Term.fun
          "fun"
          (Term.basicFun
           [`s]
           []
           "=>"
           (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")))
         (Term.fun "fun" (Term.basicFun [`s] [] "=>" `rfl))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `is_colimit.of_faithful
       [(TopCat.Topology.Category.TopCat.Limits.termforget "forget")
        (Term.app `types.colimit_cocone_is_colimit [(Term.hole "_")])
        (Term.fun
         "fun"
         (Term.basicFun
          [`s]
          []
          "=>"
          (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")))
        (Term.fun "fun" (Term.basicFun [`s] [] "=>" `rfl))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`s] [] "=>" `rfl))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`s]
        []
        "=>"
        (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`s]
       []
       "=>"
       (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `types.colimit_cocone_is_colimit [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `types.colimit_cocone_is_colimit
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `types.colimit_cocone_is_colimit [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'TopCat.Topology.Category.TopCat.Limits.termforget', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'TopCat.Topology.Category.TopCat.Limits.termforget', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (TopCat.Topology.Category.TopCat.Limits.termforget "forget")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'TopCat.Topology.Category.TopCat.Limits.termforget', expected 'TopCat.Topology.Category.TopCat.Limits.termforget._@.Topology.Category.TopCat.Limits._hyg.10'
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
    The chosen cocone `Top.colimit_cocone F` for a functor `F : J ⥤ Top` is a colimit cocone.
    Generally you should just use `colimit.is_colimit F`, unless you need the actual definition
    (which is in terms of `types.colimit_cocone_is_colimit`).
    -/
  def
    colimitCoconeIsColimit
    ( F : J ⥤ TopCat .{ max v u } ) : IsColimit colimitCocone F
    :=
      by
        refine'
            is_colimit.of_faithful
              forget types.colimit_cocone_is_colimit _ fun s => ⟨ _ , _ ⟩ fun s => rfl
          exact
            continuous_iff_le_induced.mpr
              supᵢ_le
                fun
                  j
                    =>
                    coinduced_le_iff_le_induced.mp
                      <|
                      ( continuous_iff_coinduced_le.mp s.ι.app j . Continuous : _ )
#align Top.colimit_cocone_is_colimit TopCat.colimitCoconeIsColimit

instance topHasColimitsOfSize : HasColimitsOfSize.{v} TopCat.{max v u}
    where HasColimitsOfShape J 𝒥 :=
    {
      HasColimit := fun F =>
        has_colimit.mk
          { Cocone := colimit_cocone F
            IsColimit := colimit_cocone_is_colimit F } }
#align Top.Top_has_colimits_of_size TopCat.topHasColimitsOfSize

instance Top_has_colimits : HasColimits TopCat.{u} :=
  TopCat.topHasColimitsOfSize.{u, u}
#align Top.Top_has_colimits TopCat.Top_has_colimits

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `forgetPreservesColimitsOfSize [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         (Term.explicitUniv `PreservesColimitsOfSize ".{" [`v "," `v] "}")
         [(Term.typeAscription
           "("
           (TopCat.Topology.Category.TopCat.Limits.termforget "forget")
           ":"
           [(CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
             (Term.explicitUniv `TopCat ".{" [(Level.max "max" [`v `u])] "}")
             " ⥤ "
             (Term.type "Type" [(Level.max "max" [`v `u])]))]
           ")")])))
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `PreservesColimitsOfShape
           [`J `𝒥]
           []
           ":="
           (Term.structInst
            "{"
            []
            [(Term.structInstField
              (Term.structInstLVal `PreservesColimit [])
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`F]
                []
                "=>"
                (Term.app
                 `preserves_colimit_of_preserves_colimit_cocone
                 [(Term.app `colimit_cocone_is_colimit [`F])
                  (Term.app
                   `types.colimit_cocone_is_colimit
                   [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
                     `F
                     " ⋙ "
                     (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))])]))))]
            (Term.optEllipsis [])
            []
            "}"))))]
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
      (Term.structInst
       "{"
       []
       [(Term.structInstField
         (Term.structInstLVal `PreservesColimit [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`F]
           []
           "=>"
           (Term.app
            `preserves_colimit_of_preserves_colimit_cocone
            [(Term.app `colimit_cocone_is_colimit [`F])
             (Term.app
              `types.colimit_cocone_is_colimit
              [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
                `F
                " ⋙ "
                (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))])]))))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`F]
        []
        "=>"
        (Term.app
         `preserves_colimit_of_preserves_colimit_cocone
         [(Term.app `colimit_cocone_is_colimit [`F])
          (Term.app
           `types.colimit_cocone_is_colimit
           [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
             `F
             " ⋙ "
             (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `preserves_colimit_of_preserves_colimit_cocone
       [(Term.app `colimit_cocone_is_colimit [`F])
        (Term.app
         `types.colimit_cocone_is_colimit
         [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
           `F
           " ⋙ "
           (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `types.colimit_cocone_is_colimit
       [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
         `F
         " ⋙ "
         (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
       `F
       " ⋙ "
       (TopCat.Topology.Category.TopCat.Limits.termforget "forget"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (TopCat.Topology.Category.TopCat.Limits.termforget "forget")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'TopCat.Topology.Category.TopCat.Limits.termforget', expected 'TopCat.Topology.Category.TopCat.Limits.termforget._@.Topology.Category.TopCat.Limits._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  forgetPreservesColimitsOfSize
  : PreservesColimitsOfSize .{ v , v } ( forget : TopCat .{ max v u } ⥤ Type max v u )
  where
    PreservesColimitsOfShape
      J 𝒥
      :=
      {
        PreservesColimit
          :=
          fun
            F
              =>
              preserves_colimit_of_preserves_colimit_cocone
                colimit_cocone_is_colimit F types.colimit_cocone_is_colimit F ⋙ forget
        }
#align Top.forget_preserves_colimits_of_size TopCat.forgetPreservesColimitsOfSize

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `forgetPreservesColimits [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `PreservesColimits
         [(Term.typeAscription
           "("
           (TopCat.Topology.Category.TopCat.Limits.termforget "forget")
           ":"
           [(CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
             (Term.explicitUniv `TopCat ".{" [`u] "}")
             " ⥤ "
             (Term.type "Type" [`u]))]
           ")")])))
      (Command.declValSimple
       ":="
       (Term.explicitUniv `TopCat.forgetPreservesColimitsOfSize ".{" [`u "," `u] "}")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.explicitUniv `TopCat.forgetPreservesColimitsOfSize ".{" [`u "," `u] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `TopCat.forgetPreservesColimitsOfSize
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `PreservesColimits
       [(Term.typeAscription
         "("
         (TopCat.Topology.Category.TopCat.Limits.termforget "forget")
         ":"
         [(CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
           (Term.explicitUniv `TopCat ".{" [`u] "}")
           " ⥤ "
           (Term.type "Type" [`u]))]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (TopCat.Topology.Category.TopCat.Limits.termforget "forget")
       ":"
       [(CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
         (Term.explicitUniv `TopCat ".{" [`u] "}")
         " ⥤ "
         (Term.type "Type" [`u]))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
       (Term.explicitUniv `TopCat ".{" [`u] "}")
       " ⥤ "
       (Term.type "Type" [`u]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.type "Type" [`u])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 26 >? 1022, (some 1024,
     level) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 26, term))
      (Term.explicitUniv `TopCat ".{" [`u] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `u
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `TopCat
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 27 >? 1024, (none, [anonymous]) <=? (some 26, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 26, (some 26, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (TopCat.Topology.Category.TopCat.Limits.termforget "forget")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'TopCat.Topology.Category.TopCat.Limits.termforget', expected 'TopCat.Topology.Category.TopCat.Limits.termforget._@.Topology.Category.TopCat.Limits._hyg.10'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  forgetPreservesColimits
  : PreservesColimits ( forget : TopCat .{ u } ⥤ Type u )
  := TopCat.forgetPreservesColimitsOfSize .{ u , u }
#align Top.forget_preserves_colimits TopCat.forgetPreservesColimits

/-- The projection from the product as a bundled continous map. -/
abbrev piπ {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) : TopCat.of (∀ i, α i) ⟶ α i :=
  ⟨fun f => f i, continuous_apply i⟩
#align Top.pi_π TopCat.piπ

/-- The explicit fan of a family of topological spaces given by the pi type. -/
@[simps x π_app]
def piFan {ι : Type v} (α : ι → TopCat.{max v u}) : Fan α :=
  Fan.mk (TopCat.of (∀ i, α i)) (piπ α)
#align Top.pi_fan TopCat.piFan

/-- The constructed fan is indeed a limit -/
def piFanIsLimit {ι : Type v} (α : ι → TopCat.{max v u}) : IsLimit (piFan α)
    where
  lift S := { toFun := fun s i => S.π.app ⟨i⟩ s }
  uniq' := by
    intro S m h
    ext (x i)
    simp [← h ⟨i⟩]
  fac' s j := by
    cases j
    tidy
#align Top.pi_fan_is_limit TopCat.piFanIsLimit

/-- The product is homeomorphic to the product of the underlying spaces,
equipped with the product topology.
-/
def piIsoPi {ι : Type v} (α : ι → TopCat.{max v u}) : ∏ α ≅ TopCat.of (∀ i, α i) :=
  (limit.isLimit _).conePointUniqueUpToIso (piFanIsLimit α)
#align Top.pi_iso_pi TopCat.piIsoPi

@[simp, reassoc.1]
theorem pi_iso_pi_inv_π {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) :
    (piIsoPi α).inv ≫ Pi.π α i = piπ α i := by simp [pi_iso_pi]
#align Top.pi_iso_pi_inv_π TopCat.pi_iso_pi_inv_π

@[simp]
theorem pi_iso_pi_inv_π_apply {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) (x : ∀ i, α i) :
    (Pi.π α i : _) ((piIsoPi α).inv x) = x i :=
  ConcreteCategory.congr_hom (pi_iso_pi_inv_π α i) x
#align Top.pi_iso_pi_inv_π_apply TopCat.pi_iso_pi_inv_π_apply

@[simp]
theorem pi_iso_pi_hom_apply {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) (x : ∏ α) :
    (piIsoPi α).Hom x i = (Pi.π α i : _) x :=
  by
  have := pi_iso_pi_inv_π α i
  rw [iso.inv_comp_eq] at this
  exact concrete_category.congr_hom this x
#align Top.pi_iso_pi_hom_apply TopCat.pi_iso_pi_hom_apply

/-- The inclusion to the coproduct as a bundled continous map. -/
abbrev sigmaι {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) : α i ⟶ TopCat.of (Σi, α i) :=
  ⟨Sigma.mk i⟩
#align Top.sigma_ι TopCat.sigmaι

/-- The explicit cofan of a family of topological spaces given by the sigma type. -/
@[simps x ι_app]
def sigmaCofan {ι : Type v} (α : ι → TopCat.{max v u}) : Cofan α :=
  Cofan.mk (TopCat.of (Σi, α i)) (sigmaι α)
#align Top.sigma_cofan TopCat.sigmaCofan

/-- The constructed cofan is indeed a colimit -/
def sigmaCofanIsColimit {ι : Type v} (α : ι → TopCat.{max v u}) : IsColimit (sigmaCofan α)
    where
  desc S :=
    { toFun := fun s => S.ι.app ⟨s.1⟩ s.2
      continuous_to_fun := continuous_sigma fun i => map_continuous (S.ι.app ⟨i⟩) }
  uniq' := by
    intro S m h
    ext ⟨i, x⟩
    simp [← h ⟨i⟩]
  fac' s j := by
    cases j
    tidy
#align Top.sigma_cofan_is_colimit TopCat.sigmaCofanIsColimit

/-- The coproduct is homeomorphic to the disjoint union of the topological spaces.
-/
def sigmaIsoSigma {ι : Type v} (α : ι → TopCat.{max v u}) : ∐ α ≅ TopCat.of (Σi, α i) :=
  (colimit.isColimit _).coconePointUniqueUpToIso (sigmaCofanIsColimit α)
#align Top.sigma_iso_sigma TopCat.sigmaIsoSigma

@[simp, reassoc.1]
theorem sigma_iso_sigma_hom_ι {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) :
    Sigma.ι α i ≫ (sigmaIsoSigma α).Hom = sigmaι α i := by simp [sigma_iso_sigma]
#align Top.sigma_iso_sigma_hom_ι TopCat.sigma_iso_sigma_hom_ι

@[simp]
theorem sigma_iso_sigma_hom_ι_apply {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) (x : α i) :
    (sigmaIsoSigma α).Hom ((Sigma.ι α i : _) x) = Sigma.mk i x :=
  ConcreteCategory.congr_hom (sigma_iso_sigma_hom_ι α i) x
#align Top.sigma_iso_sigma_hom_ι_apply TopCat.sigma_iso_sigma_hom_ι_apply

@[simp]
theorem sigma_iso_sigma_inv_apply {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) (x : α i) :
    (sigmaIsoSigma α).inv ⟨i, x⟩ = (Sigma.ι α i : _) x :=
  by
  rw [← sigma_iso_sigma_hom_ι_apply, ← comp_app]
  simp
#align Top.sigma_iso_sigma_inv_apply TopCat.sigma_iso_sigma_inv_apply

theorem induced_of_is_limit {F : J ⥤ TopCat.{max v u}} (C : Cone F) (hC : IsLimit C) :
    C.x.TopologicalSpace = ⨅ j, (F.obj j).TopologicalSpace.induced (C.π.app j) :=
  by
  let homeo := homeo_of_iso (hC.cone_point_unique_up_to_iso (limit_cone_infi_is_limit F))
  refine' homeo.inducing.induced.trans _
  change induced homeo (⨅ j : J, _) = _
  simpa [induced_infi, induced_compose]
#align Top.induced_of_is_limit TopCat.induced_of_is_limit

theorem limit_topology (F : J ⥤ TopCat.{max v u}) :
    (limit F).TopologicalSpace = ⨅ j, (F.obj j).TopologicalSpace.induced (limit.π F j) :=
  induced_of_is_limit _ (limit.isLimit F)
#align Top.limit_topology TopCat.limit_topology

section Prod

/-- The first projection from the product. -/
abbrev prodFst {X Y : TopCat.{u}} : TopCat.of (X × Y) ⟶ X :=
  ⟨Prod.fst⟩
#align Top.prod_fst TopCat.prodFst

/-- The second projection from the product. -/
abbrev prodSnd {X Y : TopCat.{u}} : TopCat.of (X × Y) ⟶ Y :=
  ⟨Prod.snd⟩
#align Top.prod_snd TopCat.prodSnd

/-- The explicit binary cofan of `X, Y` given by `X × Y`. -/
def prodBinaryFan (X Y : TopCat.{u}) : BinaryFan X Y :=
  BinaryFan.mk prodFst prodSnd
#align Top.prod_binary_fan TopCat.prodBinaryFan

/-- The constructed binary fan is indeed a limit -/
def prodBinaryFanIsLimit (X Y : TopCat.{u}) : IsLimit (prodBinaryFan X Y)
    where
  lift := fun S : BinaryFan X Y => { toFun := fun s => (S.fst s, S.snd s) }
  fac' := by
    rintro S (_ | _)
    tidy
  uniq' := by
    intro S m h
    ext x
    · specialize h ⟨walking_pair.left⟩
      apply_fun fun e => e x  at h
      exact h
    · specialize h ⟨walking_pair.right⟩
      apply_fun fun e => e x  at h
      exact h
#align Top.prod_binary_fan_is_limit TopCat.prodBinaryFanIsLimit

/-- The homeomorphism between `X ⨯ Y` and the set-theoretic product of `X` and `Y`,
equipped with the product topology.
-/
def prodIsoProd (X Y : TopCat.{u}) : X ⨯ Y ≅ TopCat.of (X × Y) :=
  (limit.isLimit _).conePointUniqueUpToIso (prodBinaryFanIsLimit X Y)
#align Top.prod_iso_prod TopCat.prodIsoProd

@[simp, reassoc.1]
theorem prod_iso_prod_hom_fst (X Y : TopCat.{u}) :
    (prodIsoProd X Y).Hom ≫ prod_fst = limits.prod.fst := by
  simpa [← iso.eq_inv_comp, prod_iso_prod]
#align Top.prod_iso_prod_hom_fst TopCat.prod_iso_prod_hom_fst

@[simp, reassoc.1]
theorem prod_iso_prod_hom_snd (X Y : TopCat.{u}) :
    (prodIsoProd X Y).Hom ≫ prod_snd = limits.prod.snd := by
  simpa [← iso.eq_inv_comp, prod_iso_prod]
#align Top.prod_iso_prod_hom_snd TopCat.prod_iso_prod_hom_snd

@[simp]
theorem prod_iso_prod_hom_apply {X Y : TopCat.{u}} (x : X ⨯ Y) :
    (prodIsoProd X Y).Hom x = ((Limits.prod.fst : X ⨯ Y ⟶ _) x, (Limits.prod.snd : X ⨯ Y ⟶ _) x) :=
  by
  ext
  · exact concrete_category.congr_hom (prod_iso_prod_hom_fst X Y) x
  · exact concrete_category.congr_hom (prod_iso_prod_hom_snd X Y) x
#align Top.prod_iso_prod_hom_apply TopCat.prod_iso_prod_hom_apply

@[simp, reassoc.1, elementwise]
theorem prod_iso_prod_inv_fst (X Y : TopCat.{u}) :
    (prodIsoProd X Y).inv ≫ limits.prod.fst = prod_fst := by simp [iso.inv_comp_eq]
#align Top.prod_iso_prod_inv_fst TopCat.prod_iso_prod_inv_fst

@[simp, reassoc.1, elementwise]
theorem prod_iso_prod_inv_snd (X Y : TopCat.{u}) :
    (prodIsoProd X Y).inv ≫ limits.prod.snd = prod_snd := by simp [iso.inv_comp_eq]
#align Top.prod_iso_prod_inv_snd TopCat.prod_iso_prod_inv_snd

theorem prod_topology {X Y : TopCat} :
    (X ⨯ Y).TopologicalSpace =
      induced (Limits.prod.fst : X ⨯ Y ⟶ _) X.TopologicalSpace ⊓
        induced (Limits.prod.snd : X ⨯ Y ⟶ _) Y.TopologicalSpace :=
  by
  let homeo := homeo_of_iso (prod_iso_prod X Y)
  refine' homeo.inducing.induced.trans _
  change induced homeo (_ ⊓ _) = _
  simpa [induced_compose]
#align Top.prod_topology TopCat.prod_topology

theorem range_prod_map {W X Y Z : TopCat.{u}} (f : W ⟶ Y) (g : X ⟶ Z) :
    Set.range (Limits.prod.map f g) =
      (Limits.prod.fst : Y ⨯ Z ⟶ _) ⁻¹' Set.range f ∩
        (Limits.prod.snd : Y ⨯ Z ⟶ _) ⁻¹' Set.range g :=
  by
  ext
  constructor
  · rintro ⟨y, rfl⟩
    simp only [Set.mem_preimage, Set.mem_range, Set.mem_inter_iff, ← comp_apply]
    simp only [limits.prod.map_fst, limits.prod.map_snd, exists_apply_eq_apply, comp_apply,
      and_self_iff]
  · rintro ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
    use (prod_iso_prod W X).inv (x₁, x₂)
    apply concrete.limit_ext
    rintro ⟨⟨⟩⟩
    · simp only [← comp_apply, category.assoc]
      erw [limits.prod.map_fst]
      simp [hx₁]
    · simp only [← comp_apply, category.assoc]
      erw [limits.prod.map_snd]
      simp [hx₂]
#align Top.range_prod_map TopCat.range_prod_map

theorem inducing_prod_map {W X Y Z : TopCat} {f : W ⟶ X} {g : Y ⟶ Z} (hf : Inducing f)
    (hg : Inducing g) : Inducing (Limits.prod.map f g) :=
  by
  constructor
  simp only [prod_topology, induced_compose, ← coe_comp, limits.prod.map_fst, limits.prod.map_snd,
    induced_inf]
  simp only [coe_comp]
  rw [← @induced_compose _ _ _ _ _ f, ← @induced_compose _ _ _ _ _ g, ← hf.induced, ← hg.induced]
#align Top.inducing_prod_map TopCat.inducing_prod_map

theorem embedding_prod_map {W X Y Z : TopCat} {f : W ⟶ X} {g : Y ⟶ Z} (hf : Embedding f)
    (hg : Embedding g) : Embedding (Limits.prod.map f g) :=
  ⟨inducing_prod_map hf.to_inducing hg.to_inducing,
    by
    haveI := (TopCat.mono_iff_injective _).mpr hf.inj
    haveI := (TopCat.mono_iff_injective _).mpr hg.inj
    exact (TopCat.mono_iff_injective _).mp inferInstance⟩
#align Top.embedding_prod_map TopCat.embedding_prod_map

end Prod

section Pullback

variable {X Y Z : TopCat.{u}}

/-- The first projection from the pullback. -/
abbrev pullbackFst (f : X ⟶ Z) (g : Y ⟶ Z) : TopCat.of { p : X × Y // f p.1 = g p.2 } ⟶ X :=
  ⟨Prod.fst ∘ Subtype.val⟩
#align Top.pullback_fst TopCat.pullbackFst

/-- The second projection from the pullback. -/
abbrev pullbackSnd (f : X ⟶ Z) (g : Y ⟶ Z) : TopCat.of { p : X × Y // f p.1 = g p.2 } ⟶ Y :=
  ⟨Prod.snd ∘ Subtype.val⟩
#align Top.pullback_snd TopCat.pullbackSnd

/-- The explicit pullback cone of `X, Y` given by `{ p : X × Y // f p.1 = g p.2 }`. -/
def pullbackCone (f : X ⟶ Z) (g : Y ⟶ Z) : PullbackCone f g :=
  PullbackCone.mk (pullbackFst f g) (pullbackSnd f g)
    (by
      ext ⟨x, h⟩
      simp [h])
#align Top.pullback_cone TopCat.pullbackCone

/-- The constructed cone is a limit. -/
def pullbackConeIsLimit (f : X ⟶ Z) (g : Y ⟶ Z) : IsLimit (pullbackCone f g) :=
  PullbackCone.isLimitAux' _
    (by
      intro s
      constructor; swap
      exact
        {
          toFun := fun x =>
            ⟨⟨s.fst x, s.snd x⟩, by simpa using concrete_category.congr_hom s.condition x⟩ }
      refine' ⟨_, _, _⟩
      · ext
        delta pullback_cone
        simp
      · ext
        delta pullback_cone
        simp
      · intro m h₁ h₂
        ext x
        · simpa using concrete_category.congr_hom h₁ x
        · simpa using concrete_category.congr_hom h₂ x)
#align Top.pullback_cone_is_limit TopCat.pullbackConeIsLimit

/-- The pullback of two maps can be identified as a subspace of `X × Y`. -/
def pullbackIsoProdSubtype (f : X ⟶ Z) (g : Y ⟶ Z) :
    pullback f g ≅ TopCat.of { p : X × Y // f p.1 = g p.2 } :=
  (limit.isLimit _).conePointUniqueUpToIso (pullbackConeIsLimit f g)
#align Top.pullback_iso_prod_subtype TopCat.pullbackIsoProdSubtype

@[simp, reassoc.1]
theorem pullback_iso_prod_subtype_inv_fst (f : X ⟶ Z) (g : Y ⟶ Z) :
    (pullbackIsoProdSubtype f g).inv ≫ pullback.fst = pullbackFst f g := by
  simpa [pullback_iso_prod_subtype]
#align Top.pullback_iso_prod_subtype_inv_fst TopCat.pullback_iso_prod_subtype_inv_fst

@[simp]
theorem pullback_iso_prod_subtype_inv_fst_apply (f : X ⟶ Z) (g : Y ⟶ Z)
    (x : { p : X × Y // f p.1 = g p.2 }) :
    (pullback.fst : pullback f g ⟶ _) ((pullbackIsoProdSubtype f g).inv x) = (x : X × Y).fst :=
  ConcreteCategory.congr_hom (pullback_iso_prod_subtype_inv_fst f g) x
#align Top.pullback_iso_prod_subtype_inv_fst_apply TopCat.pullback_iso_prod_subtype_inv_fst_apply

@[simp, reassoc.1]
theorem pullback_iso_prod_subtype_inv_snd (f : X ⟶ Z) (g : Y ⟶ Z) :
    (pullbackIsoProdSubtype f g).inv ≫ pullback.snd = pullbackSnd f g := by
  simpa [pullback_iso_prod_subtype]
#align Top.pullback_iso_prod_subtype_inv_snd TopCat.pullback_iso_prod_subtype_inv_snd

@[simp]
theorem pullback_iso_prod_subtype_inv_snd_apply (f : X ⟶ Z) (g : Y ⟶ Z)
    (x : { p : X × Y // f p.1 = g p.2 }) :
    (pullback.snd : pullback f g ⟶ _) ((pullbackIsoProdSubtype f g).inv x) = (x : X × Y).snd :=
  ConcreteCategory.congr_hom (pullback_iso_prod_subtype_inv_snd f g) x
#align Top.pullback_iso_prod_subtype_inv_snd_apply TopCat.pullback_iso_prod_subtype_inv_snd_apply

theorem pullback_iso_prod_subtype_hom_fst (f : X ⟶ Z) (g : Y ⟶ Z) :
    (pullbackIsoProdSubtype f g).Hom ≫ pullbackFst f g = pullback.fst := by
  rw [← iso.eq_inv_comp, pullback_iso_prod_subtype_inv_fst]
#align Top.pullback_iso_prod_subtype_hom_fst TopCat.pullback_iso_prod_subtype_hom_fst

theorem pullback_iso_prod_subtype_hom_snd (f : X ⟶ Z) (g : Y ⟶ Z) :
    (pullbackIsoProdSubtype f g).Hom ≫ pullbackSnd f g = pullback.snd := by
  rw [← iso.eq_inv_comp, pullback_iso_prod_subtype_inv_snd]
#align Top.pullback_iso_prod_subtype_hom_snd TopCat.pullback_iso_prod_subtype_hom_snd

@[simp]
theorem pullback_iso_prod_subtype_hom_apply {f : X ⟶ Z} {g : Y ⟶ Z} (x : pullback f g) :
    (pullbackIsoProdSubtype f g).Hom x =
      ⟨⟨(pullback.fst : pullback f g ⟶ _) x, (pullback.snd : pullback f g ⟶ _) x⟩, by
        simpa using concrete_category.congr_hom pullback.condition x⟩ :=
  by
  ext
  exacts[concrete_category.congr_hom (pullback_iso_prod_subtype_hom_fst f g) x,
    concrete_category.congr_hom (pullback_iso_prod_subtype_hom_snd f g) x]
#align Top.pullback_iso_prod_subtype_hom_apply TopCat.pullback_iso_prod_subtype_hom_apply

theorem pullback_topology {X Y Z : TopCat.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (pullback f g).TopologicalSpace =
      induced (pullback.fst : pullback f g ⟶ _) X.TopologicalSpace ⊓
        induced (pullback.snd : pullback f g ⟶ _) Y.TopologicalSpace :=
  by
  let homeo := homeo_of_iso (pullback_iso_prod_subtype f g)
  refine' homeo.inducing.induced.trans _
  change induced homeo (induced _ (_ ⊓ _)) = _
  simpa [induced_compose]
#align Top.pullback_topology TopCat.pullback_topology

theorem range_pullback_to_prod {X Y Z : TopCat} (f : X ⟶ Z) (g : Y ⟶ Z) :
    Set.range (prod.lift pullback.fst pullback.snd : pullback f g ⟶ X ⨯ Y) =
      { x | (limits.prod.fst ≫ f) x = (limits.prod.snd ≫ g) x } :=
  by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    simp only [← comp_apply, Set.mem_setOf_eq]
    congr 1
    simp [pullback.condition]
  · intro h
    use (pullback_iso_prod_subtype f g).inv ⟨⟨_, _⟩, h⟩
    apply concrete.limit_ext
    rintro ⟨⟨⟩⟩ <;> simp
#align Top.range_pullback_to_prod TopCat.range_pullback_to_prod

theorem inducing_pullback_to_prod {X Y Z : TopCat} (f : X ⟶ Z) (g : Y ⟶ Z) :
    Inducing ⇑(prod.lift pullback.fst pullback.snd : pullback f g ⟶ X ⨯ Y) :=
  ⟨by simp [prod_topology, pullback_topology, induced_compose, ← coe_comp]⟩
#align Top.inducing_pullback_to_prod TopCat.inducing_pullback_to_prod

theorem embedding_pullback_to_prod {X Y Z : TopCat} (f : X ⟶ Z) (g : Y ⟶ Z) :
    Embedding ⇑(prod.lift pullback.fst pullback.snd : pullback f g ⟶ X ⨯ Y) :=
  ⟨inducing_pullback_to_prod f g, (TopCat.mono_iff_injective _).mp inferInstance⟩
#align Top.embedding_pullback_to_prod TopCat.embedding_pullback_to_prod

/-- If the map `S ⟶ T` is mono, then there is a description of the image of `W ×ₛ X ⟶ Y ×ₜ Z`. -/
theorem range_pullback_map {W X Y Z S T : TopCat} (f₁ : W ⟶ S) (f₂ : X ⟶ S) (g₁ : Y ⟶ T)
    (g₂ : Z ⟶ T) (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) [H₃ : Mono i₃] (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁)
    (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
    Set.range (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) =
      (pullback.fst : pullback g₁ g₂ ⟶ _) ⁻¹' Set.range i₁ ∩
        (pullback.snd : pullback g₁ g₂ ⟶ _) ⁻¹' Set.range i₂ :=
  by
  ext
  constructor
  · rintro ⟨y, rfl⟩
    simp
  rintro ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
  have : f₁ x₁ = f₂ x₂ := by
    apply (TopCat.mono_iff_injective _).mp H₃
    simp only [← comp_apply, eq₁, eq₂]
    simp only [comp_apply, hx₁, hx₂]
    simp only [← comp_apply, pullback.condition]
  use (pullback_iso_prod_subtype f₁ f₂).inv ⟨⟨x₁, x₂⟩, this⟩
  apply concrete.limit_ext
  rintro (_ | _ | _)
  · simp only [TopCat.comp_app, limit.lift_π_apply, category.assoc, pullback_cone.mk_π_app_one, hx₁,
      pullback_iso_prod_subtype_inv_fst_apply, Subtype.coe_mk]
    simp only [← comp_apply]
    congr
    apply limit.w _ walking_cospan.hom.inl
  · simp [hx₁]
  · simp [hx₂]
#align Top.range_pullback_map TopCat.range_pullback_map

theorem pullback_fst_range {X Y S : TopCat} (f : X ⟶ S) (g : Y ⟶ S) :
    Set.range (pullback.fst : pullback f g ⟶ _) = { x : X | ∃ y : Y, f x = g y } :=
  by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    use (pullback.snd : pullback f g ⟶ _) y
    exact concrete_category.congr_hom pullback.condition y
  · rintro ⟨y, eq⟩
    use (TopCat.pullbackIsoProdSubtype f g).inv ⟨⟨x, y⟩, Eq⟩
    simp
#align Top.pullback_fst_range TopCat.pullback_fst_range

theorem pullback_snd_range {X Y S : TopCat} (f : X ⟶ S) (g : Y ⟶ S) :
    Set.range (pullback.snd : pullback f g ⟶ _) = { y : Y | ∃ x : X, f x = g y } :=
  by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    use (pullback.fst : pullback f g ⟶ _) x
    exact concrete_category.congr_hom pullback.condition x
  · rintro ⟨x, eq⟩
    use (TopCat.pullbackIsoProdSubtype f g).inv ⟨⟨x, y⟩, Eq⟩
    simp
#align Top.pullback_snd_range TopCat.pullback_snd_range

/-- If there is a diagram where the morphisms `W ⟶ Y` and `X ⟶ Z` are embeddings,
then the induced morphism `W ×ₛ X ⟶ Y ×ₜ Z` is also an embedding.

  W  ⟶  Y
    ↘      ↘
      S  ⟶  T
    ↗      ↗
  X  ⟶  Z
-/
theorem pullback_map_embedding_of_embeddings {W X Y Z S T : TopCat} (f₁ : W ⟶ S) (f₂ : X ⟶ S)
    (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) {i₁ : W ⟶ Y} {i₂ : X ⟶ Z} (H₁ : Embedding i₁) (H₂ : Embedding i₂)
    (i₃ : S ⟶ T) (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
    Embedding (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) :=
  by
  refine'
    embedding_of_embedding_compose (ContinuousMap.continuous_to_fun _)
      (show Continuous (prod.lift pullback.fst pullback.snd : pullback g₁ g₂ ⟶ Y ⨯ Z) from
        ContinuousMap.continuous_to_fun _)
      _
  suffices
    Embedding (prod.lift pullback.fst pullback.snd ≫ limits.prod.map i₁ i₂ : pullback f₁ f₂ ⟶ _) by
    simpa [← coe_comp] using this
  rw [coe_comp]
  refine' Embedding.comp (embedding_prod_map H₁ H₂) (embedding_pullback_to_prod _ _)
#align Top.pullback_map_embedding_of_embeddings TopCat.pullback_map_embedding_of_embeddings

/-- If there is a diagram where the morphisms `W ⟶ Y` and `X ⟶ Z` are open embeddings, and `S ⟶ T`
is mono, then the induced morphism `W ×ₛ X ⟶ Y ×ₜ Z` is also an open embedding.
  W  ⟶  Y
    ↘      ↘
      S  ⟶  T
    ↗       ↗
  X  ⟶  Z
-/
theorem pullback_map_open_embedding_of_open_embeddings {W X Y Z S T : TopCat} (f₁ : W ⟶ S)
    (f₂ : X ⟶ S) (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) {i₁ : W ⟶ Y} {i₂ : X ⟶ Z} (H₁ : OpenEmbedding i₁)
    (H₂ : OpenEmbedding i₂) (i₃ : S ⟶ T) [H₃ : Mono i₃] (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁)
    (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) : OpenEmbedding (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) :=
  by
  constructor
  ·
    apply
      pullback_map_embedding_of_embeddings f₁ f₂ g₁ g₂ H₁.to_embedding H₂.to_embedding i₃ eq₁ eq₂
  · rw [range_pullback_map]
    apply IsOpen.inter <;> apply Continuous.is_open_preimage
    continuity
    exacts[H₁.open_range, H₂.open_range]
#align
  Top.pullback_map_open_embedding_of_open_embeddings TopCat.pullback_map_open_embedding_of_open_embeddings

theorem snd_embedding_of_left_embedding {X Y S : TopCat} {f : X ⟶ S} (H : Embedding f) (g : Y ⟶ S) :
    Embedding ⇑(pullback.snd : pullback f g ⟶ Y) :=
  by
  convert
    (homeo_of_iso (as_iso (pullback.snd : pullback (𝟙 S) g ⟶ _))).Embedding.comp
      (pullback_map_embedding_of_embeddings f g (𝟙 _) g H (homeo_of_iso (iso.refl _)).Embedding
        (𝟙 _) rfl (by simp))
  erw [← coe_comp]
  simp
#align Top.snd_embedding_of_left_embedding TopCat.snd_embedding_of_left_embedding

theorem fst_embedding_of_right_embedding {X Y S : TopCat} (f : X ⟶ S) {g : Y ⟶ S}
    (H : Embedding g) : Embedding ⇑(pullback.fst : pullback f g ⟶ X) :=
  by
  convert
    (homeo_of_iso (as_iso (pullback.fst : pullback f (𝟙 S) ⟶ _))).Embedding.comp
      (pullback_map_embedding_of_embeddings f g f (𝟙 _) (homeo_of_iso (iso.refl _)).Embedding H
        (𝟙 _) rfl (by simp))
  erw [← coe_comp]
  simp
#align Top.fst_embedding_of_right_embedding TopCat.fst_embedding_of_right_embedding

theorem embedding_of_pullback_embeddings {X Y S : TopCat} {f : X ⟶ S} {g : Y ⟶ S} (H₁ : Embedding f)
    (H₂ : Embedding g) : Embedding (limit.π (cospan f g) WalkingCospan.one) :=
  by
  convert H₂.comp (snd_embedding_of_left_embedding H₁ g)
  erw [← coe_comp]
  congr
  exact (limit.w _ walking_cospan.hom.inr).symm
#align Top.embedding_of_pullback_embeddings TopCat.embedding_of_pullback_embeddings

theorem snd_open_embedding_of_left_open_embedding {X Y S : TopCat} {f : X ⟶ S} (H : OpenEmbedding f)
    (g : Y ⟶ S) : OpenEmbedding ⇑(pullback.snd : pullback f g ⟶ Y) :=
  by
  convert
    (homeo_of_iso (as_iso (pullback.snd : pullback (𝟙 S) g ⟶ _))).OpenEmbedding.comp
      (pullback_map_open_embedding_of_open_embeddings f g (𝟙 _) g H
        (homeo_of_iso (iso.refl _)).OpenEmbedding (𝟙 _) rfl (by simp))
  erw [← coe_comp]
  simp
#align
  Top.snd_open_embedding_of_left_open_embedding TopCat.snd_open_embedding_of_left_open_embedding

theorem fst_open_embedding_of_right_open_embedding {X Y S : TopCat} (f : X ⟶ S) {g : Y ⟶ S}
    (H : OpenEmbedding g) : OpenEmbedding ⇑(pullback.fst : pullback f g ⟶ X) :=
  by
  convert
    (homeo_of_iso (as_iso (pullback.fst : pullback f (𝟙 S) ⟶ _))).OpenEmbedding.comp
      (pullback_map_open_embedding_of_open_embeddings f g f (𝟙 _)
        (homeo_of_iso (iso.refl _)).OpenEmbedding H (𝟙 _) rfl (by simp))
  erw [← coe_comp]
  simp
#align
  Top.fst_open_embedding_of_right_open_embedding TopCat.fst_open_embedding_of_right_open_embedding

/-- If `X ⟶ S`, `Y ⟶ S` are open embeddings, then so is `X ×ₛ Y ⟶ S`. -/
theorem open_embedding_of_pullback_open_embeddings {X Y S : TopCat} {f : X ⟶ S} {g : Y ⟶ S}
    (H₁ : OpenEmbedding f) (H₂ : OpenEmbedding g) :
    OpenEmbedding (limit.π (cospan f g) WalkingCospan.one) :=
  by
  convert H₂.comp (snd_open_embedding_of_left_open_embedding H₁ g)
  erw [← coe_comp]
  congr
  exact (limit.w _ walking_cospan.hom.inr).symm
#align
  Top.open_embedding_of_pullback_open_embeddings TopCat.open_embedding_of_pullback_open_embeddings

theorem fst_iso_of_right_embedding_range_subset {X Y S : TopCat} (f : X ⟶ S) {g : Y ⟶ S}
    (hg : Embedding g) (H : Set.range f ⊆ Set.range g) : IsIso (pullback.fst : pullback f g ⟶ X) :=
  by
  let this : (pullback f g : TopCat) ≃ₜ X :=
    (Homeomorph.ofEmbedding _ (fst_embedding_of_right_embedding f hg)).trans
      { toFun := coe
        invFun := fun x =>
          ⟨x, by
            rw [pullback_fst_range]
            exact ⟨_, (H (Set.mem_range_self x)).some_spec.symm⟩⟩
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := fun x => rfl }
  convert is_iso.of_iso (iso_of_homeo this)
  ext
  rfl
#align Top.fst_iso_of_right_embedding_range_subset TopCat.fst_iso_of_right_embedding_range_subset

theorem snd_iso_of_left_embedding_range_subset {X Y S : TopCat} {f : X ⟶ S} (hf : Embedding f)
    (g : Y ⟶ S) (H : Set.range g ⊆ Set.range f) : IsIso (pullback.snd : pullback f g ⟶ Y) :=
  by
  let this : (pullback f g : TopCat) ≃ₜ Y :=
    (Homeomorph.ofEmbedding _ (snd_embedding_of_left_embedding hf g)).trans
      { toFun := coe
        invFun := fun x =>
          ⟨x, by
            rw [pullback_snd_range]
            exact ⟨_, (H (Set.mem_range_self x)).some_spec⟩⟩
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := fun x => rfl }
  convert is_iso.of_iso (iso_of_homeo this)
  ext
  rfl
#align Top.snd_iso_of_left_embedding_range_subset TopCat.snd_iso_of_left_embedding_range_subset

theorem pullback_snd_image_fst_preimage (f : X ⟶ Z) (g : Y ⟶ Z) (U : Set X) :
    (pullback.snd : pullback f g ⟶ _) '' ((pullback.fst : pullback f g ⟶ _) ⁻¹' U) =
      g ⁻¹' (f '' U) :=
  by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact
      ⟨(pullback.fst : pullback f g ⟶ _) y, hy, concrete_category.congr_hom pullback.condition y⟩
  · rintro ⟨y, hy, eq⟩
    exact ⟨(TopCat.pullbackIsoProdSubtype f g).inv ⟨⟨_, _⟩, Eq⟩, by simpa, by simp⟩
#align Top.pullback_snd_image_fst_preimage TopCat.pullback_snd_image_fst_preimage

theorem pullback_fst_image_snd_preimage (f : X ⟶ Z) (g : Y ⟶ Z) (U : Set Y) :
    (pullback.fst : pullback f g ⟶ _) '' ((pullback.snd : pullback f g ⟶ _) ⁻¹' U) =
      f ⁻¹' (g '' U) :=
  by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact
      ⟨(pullback.snd : pullback f g ⟶ _) y, hy,
        (concrete_category.congr_hom pullback.condition y).symm⟩
  · rintro ⟨y, hy, eq⟩
    exact ⟨(TopCat.pullbackIsoProdSubtype f g).inv ⟨⟨_, _⟩, Eq.symm⟩, by simpa, by simp⟩
#align Top.pullback_fst_image_snd_preimage TopCat.pullback_fst_image_snd_preimage

end Pullback

/-- The terminal object of `Top` is `punit`. -/
def isTerminalPunit : IsTerminal (TopCat.of PUnit.{u + 1}) :=
  haveI : ∀ X, Unique (X ⟶ TopCat.of PUnit.{u + 1}) := fun X =>
    ⟨⟨⟨fun x => PUnit.unit, by continuity⟩⟩, fun f => by ext⟩
  limits.is_terminal.of_unique _
#align Top.is_terminal_punit TopCat.isTerminalPunit

/-- The terminal object of `Top` is `punit`. -/
def terminalIsoPunit : ⊤_ TopCat.{u} ≅ TopCat.of PUnit :=
  terminalIsTerminal.uniqueUpToIso isTerminalPunit
#align Top.terminal_iso_punit TopCat.terminalIsoPunit

/-- The initial object of `Top` is `pempty`. -/
def isInitialPempty : IsInitial (TopCat.of PEmpty.{u + 1}) :=
  haveI : ∀ X, Unique (TopCat.of PEmpty.{u + 1} ⟶ X) := fun X =>
    ⟨⟨⟨fun x => x.elim, by continuity⟩⟩, fun f => by ext ⟨⟩⟩
  limits.is_initial.of_unique _
#align Top.is_initial_pempty TopCat.isInitialPempty

/-- The initial object of `Top` is `pempty`. -/
def initialIsoPempty : ⊥_ TopCat.{u} ≅ TopCat.of PEmpty :=
  initialIsInitial.uniqueUpToIso isInitialPempty
#align Top.initial_iso_pempty TopCat.initialIsoPempty

/-- The binary coproduct cofan in `Top`. -/
protected def binaryCofan (X Y : TopCat.{u}) : BinaryCofan X Y :=
  BinaryCofan.mk (⟨Sum.inl⟩ : X ⟶ TopCat.of (Sum X Y)) ⟨Sum.inr⟩
#align Top.binary_cofan TopCat.binaryCofan

/-- The constructed binary coproduct cofan in `Top` is the coproduct. -/
def binaryCofanIsColimit (X Y : TopCat.{u}) : IsColimit (TopCat.binaryCofan X Y) :=
  by
  refine' limits.binary_cofan.is_colimit_mk (fun s => ⟨Sum.elim s.inl s.inr⟩) _ _ _
  · intro s
    ext
    rfl
  · intro s
    ext
    rfl
  · intro s m h₁ h₂
    ext (x | x)
    exacts[(concrete_category.congr_hom h₁ x : _), (concrete_category.congr_hom h₂ x : _)]
#align Top.binary_cofan_is_colimit TopCat.binaryCofanIsColimit

theorem binary_cofan_is_colimit_iff {X Y : TopCat} (c : BinaryCofan X Y) :
    Nonempty (IsColimit c) ↔
      OpenEmbedding c.inl ∧ OpenEmbedding c.inr ∧ IsCompl (Set.range c.inl) (Set.range c.inr) :=
  by
  classical
    constructor
    · rintro ⟨h⟩
      rw [←
        show _ = c.inl from
          h.comp_cocone_point_unique_up_to_iso_inv (binary_cofan_is_colimit X Y)
            ⟨walking_pair.left⟩,
        ←
        show _ = c.inr from
          h.comp_cocone_point_unique_up_to_iso_inv (binary_cofan_is_colimit X Y)
            ⟨walking_pair.right⟩]
      dsimp
      refine'
        ⟨(homeo_of_iso <|
                    h.cocone_point_unique_up_to_iso
                      (binary_cofan_is_colimit X Y)).symm.OpenEmbedding.comp
            open_embedding_inl,
          (homeo_of_iso <|
                    h.cocone_point_unique_up_to_iso
                      (binary_cofan_is_colimit X Y)).symm.OpenEmbedding.comp
            open_embedding_inr,
          _⟩
      erw [Set.range_comp, ← eq_compl_iff_isCompl, Set.range_comp _ Sum.inr, ←
        Set.image_compl_eq
          (homeo_of_iso <|
                h.cocone_point_unique_up_to_iso (binary_cofan_is_colimit X Y)).symm.Bijective]
      congr 1
      exact set.compl_range_inr.symm
    · rintro ⟨h₁, h₂, h₃⟩
      have : ∀ x, x ∈ Set.range c.inl ∨ x ∈ Set.range c.inr :=
        by
        rw [eq_compl_iff_is_compl.mpr h₃.symm]
        exact fun _ => or_not
      refine' ⟨binary_cofan.is_colimit.mk _ _ _ _ _⟩
      · intro T f g
        refine' ContinuousMap.mk _ _
        ·
          exact fun x =>
            if h : x ∈ Set.range c.inl then f ((Equiv.ofInjective _ h₁.inj).symm ⟨x, h⟩)
            else g ((Equiv.ofInjective _ h₂.inj).symm ⟨x, (this x).resolve_left h⟩)
        rw [continuous_iff_continuous_at]
        intro x
        by_cases x ∈ Set.range c.inl
        · revert h x
          apply (IsOpen.continuous_on_iff _).mp
          · rw [continuous_on_iff_continuous_restrict]
            convert_to Continuous (f ∘ (Homeomorph.ofEmbedding _ h₁.to_embedding).symm)
            · ext ⟨x, hx⟩
              exact dif_pos hx
            continuity
          · exact h₁.open_range
        · revert h x
          apply (IsOpen.continuous_on_iff _).mp
          · rw [continuous_on_iff_continuous_restrict]
            have : ∀ a, a ∉ Set.range c.inl → a ∈ Set.range c.inr :=
              by
              rintro a (h : a ∈ Set.range c.inlᶜ)
              rwa [eq_compl_iff_is_compl.mpr h₃.symm]
            convert_to
              Continuous (g ∘ (Homeomorph.ofEmbedding _ h₂.to_embedding).symm ∘ Subtype.map _ this)
            · ext ⟨x, hx⟩
              exact dif_neg hx
            continuity
            rw [embedding_subtype_coe.to_inducing.continuous_iff]
            exact continuous_subtype_coe
          · change IsOpen (Set.range c.inlᶜ)
            rw [← eq_compl_iff_is_compl.mpr h₃.symm]
            exact h₂.open_range
      · intro T f g
        ext x
        refine' (dif_pos _).trans _
        · exact ⟨x, rfl⟩
        · rw [Equiv.ofInjective_symm_apply]
      · intro T f g
        ext x
        refine' (dif_neg _).trans _
        · rintro ⟨y, e⟩
          have : c.inr x ∈ Set.range c.inl ⊓ Set.range c.inr := ⟨⟨_, e⟩, ⟨_, rfl⟩⟩
          rwa [disjoint_iff.mp h₃.1] at this
        · exact congr_arg g (Equiv.ofInjective_symm_apply _ _)
      · rintro T _ _ m rfl rfl
        ext x
        change m x = dite _ _ _
        split_ifs <;> exact congr_arg _ (Equiv.apply_ofInjective_symm _ ⟨_, _⟩).symm
#align Top.binary_cofan_is_colimit_iff TopCat.binary_cofan_is_colimit_iff

--TODO: Add analogous constructions for `pushout`.
theorem coinduced_of_is_colimit {F : J ⥤ TopCat.{max v u}} (c : Cocone F) (hc : IsColimit c) :
    c.x.TopologicalSpace = ⨆ j, (F.obj j).TopologicalSpace.coinduced (c.ι.app j) :=
  by
  let homeo := homeo_of_iso (hc.cocone_point_unique_up_to_iso (colimit_cocone_is_colimit F))
  ext
  refine' homeo.symm.is_open_preimage.symm.trans (Iff.trans _ is_open_supr_iff.symm)
  exact is_open_supr_iff
#align Top.coinduced_of_is_colimit TopCat.coinduced_of_is_colimit

theorem colimit_topology (F : J ⥤ TopCat.{max v u}) :
    (colimit F).TopologicalSpace = ⨆ j, (F.obj j).TopologicalSpace.coinduced (colimit.ι F j) :=
  coinduced_of_is_colimit _ (colimit.isColimit F)
#align Top.colimit_topology TopCat.colimit_topology

theorem colimit_is_open_iff (F : J ⥤ TopCat.{max v u}) (U : Set ((colimit F : _) : Type max v u)) :
    IsOpen U ↔ ∀ j, IsOpen (colimit.ι F j ⁻¹' U) :=
  by
  conv_lhs => rw [colimit_topology F]
  exact is_open_supr_iff
#align Top.colimit_is_open_iff TopCat.colimit_is_open_iff

theorem coequalizer_is_open_iff (F : walking_parallel_pair ⥤ TopCat.{u})
    (U : Set ((colimit F : _) : Type u)) :
    IsOpen U ↔ IsOpen (colimit.ι F WalkingParallelPair.one ⁻¹' U) :=
  by
  rw [colimit_is_open_iff.{u}]
  constructor
  · intro H
    exact H _
  · intro H j
    cases j
    · rw [← colimit.w F walking_parallel_pair_hom.left]
      exact (F.map walking_parallel_pair_hom.left).continuous_to_fun.is_open_preimage _ H
    · exact H
#align Top.coequalizer_is_open_iff TopCat.coequalizer_is_open_iff

end TopCat

namespace TopCat

section CofilteredLimit

variable {J : Type v} [SmallCategory J] [IsCofiltered J] (F : J ⥤ TopCat.{max v u}) (C : Cone F)
  (hC : IsLimit C)

include hC

/-- Given a *compatible* collection of topological bases for the factors in a cofiltered limit
which contain `set.univ` and are closed under intersections, the induced *naive* collection
of sets in the limit is, in fact, a topological basis.
-/
theorem is_topological_basis_cofiltered_limit (T : ∀ j, Set (Set (F.obj j)))
    (hT : ∀ j, IsTopologicalBasis (T j)) (univ : ∀ i : J, Set.univ ∈ T i)
    (inter : ∀ (i) (U1 U2 : Set (F.obj i)), U1 ∈ T i → U2 ∈ T i → U1 ∩ U2 ∈ T i)
    (compat : ∀ (i j : J) (f : i ⟶ j) (V : Set (F.obj j)) (hV : V ∈ T j), F.map f ⁻¹' V ∈ T i) :
    IsTopologicalBasis
      { U : Set C.x | ∃ (j : _)(V : Set (F.obj j)), V ∈ T j ∧ U = C.π.app j ⁻¹' V } :=
  by
  classical
    -- The limit cone for `F` whose topology is defined as an infimum.
    let D := limit_cone_infi F
    -- The isomorphism between the cone point of `C` and the cone point of `D`.
    let E : C.X ≅ D.X := hC.cone_point_unique_up_to_iso (limit_cone_infi_is_limit _)
    have hE : Inducing E.hom := (TopCat.homeoOfIso E).Inducing
    -- Reduce to the assertion of the theorem with `D` instead of `C`.
    suffices
      is_topological_basis
        { U : Set D.X | ∃ (j : _)(V : Set (F.obj j)), V ∈ T j ∧ U = D.π.app j ⁻¹' V }
      by
      convert this.inducing hE
      ext U0
      constructor
      · rintro ⟨j, V, hV, rfl⟩
        refine' ⟨D.π.app j ⁻¹' V, ⟨j, V, hV, rfl⟩, rfl⟩
      · rintro ⟨W, ⟨j, V, hV, rfl⟩, rfl⟩
        refine' ⟨j, V, hV, rfl⟩
    -- Using `D`, we can apply the characterization of the topological basis of a
    -- topology defined as an infimum...
    convert is_topological_basis_infi hT fun j (x : D.X) => D.π.app j x
    ext U0
    constructor
    · rintro ⟨j, V, hV, rfl⟩
      let U : ∀ i, Set (F.obj i) := fun i =>
        if h : i = j then by
          rw [h]
          exact V
        else Set.univ
      refine' ⟨U, {j}, _, _⟩
      · rintro i h
        rw [Finset.mem_singleton] at h
        dsimp [U]
        rw [dif_pos h]
        subst h
        exact hV
      · dsimp [U]
        simp
    · rintro ⟨U, G, h1, h2⟩
      obtain ⟨j, hj⟩ := is_cofiltered.inf_objs_exists G
      let g : ∀ (e) (he : e ∈ G), j ⟶ e := fun _ he => (hj he).some
      let Vs : J → Set (F.obj j) := fun e => if h : e ∈ G then F.map (g e h) ⁻¹' U e else Set.univ
      let V : Set (F.obj j) := ⋂ (e : J) (he : e ∈ G), Vs e
      refine' ⟨j, V, _, _⟩
      · -- An intermediate claim used to apply induction along `G : finset J` later on.
        have :
          ∀ (S : Set (Set (F.obj j))) (E : Finset J) (P : J → Set (F.obj j)) (univ : Set.univ ∈ S)
            (inter : ∀ A B : Set (F.obj j), A ∈ S → B ∈ S → A ∩ B ∈ S)
            (cond : ∀ (e : J) (he : e ∈ E), P e ∈ S), (⋂ (e) (he : e ∈ E), P e) ∈ S :=
          by
          intro S E
          apply E.induction_on
          · intro P he hh
            simpa
          · intro a E ha hh1 hh2 hh3 hh4 hh5
            rw [Finset.set_bInter_insert]
            refine' hh4 _ _ (hh5 _ (Finset.mem_insert_self _ _)) (hh1 _ hh3 hh4 _)
            intro e he
            exact hh5 e (Finset.mem_insert_of_mem he)
        -- use the intermediate claim to finish off the goal using `univ` and `inter`.
        refine' this _ _ _ (univ _) (inter _) _
        intro e he
        dsimp [Vs]
        rw [dif_pos he]
        exact compat j e (g e he) (U e) (h1 e he)
      · -- conclude...
        rw [h2]
        dsimp [V]
        rw [Set.preimage_interᵢ]
        congr 1
        ext1 e
        rw [Set.preimage_interᵢ]
        congr 1
        ext1 he
        dsimp [Vs]
        rw [dif_pos he, ← Set.preimage_comp]
        congr 1
        change _ = ⇑(D.π.app j ≫ F.map (g e he))
        rw [D.w]
#align Top.is_topological_basis_cofiltered_limit TopCat.is_topological_basis_cofiltered_limit

end CofilteredLimit

section TopologicalKonig

/-!
## Topological Kőnig's lemma

A topological version of Kőnig's lemma is that the inverse limit of nonempty compact Hausdorff
spaces is nonempty.  (Note: this can be generalized further to inverse limits of nonempty compact
T0 spaces, where all the maps are closed maps; see [Stone1979] --- however there is an erratum
for Theorem 4 that the element in the inverse limit can have cofinally many components that are
not closed points.)

We give this in a more general form, which is that cofiltered limits
of nonempty compact Hausdorff spaces are nonempty
(`nonempty_limit_cone_of_compact_t2_cofiltered_system`).

This also applies to inverse limits, where `{J : Type u} [preorder J] [is_directed J (≤)]` and
`F : Jᵒᵖ ⥤ Top`.

The theorem is specialized to nonempty finite types (which are compact Hausdorff with the
discrete topology) in `nonempty_sections_of_fintype_cofiltered_system` and
`nonempty_sections_of_fintype_inverse_system`.

(See <https://stacks.math.columbia.edu/tag/086J> for the Set version.)
-/


variable {J : Type u} [SmallCategory J]

variable (F : J ⥤ TopCat.{u})

private abbrev finite_diagram_arrow {J : Type u} [SmallCategory J] (G : Finset J) :=
  Σ'(X Y : J)(mX : X ∈ G)(mY : Y ∈ G), X ⟶ Y
#align Top.finite_diagram_arrow Top.finite_diagram_arrow

private abbrev finite_diagram (J : Type u) [SmallCategory J] :=
  ΣG : Finset J, Finset (FiniteDiagramArrow G)
#align Top.finite_diagram Top.finite_diagram

/-- Partial sections of a cofiltered limit are sections when restricted to
a finite subset of objects and morphisms of `J`.
-/
def partialSections {J : Type u} [SmallCategory J] (F : J ⥤ TopCat.{u}) {G : Finset J}
    (H : Finset (FiniteDiagramArrow G)) : Set (∀ j, F.obj j) :=
  { u | ∀ {f : FiniteDiagramArrow G} (hf : f ∈ H), F.map f.2.2.2.2 (u f.1) = u f.2.1 }
#align Top.partial_sections TopCat.partialSections

theorem partialSections.nonempty [IsCofiltered J] [h : ∀ j : J, Nonempty (F.obj j)] {G : Finset J}
    (H : Finset (FiniteDiagramArrow G)) : (partialSections F H).Nonempty := by
  classical
    use fun j : J =>
      if hj : j ∈ G then F.map (is_cofiltered.inf_to G H hj) (h (is_cofiltered.inf G H)).some
      else (h _).some
    rintro ⟨X, Y, hX, hY, f⟩ hf
    dsimp only
    rwa [dif_pos hX, dif_pos hY, ← comp_app, ← F.map_comp, @is_cofiltered.inf_to_commutes _ _ _ G H]
#align Top.partial_sections.nonempty TopCat.partialSections.nonempty

theorem partialSections.directed :
    Directed Superset fun G : FiniteDiagram J => partialSections F G.2 := by
  classical
    intro A B
    let ιA : finite_diagram_arrow A.1 → finite_diagram_arrow (A.1 ⊔ B.1) := fun f =>
      ⟨f.1, f.2.1, Finset.mem_union_left _ f.2.2.1, Finset.mem_union_left _ f.2.2.2.1, f.2.2.2.2⟩
    let ιB : finite_diagram_arrow B.1 → finite_diagram_arrow (A.1 ⊔ B.1) := fun f =>
      ⟨f.1, f.2.1, Finset.mem_union_right _ f.2.2.1, Finset.mem_union_right _ f.2.2.2.1, f.2.2.2.2⟩
    refine' ⟨⟨A.1 ⊔ B.1, A.2.image ιA ⊔ B.2.image ιB⟩, _, _⟩
    · rintro u hu f hf
      have : ιA f ∈ A.2.image ιA ⊔ B.2.image ιB :=
        by
        apply Finset.mem_union_left
        rw [Finset.mem_image]
        refine' ⟨f, hf, rfl⟩
      exact hu this
    · rintro u hu f hf
      have : ιB f ∈ A.2.image ιA ⊔ B.2.image ιB :=
        by
        apply Finset.mem_union_right
        rw [Finset.mem_image]
        refine' ⟨f, hf, rfl⟩
      exact hu this
#align Top.partial_sections.directed TopCat.partialSections.directed

theorem partialSections.closed [∀ j : J, T2Space (F.obj j)] {G : Finset J}
    (H : Finset (FiniteDiagramArrow G)) : IsClosed (partialSections F H) :=
  by
  have :
    partial_sections F H =
      ⋂ (f : finite_diagram_arrow G) (hf : f ∈ H), { u | F.map f.2.2.2.2 (u f.1) = u f.2.1 } :=
    by
    ext1
    simp only [Set.mem_interᵢ, Set.mem_setOf_eq]
    rfl
  rw [this]
  apply is_closed_bInter
  intro f hf
  apply is_closed_eq
  continuity
#align Top.partial_sections.closed TopCat.partialSections.closed

/-- Cofiltered limits of nonempty compact Hausdorff spaces are nonempty topological spaces.
-/
theorem nonempty_limit_cone_of_compact_t2_cofiltered_system [IsCofiltered J]
    [∀ j : J, Nonempty (F.obj j)] [∀ j : J, CompactSpace (F.obj j)] [∀ j : J, T2Space (F.obj j)] :
    Nonempty (TopCat.limitCone.{u} F).x := by
  classical
    obtain ⟨u, hu⟩ :=
      IsCompact.nonempty_Inter_of_directed_nonempty_compact_closed (fun G => partial_sections F _)
        (partial_sections.directed F) (fun G => partial_sections.nonempty F _)
        (fun G => IsClosed.is_compact (partial_sections.closed F _)) fun G =>
        partial_sections.closed F _
    use u
    intro X Y f
    let G : finite_diagram J :=
      ⟨{X, Y},
        {⟨X, Y, by simp only [true_or_iff, eq_self_iff_true, Finset.mem_insert], by
            simp only [eq_self_iff_true, or_true_iff, Finset.mem_insert, Finset.mem_singleton], f⟩}⟩
    exact hu _ ⟨G, rfl⟩ (Finset.mem_singleton_self _)
#align
  Top.nonempty_limit_cone_of_compact_t2_cofiltered_system TopCat.nonempty_limit_cone_of_compact_t2_cofiltered_system

end TopologicalKonig

end TopCat

section FintypeKonig

/-- This bootstraps `nonempty_sections_of_fintype_inverse_system`. In this version,
the `F` functor is between categories of the same universe, and it is an easy
corollary to `Top.nonempty_limit_cone_of_compact_t2_inverse_system`. -/
theorem NonemptySectionsOfFintypeCofilteredSystem.init {J : Type u} [SmallCategory J]
    [IsCofiltered J] (F : J ⥤ Type u) [hf : ∀ j : J, Fintype (F.obj j)]
    [hne : ∀ j : J, Nonempty (F.obj j)] : F.sections.Nonempty :=
  by
  let F' : J ⥤ TopCat := F ⋙ TopCat.discrete
  haveI : ∀ j : J, Fintype (F'.obj j) := hf
  haveI : ∀ j : J, Nonempty (F'.obj j) := hne
  obtain ⟨⟨u, hu⟩⟩ := TopCat.nonempty_limit_cone_of_compact_t2_cofiltered_system F'
  exact ⟨u, fun _ _ f => hu f⟩
#align
  nonempty_sections_of_fintype_cofiltered_system.init NonemptySectionsOfFintypeCofilteredSystem.init

/-- The cofiltered limit of nonempty finite types is nonempty.

See `nonempty_sections_of_fintype_inverse_system` for a specialization to inverse limits. -/
theorem nonempty_sections_of_fintype_cofiltered_system {J : Type u} [Category.{w} J]
    [IsCofiltered J] (F : J ⥤ Type v) [∀ j : J, Fintype (F.obj j)] [∀ j : J, Nonempty (F.obj j)] :
    F.sections.Nonempty :=
  by
  -- Step 1: lift everything to the `max u v w` universe.
  let J' : Type max w v u := AsSmall.{max w v} J
  let down : J' ⥤ J := as_small.down
  let F' : J' ⥤ Type max u v w := down ⋙ F ⋙ ulift_functor.{max u w, v}
  haveI : ∀ i, Nonempty (F'.obj i) := fun i => ⟨⟨Classical.arbitrary (F.obj (down.obj i))⟩⟩
  haveI : ∀ i, Fintype (F'.obj i) := fun i => Fintype.ofEquiv (F.obj (down.obj i)) equiv.ulift.symm
  -- Step 2: apply the bootstrap theorem
  obtain ⟨u, hu⟩ := NonemptySectionsOfFintypeCofilteredSystem.init F'
  -- Step 3: interpret the results
  use fun j => (u ⟨j⟩).down
  intro j j' f
  have h := @hu (⟨j⟩ : J') (⟨j'⟩ : J') (ULift.up f)
  simp only [as_small.down, functor.comp_map, ulift_functor_map, functor.op_map] at h
  simp_rw [← h]
  rfl
#align nonempty_sections_of_fintype_cofiltered_system nonempty_sections_of_fintype_cofiltered_system

/-- The inverse limit of nonempty finite types is nonempty.

See `nonempty_sections_of_fintype_cofiltered_system` for a generalization to cofiltered limits.
That version applies in almost all cases, and the only difference is that this version
allows `J` to be empty.

This may be regarded as a generalization of Kőnig's lemma.
To specialize: given a locally finite connected graph, take `Jᵒᵖ` to be `ℕ` and
`F j` to be length-`j` paths that start from an arbitrary fixed vertex.
Elements of `F.sections` can be read off as infinite rays in the graph. -/
theorem nonempty_sections_of_fintype_inverse_system {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)]
    (F : Jᵒᵖ ⥤ Type v) [∀ j : Jᵒᵖ, Fintype (F.obj j)] [∀ j : Jᵒᵖ, Nonempty (F.obj j)] :
    F.sections.Nonempty := by
  cases isEmpty_or_nonempty J
  · haveI : IsEmpty Jᵒᵖ := ⟨fun j => isEmptyElim j.unop⟩
    -- TODO: this should be a global instance
    exact ⟨isEmptyElim, isEmptyElim⟩
  · exact nonempty_sections_of_fintype_cofiltered_system _
#align nonempty_sections_of_fintype_inverse_system nonempty_sections_of_fintype_inverse_system

end FintypeKonig

