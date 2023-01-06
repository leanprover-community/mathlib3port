/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module algebraic_geometry.presheafed_space.gluing
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Gluing
import Mathbin.AlgebraicGeometry.OpenImmersion
import Mathbin.AlgebraicGeometry.LocallyRingedSpace.HasColimits

/-!
# Gluing Structured spaces

Given a family of gluing data of structured spaces (presheafed spaces, sheafed spaces, or locally
ringed spaces), we may glue them together.

The construction should be "sealed" and considered as a black box, while only using the API
provided.

## Main definitions

* `algebraic_geometry.PresheafedSpace.glue_data`: A structure containing the family of gluing data.
* `category_theory.glue_data.glued`: The glued presheafed space.
    This is defined as the multicoequalizer of `∐ V i j ⇉ ∐ U i`, so that the general colimit API
    can be used.
* `category_theory.glue_data.ι`: The immersion `ι i : U i ⟶ glued` for each `i : J`.

## Main results

* `algebraic_geometry.PresheafedSpace.glue_data.ι_is_open_immersion`: The map `ι i : U i ⟶ glued`
  is an open immersion for each `i : J`.
* `algebraic_geometry.PresheafedSpace.glue_data.ι_jointly_surjective` : The underlying maps of
  `ι i : U i ⟶ glued` are jointly surjective.
* `algebraic_geometry.PresheafedSpace.glue_data.V_pullback_cone_is_limit` : `V i j` is the pullback
  (intersection) of `U i` and `U j` over the glued space.

Analogous results are also provided for `SheafedSpace` and `LocallyRingedSpace`.

## Implementation details

Almost the whole file is dedicated to showing tht `ι i` is an open immersion. The fact that
this is an open embedding of topological spaces follows from `topology.gluing.lean`, and it remains
to construct `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_X, ι i '' U)` for each `U ⊆ U i`.
Since `Γ(𝒪_X, ι i '' U)` is the the limit of `diagram_over_open`, the components of the structure
sheafs of the spaces in the gluing diagram, we need to construct a map
`ι_inv_app_π_app : Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_V, U_V)` for each `V` in the gluing diagram.

We will refer to ![this diagram](https://i.imgur.com/P0phrwr.png) in the following doc strings.
The `X` is the glued space, and the dotted arrow is a partial inverse guaranteed by the fact
that it is an open immersion. The map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_{U_j}, _)` is given by the composition
of the red arrows, and the map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_{V_{jk}}, _)` is given by the composition of the
blue arrows. To lift this into a map from `Γ(𝒪_X, ι i '' U)`, we also need to show that these
commute with the maps in the diagram (the green arrows), which is just a lengthy diagram-chasing.

-/


noncomputable section

open TopologicalSpace CategoryTheory Opposite

open CategoryTheory.Limits AlgebraicGeometry.PresheafedSpaceCat

open CategoryTheory.GlueData

namespace AlgebraicGeometry

universe v u

variable (C : Type u) [Category.{v} C]

namespace PresheafedSpaceCat

/-- A family of gluing data consists of
1. An index type `J`
2. A presheafed space `U i` for each `i : J`.
3. A presheafed space `V i j` for each `i j : J`.
  (Note that this is `J × J → PresheafedSpace C` rather than `J → J → PresheafedSpace C` to
  connect to the limits library easier.)
4. An open immersion `f i j : V i j ⟶ U i` for each `i j : ι`.
5. A transition map `t i j : V i j ⟶ V j i` for each `i j : ι`.
such that
6. `f i i` is an isomorphism.
7. `t i i` is the identity.
8. `V i j ×[U i] V i k ⟶ V i j ⟶ V j i` factors through `V j k ×[U j] V j i ⟶ V j i` via some
    `t' : V i j ×[U i] V i k ⟶ V j k ×[U j] V j i`.
9. `t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _`.

We can then glue the spaces `U i` together by identifying `V i j` with `V j i`, such
that the `U i`'s are open subspaces of the glued space.
-/
@[nolint has_nonempty_instance]
structure GlueData extends GlueData (PresheafedSpaceCat.{v} C) where
  f_open : ∀ i j, IsOpenImmersion (f i j)
#align algebraic_geometry.PresheafedSpace.glue_data AlgebraicGeometry.PresheafedSpaceCat.GlueData

attribute [instance] glue_data.f_open

namespace GlueData

variable {C} (D : GlueData C)

-- mathport name: «expr𝖣»
local notation "𝖣" => D.toGlueData

-- mathport name: «exprπ₁ , , »
local notation "π₁ " i ", " j ", " k => @pullback.fst _ _ _ _ _ (D.f i j) (D.f i k) _

-- mathport name: «exprπ₂ , , »
local notation "π₂ " i ", " j ", " k => @pullback.snd _ _ _ _ _ (D.f i j) (D.f i k) _

-- mathport name: «exprπ₁⁻¹ , , »
local notation "π₁⁻¹ " i ", " j ", " k =>
  (PresheafedSpaceCat.IsOpenImmersion.pullbackFstOfRight (D.f i j) (D.f i k)).invApp

-- mathport name: «exprπ₂⁻¹ , , »
local notation "π₂⁻¹ " i ", " j ", " k =>
  (PresheafedSpaceCat.IsOpenImmersion.pullbackSndOfLeft (D.f i j) (D.f i k)).invApp

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The glue data of topological spaces associated to a family of glue data of PresheafedSpaces. -/")]
      []
      []
      []
      []
      [])
     (Command.abbrev
      "abbrev"
      (Command.declId `toTopGlueData [])
      (Command.optDeclSig [] [(Term.typeSpec ":" `TopCat.GlueData)])
      (Command.declValSimple
       ":="
       (Term.structInst
        "{"
        []
        [(Term.structInstField
          (Term.structInstLVal `f_open [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`i `j]
            []
            "=>"
            (Term.proj (Term.app (Term.proj `D "." `f_open) [`i `j]) "." `base_open))))
         []
         (Term.structInstField
          (Term.structInstLVal `toGlueData [])
          ":="
          (Term.app
           (Term.proj
            (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
             "𝖣")
            "."
            `mapGlueData)
           [(Term.app `forget [`C])]))]
        (Term.optEllipsis [])
        []
        "}")
       [])
      []
      []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       []
       [(Term.structInstField
         (Term.structInstLVal `f_open [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`i `j]
           []
           "=>"
           (Term.proj (Term.app (Term.proj `D "." `f_open) [`i `j]) "." `base_open))))
        []
        (Term.structInstField
         (Term.structInstLVal `toGlueData [])
         ":="
         (Term.app
          (Term.proj
           (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
            "𝖣")
           "."
           `mapGlueData)
          [(Term.app `forget [`C])]))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
         "𝖣")
        "."
        `mapGlueData)
       [(Term.app `forget [`C])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `forget [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `forget
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `forget [`C]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
        "𝖣")
       "."
       `mapGlueData)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
       "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»', expected 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.term𝖣._@.AlgebraicGeometry.PresheafedSpace.Gluing._hyg.31'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The glue data of topological spaces associated to a family of glue data of PresheafedSpaces. -/
  abbrev
    toTopGlueData
    : TopCat.GlueData
    := { f_open := fun i j => D . f_open i j . base_open toGlueData := 𝖣 . mapGlueData forget C }
#align
  algebraic_geometry.PresheafedSpace.glue_data.to_Top_glue_data AlgebraicGeometry.PresheafedSpaceCat.GlueData.toTopGlueData

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `ι_open_embedding [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `HasLimits [`C]) "]")
        (Term.explicitBinder "(" [`i] [":" (Term.proj `D "." `J)] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `OpenEmbedding
         [(Term.proj
           (Term.app
            (Term.proj
             (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
              "𝖣")
             "."
             `ι)
            [`i])
           "."
           `base)])))
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
               (Term.show
                "show"
                («term_=_»
                 (Term.hole "_")
                 "="
                 (Term.proj
                  (Term.app
                   (Term.proj
                    (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                     "𝖣")
                    "."
                    `ι)
                   [`i])
                  "."
                  `base))
                (Term.fromTerm
                 "from"
                 (Term.app
                  (Term.proj
                   (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                    "𝖣")
                   "."
                   `ι_glued_iso_inv)
                  [(Term.app `PresheafedSpace.forget [(Term.hole "_")]) (Term.hole "_")]))))]
             "]")
            [])
           []
           (Tactic.exact
            "exact"
            (Term.app
             `OpenEmbedding.comp
             [(Term.proj
               (Term.app
                `TopCat.homeoOfIso
                [(Term.proj
                  (Term.app
                   (Term.proj
                    (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                     "𝖣")
                    "."
                    `gluedIso)
                   [(Term.app `PresheafedSpace.forget [(Term.hole "_")])])
                  "."
                  `symm)])
               "."
               `OpenEmbedding)
              (Term.app `D.to_Top_glue_data.ι_open_embedding [`i])]))])))
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
              (Term.show
               "show"
               («term_=_»
                (Term.hole "_")
                "="
                (Term.proj
                 (Term.app
                  (Term.proj
                   (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                    "𝖣")
                   "."
                   `ι)
                  [`i])
                 "."
                 `base))
               (Term.fromTerm
                "from"
                (Term.app
                 (Term.proj
                  (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                   "𝖣")
                  "."
                  `ι_glued_iso_inv)
                 [(Term.app `PresheafedSpace.forget [(Term.hole "_")]) (Term.hole "_")]))))]
            "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            `OpenEmbedding.comp
            [(Term.proj
              (Term.app
               `TopCat.homeoOfIso
               [(Term.proj
                 (Term.app
                  (Term.proj
                   (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                    "𝖣")
                   "."
                   `gluedIso)
                  [(Term.app `PresheafedSpace.forget [(Term.hole "_")])])
                 "."
                 `symm)])
              "."
              `OpenEmbedding)
             (Term.app `D.to_Top_glue_data.ι_open_embedding [`i])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `OpenEmbedding.comp
        [(Term.proj
          (Term.app
           `TopCat.homeoOfIso
           [(Term.proj
             (Term.app
              (Term.proj
               (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                "𝖣")
               "."
               `gluedIso)
              [(Term.app `PresheafedSpace.forget [(Term.hole "_")])])
             "."
             `symm)])
          "."
          `OpenEmbedding)
         (Term.app `D.to_Top_glue_data.ι_open_embedding [`i])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `OpenEmbedding.comp
       [(Term.proj
         (Term.app
          `TopCat.homeoOfIso
          [(Term.proj
            (Term.app
             (Term.proj
              (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
               "𝖣")
              "."
              `gluedIso)
             [(Term.app `PresheafedSpace.forget [(Term.hole "_")])])
            "."
            `symm)])
         "."
         `OpenEmbedding)
        (Term.app `D.to_Top_glue_data.ι_open_embedding [`i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `D.to_Top_glue_data.ι_open_embedding [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `D.to_Top_glue_data.ι_open_embedding
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `D.to_Top_glue_data.ι_open_embedding [`i])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.app
        `TopCat.homeoOfIso
        [(Term.proj
          (Term.app
           (Term.proj
            (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
             "𝖣")
            "."
            `gluedIso)
           [(Term.app `PresheafedSpace.forget [(Term.hole "_")])])
          "."
          `symm)])
       "."
       `OpenEmbedding)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `TopCat.homeoOfIso
       [(Term.proj
         (Term.app
          (Term.proj
           (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
            "𝖣")
           "."
           `gluedIso)
          [(Term.app `PresheafedSpace.forget [(Term.hole "_")])])
         "."
         `symm)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        (Term.proj
         (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
          "𝖣")
         "."
         `gluedIso)
        [(Term.app `PresheafedSpace.forget [(Term.hole "_")])])
       "."
       `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
         "𝖣")
        "."
        `gluedIso)
       [(Term.app `PresheafedSpace.forget [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `PresheafedSpace.forget [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `PresheafedSpace.forget
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `PresheafedSpace.forget [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
        "𝖣")
       "."
       `gluedIso)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
       "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»', expected 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.term𝖣._@.AlgebraicGeometry.PresheafedSpace.Gluing._hyg.31'
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
  ι_open_embedding
  [ HasLimits C ] ( i : D . J ) : OpenEmbedding 𝖣 . ι i . base
  :=
    by
      rw [ ← show _ = 𝖣 . ι i . base from 𝖣 . ι_glued_iso_inv PresheafedSpace.forget _ _ ]
        exact
          OpenEmbedding.comp
            TopCat.homeoOfIso 𝖣 . gluedIso PresheafedSpace.forget _ . symm . OpenEmbedding
              D.to_Top_glue_data.ι_open_embedding i
#align
  algebraic_geometry.PresheafedSpace.glue_data.ι_open_embedding AlgebraicGeometry.PresheafedSpaceCat.GlueData.ι_open_embedding

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `pullback_base [])
      (Command.declSig
       [(Term.explicitBinder "(" [`i `j `k] [":" (Term.proj `D "." `J)] [] ")")
        (Term.explicitBinder
         "("
         [`S]
         [":"
          (Term.app
           `Set
           [(Term.proj
             (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`i "," [`j]] ")")])
             "."
             `carrier)])]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Set.Data.Set.Image.term_''_
          (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₂_,_,_»
           "π₂ "
           `i
           ", "
           `j
           ", "
           `k)
          " '' "
          (Set.Data.Set.Image.«term_⁻¹'_»
           (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁_,_,_»
            "π₁ "
            `i
            ", "
            `j
            ", "
            `k)
           " ⁻¹' "
           `S))
         "="
         (Set.Data.Set.Image.«term_⁻¹'_»
          (Term.app (Term.proj `D "." `f) [`i `k])
          " ⁻¹' "
          (Set.Data.Set.Image.term_''_ (Term.app (Term.proj `D "." `f) [`i `j]) " '' " `S)))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`eq₁ []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Term.hole "_")
                 "="
                 (Term.proj
                  (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁_,_,_»
                   "π₁ "
                   `i
                   ", "
                   `j
                   ", "
                   `k)
                  "."
                  `base)))]
              ":="
              (Term.app
               `preserves_pullback.iso_hom_fst
               [(Term.app `forget [`C]) (Term.hole "_") (Term.hole "_")]))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`eq₂ []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Term.hole "_")
                 "="
                 (Term.proj
                  (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₂_,_,_»
                   "π₂ "
                   `i
                   ", "
                   `j
                   ", "
                   `k)
                  "."
                  `base)))]
              ":="
              (Term.app
               `preserves_pullback.iso_hom_snd
               [(Term.app `forget [`C]) (Term.hole "_") (Term.hole "_")]))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `coe_to_fun_eq)
              ","
              (Tactic.rwRule [] `coe_to_fun_eq)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eq₁)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eq₂)
              ","
              (Tactic.rwRule [] `coe_comp)
              ","
              (Tactic.rwRule [] `Set.image_comp)
              ","
              (Tactic.rwRule [] `coe_comp)
              ","
              (Tactic.rwRule [] `Set.preimage_comp)
              ","
              (Tactic.rwRule [] `Set.image_preimage_eq)
              ","
              (Tactic.rwRule [] `TopCat.pullback_snd_image_fst_preimage)]
             "]")
            [])
           []
           (Tactic.tacticRfl "rfl")
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `TopCat.epi_iff_surjective)]
             "]")
            [])
           []
           (Tactic.tacticInfer_instance "infer_instance")])))
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
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`eq₁ []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.hole "_")
                "="
                (Term.proj
                 (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁_,_,_»
                  "π₁ "
                  `i
                  ", "
                  `j
                  ", "
                  `k)
                 "."
                 `base)))]
             ":="
             (Term.app
              `preserves_pullback.iso_hom_fst
              [(Term.app `forget [`C]) (Term.hole "_") (Term.hole "_")]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`eq₂ []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.hole "_")
                "="
                (Term.proj
                 (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₂_,_,_»
                  "π₂ "
                  `i
                  ", "
                  `j
                  ", "
                  `k)
                 "."
                 `base)))]
             ":="
             (Term.app
              `preserves_pullback.iso_hom_snd
              [(Term.app `forget [`C]) (Term.hole "_") (Term.hole "_")]))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `coe_to_fun_eq)
             ","
             (Tactic.rwRule [] `coe_to_fun_eq)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eq₁)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eq₂)
             ","
             (Tactic.rwRule [] `coe_comp)
             ","
             (Tactic.rwRule [] `Set.image_comp)
             ","
             (Tactic.rwRule [] `coe_comp)
             ","
             (Tactic.rwRule [] `Set.preimage_comp)
             ","
             (Tactic.rwRule [] `Set.image_preimage_eq)
             ","
             (Tactic.rwRule [] `TopCat.pullback_snd_image_fst_preimage)]
            "]")
           [])
          []
          (Tactic.tacticRfl "rfl")
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `TopCat.epi_iff_surjective)]
            "]")
           [])
          []
          (Tactic.tacticInfer_instance "infer_instance")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticInfer_instance "infer_instance")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `TopCat.epi_iff_surjective)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `TopCat.epi_iff_surjective
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `coe_to_fun_eq)
         ","
         (Tactic.rwRule [] `coe_to_fun_eq)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eq₁)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eq₂)
         ","
         (Tactic.rwRule [] `coe_comp)
         ","
         (Tactic.rwRule [] `Set.image_comp)
         ","
         (Tactic.rwRule [] `coe_comp)
         ","
         (Tactic.rwRule [] `Set.preimage_comp)
         ","
         (Tactic.rwRule [] `Set.image_preimage_eq)
         ","
         (Tactic.rwRule [] `TopCat.pullback_snd_image_fst_preimage)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `TopCat.pullback_snd_image_fst_preimage
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.image_preimage_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.preimage_comp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_comp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.image_comp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_comp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_to_fun_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_to_fun_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`eq₂ []]
         [(Term.typeSpec
           ":"
           («term_=_»
            (Term.hole "_")
            "="
            (Term.proj
             (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₂_,_,_»
              "π₂ "
              `i
              ", "
              `j
              ", "
              `k)
             "."
             `base)))]
         ":="
         (Term.app
          `preserves_pullback.iso_hom_snd
          [(Term.app `forget [`C]) (Term.hole "_") (Term.hole "_")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `preserves_pullback.iso_hom_snd
       [(Term.app `forget [`C]) (Term.hole "_") (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `forget [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `forget
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `forget [`C]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `preserves_pullback.iso_hom_snd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       (Term.proj
        (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₂_,_,_»
         "π₂ "
         `i
         ", "
         `j
         ", "
         `k)
        "."
        `base))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₂_,_,_»
        "π₂ "
        `i
        ", "
        `j
        ", "
        `k)
       "."
       `base)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₂_,_,_»
       "π₂ "
       `i
       ", "
       `j
       ", "
       `k)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₂_,_,_»', expected 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.termπ₂_,_,_._@.AlgebraicGeometry.PresheafedSpace.Gluing._hyg.149'
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
  pullback_base
  ( i j k : D . J ) ( S : Set D . V ( i , j ) . carrier )
    : π₂ i , j , k '' π₁ i , j , k ⁻¹' S = D . f i k ⁻¹' D . f i j '' S
  :=
    by
      have eq₁ : _ = π₁ i , j , k . base := preserves_pullback.iso_hom_fst forget C _ _
        have eq₂ : _ = π₂ i , j , k . base := preserves_pullback.iso_hom_snd forget C _ _
        rw
          [
            coe_to_fun_eq
              ,
              coe_to_fun_eq
              ,
              ← eq₁
              ,
              ← eq₂
              ,
              coe_comp
              ,
              Set.image_comp
              ,
              coe_comp
              ,
              Set.preimage_comp
              ,
              Set.image_preimage_eq
              ,
              TopCat.pullback_snd_image_fst_preimage
            ]
        rfl
        rw [ ← TopCat.epi_iff_surjective ]
        infer_instance
#align
  algebraic_geometry.PresheafedSpace.glue_data.pullback_base AlgebraicGeometry.PresheafedSpaceCat.GlueData.pullback_base

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The red and the blue arrows in ![this diagram](https://i.imgur.com/0GiBUh6.png) commute. -/")]
      [(Term.attributes
        "@["
        [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))
         ","
         (Term.attrInstance
          (Term.attrKind [])
          (Attr.simple `reassoc._@.AlgebraicGeometry.PresheafedSpace.Gluing._hyg.1 []))]
        "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `f_inv_app_f_app [])
      (Command.declSig
       [(Term.explicitBinder "(" [`i `j `k] [":" (Term.proj `D "." `J)] [] ")")
        (Term.explicitBinder
         "("
         [`U]
         [":"
          (Term.app
           `Opens
           [(Term.proj
             (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`i "," [`j]] ")")])
             "."
             `carrier)])]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app (Term.proj (Term.app (Term.proj `D "." `f_open) [`i `j]) "." `invApp) [`U])
          " ≫ "
          (Term.app
           (Term.proj (Term.proj (Term.app (Term.proj `D "." `f) [`i `k]) "." `c) "." `app)
           [(Term.hole "_")]))
         "="
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app
           (Term.proj
            (Term.proj
             (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁_,_,_»
              "π₁ "
              `i
              ", "
              `j
              ", "
              `k)
             "."
             `c)
            "."
            `app)
           [(Term.app `op [`U])])
          " ≫ "
          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
           (Term.app
            (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₂⁻¹_,_,_»
             "π₂⁻¹ "
             `i
             ", "
             `j
             ", "
             `k)
            [(Term.app `unop [(Term.hole "_")])])
           " ≫ "
           (Term.app
            (Term.proj
             (Term.proj (Term.app (Term.proj `D "." `V) [(Term.hole "_")]) "." `Presheaf)
             "."
             `map)
            [(Term.app
              `eqToHom
              [(Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.delta "delta" [`is_open_immersion.open_functor] [])
                   []
                   (Tactic.dsimp
                    "dsimp"
                    []
                    []
                    ["only"]
                    ["["
                     [(Tactic.simpLemma [] [] `functor.op)
                      ","
                      (Tactic.simpLemma [] [] `IsOpenMap.functor)
                      ","
                      (Tactic.simpLemma [] [] `opens.map)
                      ","
                      (Tactic.simpLemma [] [] `unop_op)]
                     "]"]
                    [])
                   []
                   (Tactic.congr "congr" [])
                   []
                   (Tactic.apply "apply" `pullback_base)])))])]))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              []
              ":="
              (Term.app
               `PresheafedSpace.congr_app
               [(Term.app
                 (Term.explicit "@" `pullback.condition)
                 [(Term.hole "_")
                  (Term.hole "_")
                  (Term.hole "_")
                  (Term.hole "_")
                  (Term.hole "_")
                  (Term.app `D.f [`i `j])
                  (Term.app `D.f [`i `k])
                  (Term.hole "_")])]))))
           []
           (Tactic.dsimp
            "dsimp"
            []
            []
            ["only"]
            ["[" [(Tactic.simpLemma [] [] `comp_c_app)] "]"]
            [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app
                `cancel_epi
                [(Term.app
                  `inv
                  [(Term.app (Term.proj (Term.app `D.f_open [`i `j]) "." `invApp) [`U])])]))
              ","
              (Tactic.rwRule [] `is_iso.inv_hom_id_assoc)
              ","
              (Tactic.rwRule [] `is_open_immersion.inv_inv_app)]
             "]")
            [])
           []
           (Mathlib.Tactic.tacticSimp_rw__
            "simp_rw"
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
            [])
           []
           (Tactic.tacticErw__
            "erw"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               []
               (Term.proj
                (Term.proj
                 (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁_,_,_»
                  "π₁ "
                  `i
                  ", "
                  `j
                  ", "
                  `k)
                 "."
                 `c)
                "."
                `naturality_assoc))
              ","
              (Tactic.rwRule [] (Term.app `reassoc_of [`this]))
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `functor.map_comp_assoc)
              ","
              (Tactic.rwRule [] `is_open_immersion.inv_naturality_assoc)
              ","
              (Tactic.rwRule [] `is_open_immersion.app_inv_app_assoc)
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.proj
                (Term.proj (Term.app `D.V [(Term.tuple "(" [`i "," [`k]] ")")]) "." `Presheaf)
                "."
                `map_comp))
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.proj
                (Term.proj (Term.app `D.V [(Term.tuple "(" [`i "," [`k]] ")")]) "." `Presheaf)
                "."
                `map_comp))]
             "]")
            [])
           []
           (convert
            "convert"
            []
            (Term.proj (Term.app `category.comp_id [(Term.hole "_")]) "." `symm)
            [])
           []
           (Tactic.tacticErw__
            "erw"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               []
               (Term.proj
                (Term.proj (Term.app `D.V [(Term.tuple "(" [`i "," [`k]] ")")]) "." `Presheaf)
                "."
                `map_id))]
             "]")
            [])
           []
           (Tactic.tacticRfl "rfl")])))
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
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             []
             ":="
             (Term.app
              `PresheafedSpace.congr_app
              [(Term.app
                (Term.explicit "@" `pullback.condition)
                [(Term.hole "_")
                 (Term.hole "_")
                 (Term.hole "_")
                 (Term.hole "_")
                 (Term.hole "_")
                 (Term.app `D.f [`i `j])
                 (Term.app `D.f [`i `k])
                 (Term.hole "_")])]))))
          []
          (Tactic.dsimp
           "dsimp"
           []
           []
           ["only"]
           ["[" [(Tactic.simpLemma [] [] `comp_c_app)] "]"]
           [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app
               `cancel_epi
               [(Term.app
                 `inv
                 [(Term.app (Term.proj (Term.app `D.f_open [`i `j]) "." `invApp) [`U])])]))
             ","
             (Tactic.rwRule [] `is_iso.inv_hom_id_assoc)
             ","
             (Tactic.rwRule [] `is_open_immersion.inv_inv_app)]
            "]")
           [])
          []
          (Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
           [])
          []
          (Tactic.tacticErw__
           "erw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.proj
               (Term.proj
                (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁_,_,_»
                 "π₁ "
                 `i
                 ", "
                 `j
                 ", "
                 `k)
                "."
                `c)
               "."
               `naturality_assoc))
             ","
             (Tactic.rwRule [] (Term.app `reassoc_of [`this]))
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `functor.map_comp_assoc)
             ","
             (Tactic.rwRule [] `is_open_immersion.inv_naturality_assoc)
             ","
             (Tactic.rwRule [] `is_open_immersion.app_inv_app_assoc)
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.proj
               (Term.proj (Term.app `D.V [(Term.tuple "(" [`i "," [`k]] ")")]) "." `Presheaf)
               "."
               `map_comp))
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.proj
               (Term.proj (Term.app `D.V [(Term.tuple "(" [`i "," [`k]] ")")]) "." `Presheaf)
               "."
               `map_comp))]
            "]")
           [])
          []
          (convert
           "convert"
           []
           (Term.proj (Term.app `category.comp_id [(Term.hole "_")]) "." `symm)
           [])
          []
          (Tactic.tacticErw__
           "erw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.proj
               (Term.proj (Term.app `D.V [(Term.tuple "(" [`i "," [`k]] ")")]) "." `Presheaf)
               "."
               `map_id))]
            "]")
           [])
          []
          (Tactic.tacticRfl "rfl")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticErw__
       "erw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          []
          (Term.proj
           (Term.proj (Term.app `D.V [(Term.tuple "(" [`i "," [`k]] ")")]) "." `Presheaf)
           "."
           `map_id))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.proj (Term.app `D.V [(Term.tuple "(" [`i "," [`k]] ")")]) "." `Presheaf)
       "."
       `map_id)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app `D.V [(Term.tuple "(" [`i "," [`k]] ")")]) "." `Presheaf)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `D.V [(Term.tuple "(" [`i "," [`k]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`i "," [`k]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `D.V
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `D.V [(Term.tuple "(" [`i "," [`k]] ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert "convert" [] (Term.proj (Term.app `category.comp_id [(Term.hole "_")]) "." `symm) [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `category.comp_id [(Term.hole "_")]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `category.comp_id [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `category.comp_id
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `category.comp_id [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticErw__
       "erw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          []
          (Term.proj
           (Term.proj
            (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁_,_,_»
             "π₁ "
             `i
             ", "
             `j
             ", "
             `k)
            "."
            `c)
           "."
           `naturality_assoc))
         ","
         (Tactic.rwRule [] (Term.app `reassoc_of [`this]))
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `functor.map_comp_assoc)
         ","
         (Tactic.rwRule [] `is_open_immersion.inv_naturality_assoc)
         ","
         (Tactic.rwRule [] `is_open_immersion.app_inv_app_assoc)
         ","
         (Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.proj
           (Term.proj (Term.app `D.V [(Term.tuple "(" [`i "," [`k]] ")")]) "." `Presheaf)
           "."
           `map_comp))
         ","
         (Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.proj
           (Term.proj (Term.app `D.V [(Term.tuple "(" [`i "," [`k]] ")")]) "." `Presheaf)
           "."
           `map_comp))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.proj (Term.app `D.V [(Term.tuple "(" [`i "," [`k]] ")")]) "." `Presheaf)
       "."
       `map_comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app `D.V [(Term.tuple "(" [`i "," [`k]] ")")]) "." `Presheaf)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `D.V [(Term.tuple "(" [`i "," [`k]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`i "," [`k]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `D.V
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `D.V [(Term.tuple "(" [`i "," [`k]] ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.proj (Term.app `D.V [(Term.tuple "(" [`i "," [`k]] ")")]) "." `Presheaf)
       "."
       `map_comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app `D.V [(Term.tuple "(" [`i "," [`k]] ")")]) "." `Presheaf)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `D.V [(Term.tuple "(" [`i "," [`k]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`i "," [`k]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `D.V
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `D.V [(Term.tuple "(" [`i "," [`k]] ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `is_open_immersion.app_inv_app_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `is_open_immersion.inv_naturality_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `functor.map_comp_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `reassoc_of [`this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `reassoc_of
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.proj
        (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁_,_,_»
         "π₁ "
         `i
         ", "
         `j
         ", "
         `k)
        "."
        `c)
       "."
       `naturality_assoc)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁_,_,_»
        "π₁ "
        `i
        ", "
        `j
        ", "
        `k)
       "."
       `c)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁_,_,_»
       "π₁ "
       `i
       ", "
       `j
       ", "
       `k)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁_,_,_»', expected 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.termπ₁_,_,_._@.AlgebraicGeometry.PresheafedSpace.Gluing._hyg.78'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The red and the blue arrows in ![this diagram](https://i.imgur.com/0GiBUh6.png) commute. -/
    @[ simp , reassoc ]
  theorem
    f_inv_app_f_app
    ( i j k : D . J ) ( U : Opens D . V ( i , j ) . carrier )
      :
        D . f_open i j . invApp U ≫ D . f i k . c . app _
          =
          π₁ i , j , k . c . app op U
            ≫
            π₂⁻¹ i , j , k unop _
              ≫
              D . V _ . Presheaf . map
                eqToHom
                  by
                    delta is_open_immersion.open_functor
                      dsimp only [ functor.op , IsOpenMap.functor , opens.map , unop_op ]
                      congr
                      apply pullback_base
    :=
      by
        have := PresheafedSpace.congr_app @ pullback.condition _ _ _ _ _ D.f i j D.f i k _
          dsimp only [ comp_c_app ] at this
          rw
            [
              ← cancel_epi inv D.f_open i j . invApp U
                ,
                is_iso.inv_hom_id_assoc
                ,
                is_open_immersion.inv_inv_app
              ]
          simp_rw [ category.assoc ]
          erw
            [
              π₁ i , j , k . c . naturality_assoc
                ,
                reassoc_of this
                ,
                ← functor.map_comp_assoc
                ,
                is_open_immersion.inv_naturality_assoc
                ,
                is_open_immersion.app_inv_app_assoc
                ,
                ← D.V ( i , k ) . Presheaf . map_comp
                ,
                ← D.V ( i , k ) . Presheaf . map_comp
              ]
          convert category.comp_id _ . symm
          erw [ D.V ( i , k ) . Presheaf . map_id ]
          rfl
#align
  algebraic_geometry.PresheafedSpace.glue_data.f_inv_app_f_app AlgebraicGeometry.PresheafedSpaceCat.GlueData.f_inv_app_f_app

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "We can prove the `eq` along with the lemma. Thus this is bundled together here, and the\nlemma itself is separated below.\n-/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `snd_inv_app_t_app' [])
      (Command.declSig
       [(Term.explicitBinder "(" [`i `j `k] [":" (Term.proj `D "." `J)] [] ")")
        (Term.explicitBinder
         "("
         [`U]
         [":"
          (Term.app
           `Opens
           [(Term.proj
             (Term.app
              `pullback
              [(Term.app (Term.proj `D "." `f) [`i `j]) (Term.app (Term.proj `D "." `f) [`i `k])])
             "."
             `carrier)])]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `eq)] []))
         ","
         («term_=_»
          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
           (Term.app
            (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₂⁻¹_,_,_»
             "π₂⁻¹ "
             `i
             ", "
             `j
             ", "
             `k)
            [`U])
           " ≫ "
           (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
            (Term.app
             (Term.proj (Term.proj (Term.app (Term.proj `D "." `t) [`k `i]) "." `c) "." `app)
             [(Term.hole "_")])
            " ≫ "
            (Term.app
             (Term.proj
              (Term.proj
               (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`k "," [`i]] ")")])
               "."
               `Presheaf)
              "."
              `map)
             [(Term.app `eqToHom [`Eq])])))
          "="
          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
           (Term.app
            (Term.proj (Term.proj (Term.app (Term.proj `D "." `t') [`k `i `j]) "." `c) "." `app)
            [(Term.hole "_")])
           " ≫ "
           (Term.app
            (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁⁻¹_,_,_»
             "π₁⁻¹ "
             `k
             ", "
             `j
             ", "
             `i)
            [(Term.app `unop [(Term.hole "_")])]))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.constructor "constructor")
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `is_iso.eq_inv_comp)
              ","
              (Tactic.rwRule [] `is_open_immersion.inv_inv_app)
              ","
              (Tactic.rwRule [] `category.assoc)
              ","
              (Tactic.rwRule
               []
               (Term.proj (Term.proj (Term.app `D.t' [`k `i `j]) "." `c) "." `naturality_assoc))]
             "]")
            [])
           []
           (Mathlib.Tactic.tacticSimp_rw__
            "simp_rw"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `category.assoc)]
             "]")
            [])
           []
           (Tactic.tacticErw__
            "erw"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `comp_c_app)]
             "]")
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] (Term.app `congr_app [(Term.app `D.t_fac [`k `i `j])]))
              ","
              (Tactic.rwRule [] `comp_c_app)]
             "]")
            [])
           []
           (Mathlib.Tactic.tacticSimp_rw__
            "simp_rw"
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
            [])
           []
           (Tactic.tacticErw__
            "erw"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `is_open_immersion.inv_naturality)
              ","
              (Tactic.rwRule [] `is_open_immersion.inv_naturality_assoc)
              ","
              (Tactic.rwRule [] `is_open_immersion.app_inv_app'_assoc)]
             "]")
            [])
           []
           (Mathlib.Tactic.tacticSimp_rw__
            "simp_rw"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.proj
                (Term.proj
                 (Term.app
                  (Term.proj
                   (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                    "𝖣")
                   "."
                   `V)
                  [(Term.tuple "(" [`k "," [`i]] ")")])
                 "."
                 `Presheaf)
                "."
                `map_comp))
              ","
              (Tactic.rwRule
               []
               (Term.app `eq_to_hom_map [(Term.app `functor.op [(Term.hole "_")])]))
              ","
              (Tactic.rwRule [] `eq_to_hom_op)
              ","
              (Tactic.rwRule [] `eq_to_hom_trans)]
             "]")
            [])
           []
           (Std.Tactic.rintro
            "rintro"
            [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))
             (Std.Tactic.RCases.rintroPat.one
              (Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq)])
                 [])]
               "⟩"))]
            [])
           []
           (Mathlib.Tactic.tacticReplace_
            "replace"
            (Term.haveDecl
             (Term.haveIdDecl
              [`eq []]
              []
              ":="
              (Term.app
               `concrete_category.congr_arg
               [(Term.proj
                 (Term.app
                  (Term.proj
                   (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                    "𝖣")
                   "."
                   `t)
                  [`i `k])
                 "."
                 `base)
                `Eq]))))
           []
           (Tactic.change
            "change"
            («term_=_»
             (Term.app
              (Term.proj
               (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₂_,_,_»
                 "π₂ "
                 `i
                 ", "
                 `j
                 ", "
                 `k)
                " ≫ "
                (Term.app `D.t [`i `k]))
               "."
               `base)
              [`y])
             "="
             (Term.app
              (Term.proj
               (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                (Term.app `D.t [`k `i])
                " ≫ "
                (Term.app `D.t [`i `k]))
               "."
               `base)
              [`x]))
            [(Tactic.location "at" (Tactic.locationHyp [`eq] []))])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               []
               (Term.proj
                (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                 "𝖣")
                "."
                `t_inv))
              ","
              (Tactic.rwRule [] `id_base)
              ","
              (Tactic.rwRule [] `TopCat.id_app)]
             "]")
            [(Tactic.location "at" (Tactic.locationHyp [`eq] []))])
           []
           (Tactic.subst "subst" [`Eq])
           []
           (Mathlib.Tactic.«tacticUse_,,»
            "use"
            [(Term.app (Term.proj (Term.app `inv [(Term.app `D.t' [`k `i `j])]) "." `base) [`y])])
           []
           (Tactic.change
            "change"
            («term_=_»
             (Term.app
              (Term.proj
               (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                (Term.app `inv [(Term.app `D.t' [`k `i `j])])
                " ≫ "
                (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁_,_,_»
                 "π₁ "
                 `k
                 ", "
                 `i
                 ", "
                 `j))
               "."
               `base)
              [`y])
             "="
             (Term.hole "_"))
            [])
           []
           (Tactic.congr "congr" [(num "2")])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `is_iso.inv_comp_eq)
              ","
              (Tactic.rwRule
               []
               (Term.proj
                (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                 "𝖣")
                "."
                `t_fac_assoc))
              ","
              (Tactic.rwRule
               []
               (Term.proj
                (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                 "𝖣")
                "."
                `t_inv))
              ","
              (Tactic.rwRule [] `category.comp_id)]
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
         [(Tactic.constructor "constructor")
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `is_iso.eq_inv_comp)
             ","
             (Tactic.rwRule [] `is_open_immersion.inv_inv_app)
             ","
             (Tactic.rwRule [] `category.assoc)
             ","
             (Tactic.rwRule
              []
              (Term.proj (Term.proj (Term.app `D.t' [`k `i `j]) "." `c) "." `naturality_assoc))]
            "]")
           [])
          []
          (Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `category.assoc)]
            "]")
           [])
          []
          (Tactic.tacticErw__
           "erw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `comp_c_app)]
            "]")
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] (Term.app `congr_app [(Term.app `D.t_fac [`k `i `j])]))
             ","
             (Tactic.rwRule [] `comp_c_app)]
            "]")
           [])
          []
          (Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
           [])
          []
          (Tactic.tacticErw__
           "erw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `is_open_immersion.inv_naturality)
             ","
             (Tactic.rwRule [] `is_open_immersion.inv_naturality_assoc)
             ","
             (Tactic.rwRule [] `is_open_immersion.app_inv_app'_assoc)]
            "]")
           [])
          []
          (Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.proj
               (Term.proj
                (Term.app
                 (Term.proj
                  (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                   "𝖣")
                  "."
                  `V)
                 [(Term.tuple "(" [`k "," [`i]] ")")])
                "."
                `Presheaf)
               "."
               `map_comp))
             ","
             (Tactic.rwRule [] (Term.app `eq_to_hom_map [(Term.app `functor.op [(Term.hole "_")])]))
             ","
             (Tactic.rwRule [] `eq_to_hom_op)
             ","
             (Tactic.rwRule [] `eq_to_hom_trans)]
            "]")
           [])
          []
          (Std.Tactic.rintro
           "rintro"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))
            (Std.Tactic.RCases.rintroPat.one
             (Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq)])
                [])]
              "⟩"))]
           [])
          []
          (Mathlib.Tactic.tacticReplace_
           "replace"
           (Term.haveDecl
            (Term.haveIdDecl
             [`eq []]
             []
             ":="
             (Term.app
              `concrete_category.congr_arg
              [(Term.proj
                (Term.app
                 (Term.proj
                  (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                   "𝖣")
                  "."
                  `t)
                 [`i `k])
                "."
                `base)
               `Eq]))))
          []
          (Tactic.change
           "change"
           («term_=_»
            (Term.app
             (Term.proj
              (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
               (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₂_,_,_»
                "π₂ "
                `i
                ", "
                `j
                ", "
                `k)
               " ≫ "
               (Term.app `D.t [`i `k]))
              "."
              `base)
             [`y])
            "="
            (Term.app
             (Term.proj
              (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
               (Term.app `D.t [`k `i])
               " ≫ "
               (Term.app `D.t [`i `k]))
              "."
              `base)
             [`x]))
           [(Tactic.location "at" (Tactic.locationHyp [`eq] []))])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.proj
               (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                "𝖣")
               "."
               `t_inv))
             ","
             (Tactic.rwRule [] `id_base)
             ","
             (Tactic.rwRule [] `TopCat.id_app)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`eq] []))])
          []
          (Tactic.subst "subst" [`Eq])
          []
          (Mathlib.Tactic.«tacticUse_,,»
           "use"
           [(Term.app (Term.proj (Term.app `inv [(Term.app `D.t' [`k `i `j])]) "." `base) [`y])])
          []
          (Tactic.change
           "change"
           («term_=_»
            (Term.app
             (Term.proj
              (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
               (Term.app `inv [(Term.app `D.t' [`k `i `j])])
               " ≫ "
               (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁_,_,_»
                "π₁ "
                `k
                ", "
                `i
                ", "
                `j))
              "."
              `base)
             [`y])
            "="
            (Term.hole "_"))
           [])
          []
          (Tactic.congr "congr" [(num "2")])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `is_iso.inv_comp_eq)
             ","
             (Tactic.rwRule
              []
              (Term.proj
               (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                "𝖣")
               "."
               `t_fac_assoc))
             ","
             (Tactic.rwRule
              []
              (Term.proj
               (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                "𝖣")
               "."
               `t_inv))
             ","
             (Tactic.rwRule [] `category.comp_id)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `is_iso.inv_comp_eq)
         ","
         (Tactic.rwRule
          []
          (Term.proj
           (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
            "𝖣")
           "."
           `t_fac_assoc))
         ","
         (Tactic.rwRule
          []
          (Term.proj
           (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
            "𝖣")
           "."
           `t_inv))
         ","
         (Tactic.rwRule [] `category.comp_id)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `category.comp_id
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
        "𝖣")
       "."
       `t_inv)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
       "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»', expected 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.term𝖣._@.AlgebraicGeometry.PresheafedSpace.Gluing._hyg.31'
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
    We can prove the `eq` along with the lemma. Thus this is bundled together here, and the
    lemma itself is separated below.
    -/
  theorem
    snd_inv_app_t_app'
    ( i j k : D . J ) ( U : Opens pullback D . f i j D . f i k . carrier )
      :
        ∃
          eq
          ,
          π₂⁻¹ i , j , k U ≫ D . t k i . c . app _ ≫ D . V ( k , i ) . Presheaf . map eqToHom Eq
            =
            D . t' k i j . c . app _ ≫ π₁⁻¹ k , j , i unop _
    :=
      by
        constructor
          rw
            [
              ← is_iso.eq_inv_comp
                ,
                is_open_immersion.inv_inv_app
                ,
                category.assoc
                ,
                D.t' k i j . c . naturality_assoc
              ]
          simp_rw [ ← category.assoc ]
          erw [ ← comp_c_app ]
          rw [ congr_app D.t_fac k i j , comp_c_app ]
          simp_rw [ category.assoc ]
          erw
            [
              is_open_immersion.inv_naturality
                ,
                is_open_immersion.inv_naturality_assoc
                ,
                is_open_immersion.app_inv_app'_assoc
              ]
          simp_rw
            [
              ← 𝖣 . V ( k , i ) . Presheaf . map_comp
                ,
                eq_to_hom_map functor.op _
                ,
                eq_to_hom_op
                ,
                eq_to_hom_trans
              ]
          rintro x ⟨ y , hy , eq ⟩
          replace eq := concrete_category.congr_arg 𝖣 . t i k . base Eq
          change π₂ i , j , k ≫ D.t i k . base y = D.t k i ≫ D.t i k . base x at eq
          rw [ 𝖣 . t_inv , id_base , TopCat.id_app ] at eq
          subst Eq
          use inv D.t' k i j . base y
          change inv D.t' k i j ≫ π₁ k , i , j . base y = _
          congr 2
          rw [ is_iso.inv_comp_eq , 𝖣 . t_fac_assoc , 𝖣 . t_inv , category.comp_id ]
#align
  algebraic_geometry.PresheafedSpace.glue_data.snd_inv_app_t_app' AlgebraicGeometry.PresheafedSpaceCat.GlueData.snd_inv_app_t_app'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The red and the blue arrows in ![this diagram](https://i.imgur.com/q6X1GJ9.png) commute. -/")]
      [(Term.attributes
        "@["
        [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))
         ","
         (Term.attrInstance
          (Term.attrKind [])
          (Attr.simple `reassoc._@.AlgebraicGeometry.PresheafedSpace.Gluing._hyg.1 []))]
        "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `snd_inv_app_t_app [])
      (Command.declSig
       [(Term.explicitBinder "(" [`i `j `k] [":" (Term.proj `D "." `J)] [] ")")
        (Term.explicitBinder
         "("
         [`U]
         [":"
          (Term.app
           `Opens
           [(Term.proj
             (Term.app
              `pullback
              [(Term.app (Term.proj `D "." `f) [`i `j]) (Term.app (Term.proj `D "." `f) [`i `k])])
             "."
             `carrier)])]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app
           (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₂⁻¹_,_,_»
            "π₂⁻¹ "
            `i
            ", "
            `j
            ", "
            `k)
           [`U])
          " ≫ "
          (Term.app
           (Term.proj (Term.proj (Term.app (Term.proj `D "." `t) [`k `i]) "." `c) "." `app)
           [(Term.hole "_")]))
         "="
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app
           (Term.proj (Term.proj (Term.app (Term.proj `D "." `t') [`k `i `j]) "." `c) "." `app)
           [(Term.hole "_")])
          " ≫ "
          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
           (Term.app
            (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁⁻¹_,_,_»
             "π₁⁻¹ "
             `k
             ", "
             `j
             ", "
             `i)
            [(Term.app `unop [(Term.hole "_")])])
           " ≫ "
           (Term.app
            (Term.proj
             (Term.proj
              (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`k "," [`i]] ")")])
              "."
              `Presheaf)
             "."
             `map)
            [(Term.app
              `eqToHom
              [(Term.proj
                (Term.proj
                 (Term.app (Term.proj `D "." `snd_inv_app_t_app') [`i `j `k `U])
                 "."
                 `some)
                "."
                `symm)])]))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`e []]
              []
              ":="
              (Term.proj (Term.app `D.snd_inv_app_t_app' [`i `j `k `U]) "." `some_spec))))
           []
           (Tactic.reassoc! "reassoc!" [(group `e)])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `e)] "]")
            [])
           []
           (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `eq_to_hom_map)] "]"] [])])))
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
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`e []]
             []
             ":="
             (Term.proj (Term.app `D.snd_inv_app_t_app' [`i `j `k `U]) "." `some_spec))))
          []
          (Tactic.reassoc! "reassoc!" [(group `e)])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `e)] "]")
           [])
          []
          (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `eq_to_hom_map)] "]"] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `eq_to_hom_map)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq_to_hom_map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `e)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.reassoc! "reassoc!" [(group `e)])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`e []]
         []
         ":="
         (Term.proj (Term.app `D.snd_inv_app_t_app' [`i `j `k `U]) "." `some_spec))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `D.snd_inv_app_t_app' [`i `j `k `U]) "." `some_spec)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `D.snd_inv_app_t_app' [`i `j `k `U])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `D.snd_inv_app_t_app'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `D.snd_inv_app_t_app' [`i `j `k `U])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app
         (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₂⁻¹_,_,_»
          "π₂⁻¹ "
          `i
          ", "
          `j
          ", "
          `k)
         [`U])
        " ≫ "
        (Term.app
         (Term.proj (Term.proj (Term.app (Term.proj `D "." `t) [`k `i]) "." `c) "." `app)
         [(Term.hole "_")]))
       "="
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app
         (Term.proj (Term.proj (Term.app (Term.proj `D "." `t') [`k `i `j]) "." `c) "." `app)
         [(Term.hole "_")])
        " ≫ "
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         (Term.app
          (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁⁻¹_,_,_»
           "π₁⁻¹ "
           `k
           ", "
           `j
           ", "
           `i)
          [(Term.app `unop [(Term.hole "_")])])
         " ≫ "
         (Term.app
          (Term.proj
           (Term.proj
            (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`k "," [`i]] ")")])
            "."
            `Presheaf)
           "."
           `map)
          [(Term.app
            `eqToHom
            [(Term.proj
              (Term.proj (Term.app (Term.proj `D "." `snd_inv_app_t_app') [`i `j `k `U]) "." `some)
              "."
              `symm)])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app
        (Term.proj (Term.proj (Term.app (Term.proj `D "." `t') [`k `i `j]) "." `c) "." `app)
        [(Term.hole "_")])
       " ≫ "
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app
         (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁⁻¹_,_,_»
          "π₁⁻¹ "
          `k
          ", "
          `j
          ", "
          `i)
         [(Term.app `unop [(Term.hole "_")])])
        " ≫ "
        (Term.app
         (Term.proj
          (Term.proj
           (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`k "," [`i]] ")")])
           "."
           `Presheaf)
          "."
          `map)
         [(Term.app
           `eqToHom
           [(Term.proj
             (Term.proj (Term.app (Term.proj `D "." `snd_inv_app_t_app') [`i `j `k `U]) "." `some)
             "."
             `symm)])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app
        (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁⁻¹_,_,_»
         "π₁⁻¹ "
         `k
         ", "
         `j
         ", "
         `i)
        [(Term.app `unop [(Term.hole "_")])])
       " ≫ "
       (Term.app
        (Term.proj
         (Term.proj
          (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`k "," [`i]] ")")])
          "."
          `Presheaf)
         "."
         `map)
        [(Term.app
          `eqToHom
          [(Term.proj
            (Term.proj (Term.app (Term.proj `D "." `snd_inv_app_t_app') [`i `j `k `U]) "." `some)
            "."
            `symm)])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.proj
         (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`k "," [`i]] ")")])
         "."
         `Presheaf)
        "."
        `map)
       [(Term.app
         `eqToHom
         [(Term.proj
           (Term.proj (Term.app (Term.proj `D "." `snd_inv_app_t_app') [`i `j `k `U]) "." `some)
           "."
           `symm)])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `eqToHom
       [(Term.proj
         (Term.proj (Term.app (Term.proj `D "." `snd_inv_app_t_app') [`i `j `k `U]) "." `some)
         "."
         `symm)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.proj (Term.app (Term.proj `D "." `snd_inv_app_t_app') [`i `j `k `U]) "." `some)
       "."
       `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app (Term.proj `D "." `snd_inv_app_t_app') [`i `j `k `U]) "." `some)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `D "." `snd_inv_app_t_app') [`i `j `k `U])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `D "." `snd_inv_app_t_app')
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `D
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `D "." `snd_inv_app_t_app') [`i `j `k `U])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eqToHom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `eqToHom
      [(Term.proj
        (Term.proj
         (Term.paren "(" (Term.app (Term.proj `D "." `snd_inv_app_t_app') [`i `j `k `U]) ")")
         "."
         `some)
        "."
        `symm)])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.proj
        (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`k "," [`i]] ")")])
        "."
        `Presheaf)
       "."
       `map)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`k "," [`i]] ")")])
       "."
       `Presheaf)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`k "," [`i]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`k "," [`i]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `D "." `V)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `D
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`k "," [`i]] ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app
       (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁⁻¹_,_,_»
        "π₁⁻¹ "
        `k
        ", "
        `j
        ", "
        `i)
       [(Term.app `unop [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `unop [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `unop
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `unop [(Term.hole "_")]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁⁻¹_,_,_»
       "π₁⁻¹ "
       `k
       ", "
       `j
       ", "
       `i)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁⁻¹_,_,_»', expected 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.termπ₁⁻¹_,_,_._@.AlgebraicGeometry.PresheafedSpace.Gluing._hyg.215'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The red and the blue arrows in ![this diagram](https://i.imgur.com/q6X1GJ9.png) commute. -/
    @[ simp , reassoc ]
  theorem
    snd_inv_app_t_app
    ( i j k : D . J ) ( U : Opens pullback D . f i j D . f i k . carrier )
      :
        π₂⁻¹ i , j , k U ≫ D . t k i . c . app _
          =
          D . t' k i j . c . app _
            ≫
            π₁⁻¹ k , j , i unop _
              ≫
              D . V ( k , i ) . Presheaf . map eqToHom D . snd_inv_app_t_app' i j k U . some . symm
    :=
      by
        have e := D.snd_inv_app_t_app' i j k U . some_spec
          reassoc! e
          rw [ ← e ]
          simp [ eq_to_hom_map ]
#align
  algebraic_geometry.PresheafedSpace.glue_data.snd_inv_app_t_app AlgebraicGeometry.PresheafedSpaceCat.GlueData.snd_inv_app_t_app

variable [HasLimits C]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `ι_image_preimage_eq [])
      (Command.declSig
       [(Term.explicitBinder "(" [`i `j] [":" (Term.proj `D "." `J)] [] ")")
        (Term.explicitBinder
         "("
         [`U]
         [":" (Term.app `Opens [(Term.proj (Term.app (Term.proj `D "." `U) [`i]) "." `carrier)])]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (Term.proj
           (Term.app
            `Opens.map
            [(Term.proj
              (Term.app
               (Term.proj
                (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                 "𝖣")
                "."
                `ι)
               [`j])
              "."
              `base)])
           "."
           `obj)
          [(Term.app
            (Term.proj
             (Term.proj
              (Term.proj (Term.app (Term.proj `D "." `ι_open_embedding) [`i]) "." `IsOpenMap)
              "."
              `Functor)
             "."
             `obj)
            [`U])])
         "="
         (Term.app
          (Term.proj
           (Term.proj (Term.app (Term.proj `D "." `f_open) [`j `i]) "." `openFunctor)
           "."
           `obj)
          [(Term.app
            (Term.proj
             (Term.app
              `Opens.map
              [(Term.proj
                (Term.app
                 (Term.proj
                  (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                   "𝖣")
                  "."
                  `t)
                 [`j `i])
                "."
                `base)])
             "."
             `obj)
            [(Term.app
              (Term.proj
               (Term.app
                `Opens.map
                [(Term.proj
                  (Term.app
                   (Term.proj
                    (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                     "𝖣")
                    "."
                    `f)
                   [`i `j])
                  "."
                  `base)])
               "."
               `obj)
              [`U])])]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.dsimp
            "dsimp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `opens.map) "," (Tactic.simpLemma [] [] `IsOpenMap.functor)]
             "]"]
            [])
           []
           (Tactic.congr "congr" [(num "1")])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.show
                "show"
                («term_=_»
                 (Term.hole "_")
                 "="
                 (Term.proj
                  (Term.app
                   (Term.proj
                    (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                     "𝖣")
                    "."
                    `ι)
                   [`i])
                  "."
                  `base))
                (Term.fromTerm
                 "from"
                 (Term.app
                  (Term.proj
                   (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                    "𝖣")
                   "."
                   `ι_glued_iso_inv)
                  [(Term.app `PresheafedSpace.forget [(Term.hole "_")]) `i]))))
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.show
                "show"
                («term_=_»
                 (Term.hole "_")
                 "="
                 (Term.proj
                  (Term.app
                   (Term.proj
                    (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                     "𝖣")
                    "."
                    `ι)
                   [`j])
                  "."
                  `base))
                (Term.fromTerm
                 "from"
                 (Term.app
                  (Term.proj
                   (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                    "𝖣")
                   "."
                   `ι_glued_iso_inv)
                  [(Term.app `PresheafedSpace.forget [(Term.hole "_")]) `j]))))
              ","
              (Tactic.rwRule [] `coe_comp)
              ","
              (Tactic.rwRule [] `coe_comp)
              ","
              (Tactic.rwRule [] `Set.image_comp)
              ","
              (Tactic.rwRule [] `Set.preimage_comp)
              ","
              (Tactic.rwRule [] `Set.preimage_image_eq)]
             "]")
            [])
           []
           (Tactic.refine'
            "refine'"
            (Term.app
             `Eq.trans
             [(Term.app
               `D.to_Top_glue_data.preimage_image_eq_image'
               [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
              (Term.hole "_")]))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `coe_comp) "," (Tactic.rwRule [] `Set.image_comp)]
             "]")
            [])
           []
           (Tactic.congr "congr" [(num "1")])
           []
           (Tactic.tacticErw__
            "erw"
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.eq_preimage_iff_image_eq)] "]")
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_comp)]
             "]")
            [])
           []
           (Tactic.change
            "change"
            («term_=_»
             (Set.Data.Set.Image.term_''_
              (Term.proj
               (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                (Term.app `D.t [`i `j])
                " ≫ "
                (Term.app `D.t [`j `i]))
               "."
               `base)
              " '' "
              (Term.hole "_"))
             "="
             (Term.hole "_"))
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
                (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                 "𝖣")
                "."
                `t_inv))]
             "]")
            [])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp "simp" [] [] [] [] [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.change
              "change"
              (Term.app
               `Function.Bijective
               [(Term.app `TopCat.homeoOfIso [(Term.app `as_iso [(Term.hole "_")])])])
              [])
             []
             (Tactic.exact "exact" (Term.app `Homeomorph.bijective [(Term.hole "_")]))
             []
             (Tactic.tacticInfer_instance "infer_instance")])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `TopCat.mono_iff_injective)]
               "]")
              [])
             []
             (Tactic.tacticInfer_instance "infer_instance")])])))
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
         [(Tactic.dsimp
           "dsimp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `opens.map) "," (Tactic.simpLemma [] [] `IsOpenMap.functor)]
            "]"]
           [])
          []
          (Tactic.congr "congr" [(num "1")])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.show
               "show"
               («term_=_»
                (Term.hole "_")
                "="
                (Term.proj
                 (Term.app
                  (Term.proj
                   (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                    "𝖣")
                   "."
                   `ι)
                  [`i])
                 "."
                 `base))
               (Term.fromTerm
                "from"
                (Term.app
                 (Term.proj
                  (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                   "𝖣")
                  "."
                  `ι_glued_iso_inv)
                 [(Term.app `PresheafedSpace.forget [(Term.hole "_")]) `i]))))
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.show
               "show"
               («term_=_»
                (Term.hole "_")
                "="
                (Term.proj
                 (Term.app
                  (Term.proj
                   (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                    "𝖣")
                   "."
                   `ι)
                  [`j])
                 "."
                 `base))
               (Term.fromTerm
                "from"
                (Term.app
                 (Term.proj
                  (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                   "𝖣")
                  "."
                  `ι_glued_iso_inv)
                 [(Term.app `PresheafedSpace.forget [(Term.hole "_")]) `j]))))
             ","
             (Tactic.rwRule [] `coe_comp)
             ","
             (Tactic.rwRule [] `coe_comp)
             ","
             (Tactic.rwRule [] `Set.image_comp)
             ","
             (Tactic.rwRule [] `Set.preimage_comp)
             ","
             (Tactic.rwRule [] `Set.preimage_image_eq)]
            "]")
           [])
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            `Eq.trans
            [(Term.app
              `D.to_Top_glue_data.preimage_image_eq_image'
              [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
             (Term.hole "_")]))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `coe_comp) "," (Tactic.rwRule [] `Set.image_comp)]
            "]")
           [])
          []
          (Tactic.congr "congr" [(num "1")])
          []
          (Tactic.tacticErw__
           "erw"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.eq_preimage_iff_image_eq)] "]")
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_comp)]
            "]")
           [])
          []
          (Tactic.change
           "change"
           («term_=_»
            (Set.Data.Set.Image.term_''_
             (Term.proj
              (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
               (Term.app `D.t [`i `j])
               " ≫ "
               (Term.app `D.t [`j `i]))
              "."
              `base)
             " '' "
             (Term.hole "_"))
            "="
            (Term.hole "_"))
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
               (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                "𝖣")
               "."
               `t_inv))]
            "]")
           [])
          []
          (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.simp "simp" [] [] [] [] [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.change
             "change"
             (Term.app
              `Function.Bijective
              [(Term.app `TopCat.homeoOfIso [(Term.app `as_iso [(Term.hole "_")])])])
             [])
            []
            (Tactic.exact "exact" (Term.app `Homeomorph.bijective [(Term.hole "_")]))
            []
            (Tactic.tacticInfer_instance "infer_instance")])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `TopCat.mono_iff_injective)]
              "]")
             [])
            []
            (Tactic.tacticInfer_instance "infer_instance")])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `TopCat.mono_iff_injective)]
          "]")
         [])
        []
        (Tactic.tacticInfer_instance "infer_instance")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticInfer_instance "infer_instance")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `TopCat.mono_iff_injective)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `TopCat.mono_iff_injective
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.change
         "change"
         (Term.app
          `Function.Bijective
          [(Term.app `TopCat.homeoOfIso [(Term.app `as_iso [(Term.hole "_")])])])
         [])
        []
        (Tactic.exact "exact" (Term.app `Homeomorph.bijective [(Term.hole "_")]))
        []
        (Tactic.tacticInfer_instance "infer_instance")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticInfer_instance "infer_instance")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `Homeomorph.bijective [(Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Homeomorph.bijective [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Homeomorph.bijective
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       (Term.app
        `Function.Bijective
        [(Term.app `TopCat.homeoOfIso [(Term.app `as_iso [(Term.hole "_")])])])
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Function.Bijective
       [(Term.app `TopCat.homeoOfIso [(Term.app `as_iso [(Term.hole "_")])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `TopCat.homeoOfIso [(Term.app `as_iso [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `as_iso [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `as_iso
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `as_iso [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `TopCat.homeoOfIso
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `TopCat.homeoOfIso [(Term.paren "(" (Term.app `as_iso [(Term.hole "_")]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Function.Bijective
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Tactic.simp "simp" [] [] [] [] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
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
           (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
            "𝖣")
           "."
           `t_inv))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
        "𝖣")
       "."
       `t_inv)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
       "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»', expected 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.term𝖣._@.AlgebraicGeometry.PresheafedSpace.Gluing._hyg.31'
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
  ι_image_preimage_eq
  ( i j : D . J ) ( U : Opens D . U i . carrier )
    :
      Opens.map 𝖣 . ι j . base . obj D . ι_open_embedding i . IsOpenMap . Functor . obj U
        =
        D . f_open j i . openFunctor . obj
          Opens.map 𝖣 . t j i . base . obj Opens.map 𝖣 . f i j . base . obj U
  :=
    by
      dsimp only [ opens.map , IsOpenMap.functor ]
        congr 1
        rw
          [
            ← show _ = 𝖣 . ι i . base from 𝖣 . ι_glued_iso_inv PresheafedSpace.forget _ i
              ,
              ← show _ = 𝖣 . ι j . base from 𝖣 . ι_glued_iso_inv PresheafedSpace.forget _ j
              ,
              coe_comp
              ,
              coe_comp
              ,
              Set.image_comp
              ,
              Set.preimage_comp
              ,
              Set.preimage_image_eq
            ]
        refine' Eq.trans D.to_Top_glue_data.preimage_image_eq_image' _ _ _ _
        rw [ coe_comp , Set.image_comp ]
        congr 1
        erw [ Set.eq_preimage_iff_image_eq ]
        rw [ ← Set.image_comp ]
        change D.t i j ≫ D.t j i . base '' _ = _
        rw [ 𝖣 . t_inv ]
        · simp
        ·
          change Function.Bijective TopCat.homeoOfIso as_iso _
            exact Homeomorph.bijective _
            infer_instance
        · rw [ ← TopCat.mono_iff_injective ] infer_instance
#align
  algebraic_geometry.PresheafedSpace.glue_data.ι_image_preimage_eq AlgebraicGeometry.PresheafedSpaceCat.GlueData.ι_image_preimage_eq

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "(Implementation). The map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_{U_j}, 𝖣.ι j ⁻¹' (𝖣.ι i '' U))` -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `opensImagePreimageMap [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`i `j] [":" (Term.proj `D "." `J)] [] ")")
        (Term.explicitBinder
         "("
         [`U]
         [":" (Term.app `Opens [(Term.proj (Term.app (Term.proj `D "." `U) [`i]) "." `carrier)])]
         []
         ")")]
       [(Term.typeSpec
         ":"
         (Combinatorics.Quiver.Basic.«term_⟶_»
          (Term.app
           (Term.proj (Term.proj (Term.app (Term.proj `D "." `U) [`i]) "." `Presheaf) "." `obj)
           [(Term.app `op [`U])])
          " ⟶ "
          (Term.app
           (Term.proj (Term.proj (Term.app (Term.proj `D "." `U) [`j]) "." `Presheaf) "." `obj)
           [(Term.hole "_")])))])
      (Command.declValSimple
       ":="
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app
         (Term.proj (Term.proj (Term.app (Term.proj `D "." `f) [`i `j]) "." `c) "." `app)
         [(Term.app `op [`U])])
        " ≫ "
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         (Term.app
          (Term.proj (Term.proj (Term.app (Term.proj `D "." `t) [`j `i]) "." `c) "." `app)
          [(Term.hole "_")])
         " ≫ "
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app
           (Term.proj (Term.app (Term.proj `D "." `f_open) [`j `i]) "." `invApp)
           [(Term.app `unop [(Term.hole "_")])])
          " ≫ "
          (Term.app
           (Term.proj
            (Term.proj
             (Term.app
              (Term.proj
               (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                "𝖣")
               "."
               `U)
              [`j])
             "."
             `Presheaf)
            "."
            `map)
           [(Term.proj
             (Term.app `eqToHom [(Term.app (Term.proj `D "." `ι_image_preimage_eq) [`i `j `U])])
             "."
             `op)]))))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app
        (Term.proj (Term.proj (Term.app (Term.proj `D "." `f) [`i `j]) "." `c) "." `app)
        [(Term.app `op [`U])])
       " ≫ "
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app
         (Term.proj (Term.proj (Term.app (Term.proj `D "." `t) [`j `i]) "." `c) "." `app)
         [(Term.hole "_")])
        " ≫ "
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         (Term.app
          (Term.proj (Term.app (Term.proj `D "." `f_open) [`j `i]) "." `invApp)
          [(Term.app `unop [(Term.hole "_")])])
         " ≫ "
         (Term.app
          (Term.proj
           (Term.proj
            (Term.app
             (Term.proj
              (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
               "𝖣")
              "."
              `U)
             [`j])
            "."
            `Presheaf)
           "."
           `map)
          [(Term.proj
            (Term.app `eqToHom [(Term.app (Term.proj `D "." `ι_image_preimage_eq) [`i `j `U])])
            "."
            `op)]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app
        (Term.proj (Term.proj (Term.app (Term.proj `D "." `t) [`j `i]) "." `c) "." `app)
        [(Term.hole "_")])
       " ≫ "
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app
         (Term.proj (Term.app (Term.proj `D "." `f_open) [`j `i]) "." `invApp)
         [(Term.app `unop [(Term.hole "_")])])
        " ≫ "
        (Term.app
         (Term.proj
          (Term.proj
           (Term.app
            (Term.proj
             (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
              "𝖣")
             "."
             `U)
            [`j])
           "."
           `Presheaf)
          "."
          `map)
         [(Term.proj
           (Term.app `eqToHom [(Term.app (Term.proj `D "." `ι_image_preimage_eq) [`i `j `U])])
           "."
           `op)])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app
        (Term.proj (Term.app (Term.proj `D "." `f_open) [`j `i]) "." `invApp)
        [(Term.app `unop [(Term.hole "_")])])
       " ≫ "
       (Term.app
        (Term.proj
         (Term.proj
          (Term.app
           (Term.proj
            (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
             "𝖣")
            "."
            `U)
           [`j])
          "."
          `Presheaf)
         "."
         `map)
        [(Term.proj
          (Term.app `eqToHom [(Term.app (Term.proj `D "." `ι_image_preimage_eq) [`i `j `U])])
          "."
          `op)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.proj
         (Term.app
          (Term.proj
           (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
            "𝖣")
           "."
           `U)
          [`j])
         "."
         `Presheaf)
        "."
        `map)
       [(Term.proj
         (Term.app `eqToHom [(Term.app (Term.proj `D "." `ι_image_preimage_eq) [`i `j `U])])
         "."
         `op)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app `eqToHom [(Term.app (Term.proj `D "." `ι_image_preimage_eq) [`i `j `U])])
       "."
       `op)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `eqToHom [(Term.app (Term.proj `D "." `ι_image_preimage_eq) [`i `j `U])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `D "." `ι_image_preimage_eq) [`i `j `U])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `D "." `ι_image_preimage_eq)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `D
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `D "." `ι_image_preimage_eq) [`i `j `U])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eqToHom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `eqToHom
      [(Term.paren "(" (Term.app (Term.proj `D "." `ι_image_preimage_eq) [`i `j `U]) ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.proj
        (Term.app
         (Term.proj
          (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
           "𝖣")
          "."
          `U)
         [`j])
        "."
        `Presheaf)
       "."
       `map)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.app
        (Term.proj
         (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
          "𝖣")
         "."
         `U)
        [`j])
       "."
       `Presheaf)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
         "𝖣")
        "."
        `U)
       [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
        "𝖣")
       "."
       `U)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
       "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»', expected 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.term𝖣._@.AlgebraicGeometry.PresheafedSpace.Gluing._hyg.31'
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
/-- (Implementation). The map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_{U_j}, 𝖣.ι j ⁻¹' (𝖣.ι i '' U))` -/
  def
    opensImagePreimageMap
    ( i j : D . J ) ( U : Opens D . U i . carrier )
      : D . U i . Presheaf . obj op U ⟶ D . U j . Presheaf . obj _
    :=
      D . f i j . c . app op U
        ≫
        D . t j i . c . app _
          ≫
          D . f_open j i . invApp unop _
            ≫
            𝖣 . U j . Presheaf . map eqToHom D . ι_image_preimage_eq i j U . op
#align
  algebraic_geometry.PresheafedSpace.glue_data.opens_image_preimage_map AlgebraicGeometry.PresheafedSpaceCat.GlueData.opensImagePreimageMap

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `opens_image_preimage_map_app' [])
      (Command.declSig
       [(Term.explicitBinder "(" [`i `j `k] [":" (Term.proj `D "." `J)] [] ")")
        (Term.explicitBinder
         "("
         [`U]
         [":" (Term.app `Opens [(Term.proj (Term.app (Term.proj `D "." `U) [`i]) "." `carrier)])]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `eq)] []))
         ","
         («term_=_»
          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
           (Term.app (Term.proj `D "." `opensImagePreimageMap) [`i `j `U])
           " ≫ "
           (Term.app
            (Term.proj (Term.proj (Term.app (Term.proj `D "." `f) [`j `k]) "." `c) "." `app)
            [(Term.hole "_")]))
          "="
          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
           (Term.app
            (Term.proj
             (Term.proj
              (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
               (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁_,_,_»
                "π₁ "
                `j
                ", "
                `i
                ", "
                `k)
               " ≫ "
               (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                (Term.app (Term.proj `D "." `t) [`j `i])
                " ≫ "
                (Term.app (Term.proj `D "." `f) [`i `j])))
              "."
              `c)
             "."
             `app)
            [(Term.app `op [`U])])
           " ≫ "
           (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
            (Term.app
             (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₂⁻¹_,_,_»
              "π₂⁻¹ "
              `j
              ", "
              `i
              ", "
              `k)
             [(Term.app `unop [(Term.hole "_")])])
            " ≫ "
            (Term.app
             (Term.proj
              (Term.proj
               (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`j "," [`k]] ")")])
               "."
               `Presheaf)
              "."
              `map)
             [(Term.app `eqToHom [`Eq])])))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.constructor "constructor")
           []
           (Tactic.delta "delta" [`opens_image_preimage_map] [])
           []
           (Mathlib.Tactic.tacticSimp_rw__
            "simp_rw"
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               []
               (Term.proj (Term.proj (Term.app `D.f [`j `k]) "." `c) "." `naturality))
              ","
              (Tactic.rwRule [] `f_inv_app_f_app_assoc)]
             "]")
            [])
           []
           (Tactic.tacticErw__
            "erw"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.proj
                (Term.proj (Term.app `D.V [(Term.tuple "(" [`j "," [`k]] ")")]) "." `Presheaf)
                "."
                `map_comp))]
             "]")
            [])
           []
           (Mathlib.Tactic.tacticSimp_rw__
            "simp_rw"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `category.assoc)]
             "]")
            [])
           []
           (Tactic.tacticErw__
            "erw"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `comp_c_app)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `comp_c_app)]
             "]")
            [])
           []
           (Mathlib.Tactic.tacticSimp_rw__
            "simp_rw"
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
            [])
           []
           (Tactic.dsimp
            "dsimp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `functor.op)
              ","
              (Tactic.simpLemma [] [] `unop_op)
              ","
              (Tactic.simpLemma [] [] `Quiver.Hom.unop_op)]
             "]"]
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] (Term.app `eq_to_hom_map [(Term.app `opens.map [(Term.hole "_")])]))
              ","
              (Tactic.rwRule [] `eq_to_hom_op)
              ","
              (Tactic.rwRule [] `eq_to_hom_trans)]
             "]")
            [])
           []
           (Tactic.congr "congr" [])])))
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
         [(Tactic.constructor "constructor")
          []
          (Tactic.delta "delta" [`opens_image_preimage_map] [])
          []
          (Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.proj (Term.proj (Term.app `D.f [`j `k]) "." `c) "." `naturality))
             ","
             (Tactic.rwRule [] `f_inv_app_f_app_assoc)]
            "]")
           [])
          []
          (Tactic.tacticErw__
           "erw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.proj
               (Term.proj (Term.app `D.V [(Term.tuple "(" [`j "," [`k]] ")")]) "." `Presheaf)
               "."
               `map_comp))]
            "]")
           [])
          []
          (Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `category.assoc)]
            "]")
           [])
          []
          (Tactic.tacticErw__
           "erw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `comp_c_app)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `comp_c_app)]
            "]")
           [])
          []
          (Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
           [])
          []
          (Tactic.dsimp
           "dsimp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `functor.op)
             ","
             (Tactic.simpLemma [] [] `unop_op)
             ","
             (Tactic.simpLemma [] [] `Quiver.Hom.unop_op)]
            "]"]
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] (Term.app `eq_to_hom_map [(Term.app `opens.map [(Term.hole "_")])]))
             ","
             (Tactic.rwRule [] `eq_to_hom_op)
             ","
             (Tactic.rwRule [] `eq_to_hom_trans)]
            "]")
           [])
          []
          (Tactic.congr "congr" [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.congr "congr" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] (Term.app `eq_to_hom_map [(Term.app `opens.map [(Term.hole "_")])]))
         ","
         (Tactic.rwRule [] `eq_to_hom_op)
         ","
         (Tactic.rwRule [] `eq_to_hom_trans)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq_to_hom_trans
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq_to_hom_op
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `eq_to_hom_map [(Term.app `opens.map [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `opens.map [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `opens.map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `opens.map [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eq_to_hom_map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp
       "dsimp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `functor.op)
         ","
         (Tactic.simpLemma [] [] `unop_op)
         ","
         (Tactic.simpLemma [] [] `Quiver.Hom.unop_op)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Quiver.Hom.unop_op
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `unop_op
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `functor.op
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `category.assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticErw__
       "erw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `comp_c_app)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `comp_c_app)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `comp_c_app
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `comp_c_app
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `category.assoc)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `category.assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticErw__
       "erw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.proj
           (Term.proj (Term.app `D.V [(Term.tuple "(" [`j "," [`k]] ")")]) "." `Presheaf)
           "."
           `map_comp))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.proj (Term.app `D.V [(Term.tuple "(" [`j "," [`k]] ")")]) "." `Presheaf)
       "."
       `map_comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app `D.V [(Term.tuple "(" [`j "," [`k]] ")")]) "." `Presheaf)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `D.V [(Term.tuple "(" [`j "," [`k]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`j "," [`k]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `D.V
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `D.V [(Term.tuple "(" [`j "," [`k]] ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] (Term.proj (Term.proj (Term.app `D.f [`j `k]) "." `c) "." `naturality))
         ","
         (Tactic.rwRule [] `f_inv_app_f_app_assoc)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f_inv_app_f_app_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj (Term.app `D.f [`j `k]) "." `c) "." `naturality)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app `D.f [`j `k]) "." `c)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `D.f [`j `k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `D.f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `D.f [`j `k]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `category.assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.delta "delta" [`opens_image_preimage_map] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.constructor "constructor")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `eq)] []))
       ","
       («term_=_»
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         (Term.app (Term.proj `D "." `opensImagePreimageMap) [`i `j `U])
         " ≫ "
         (Term.app
          (Term.proj (Term.proj (Term.app (Term.proj `D "." `f) [`j `k]) "." `c) "." `app)
          [(Term.hole "_")]))
        "="
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         (Term.app
          (Term.proj
           (Term.proj
            (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
             (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁_,_,_»
              "π₁ "
              `j
              ", "
              `i
              ", "
              `k)
             " ≫ "
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
              (Term.app (Term.proj `D "." `t) [`j `i])
              " ≫ "
              (Term.app (Term.proj `D "." `f) [`i `j])))
            "."
            `c)
           "."
           `app)
          [(Term.app `op [`U])])
         " ≫ "
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app
           (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₂⁻¹_,_,_»
            "π₂⁻¹ "
            `j
            ", "
            `i
            ", "
            `k)
           [(Term.app `unop [(Term.hole "_")])])
          " ≫ "
          (Term.app
           (Term.proj
            (Term.proj
             (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`j "," [`k]] ")")])
             "."
             `Presheaf)
            "."
            `map)
           [(Term.app `eqToHom [`Eq])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app (Term.proj `D "." `opensImagePreimageMap) [`i `j `U])
        " ≫ "
        (Term.app
         (Term.proj (Term.proj (Term.app (Term.proj `D "." `f) [`j `k]) "." `c) "." `app)
         [(Term.hole "_")]))
       "="
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app
         (Term.proj
          (Term.proj
           (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
            (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁_,_,_»
             "π₁ "
             `j
             ", "
             `i
             ", "
             `k)
            " ≫ "
            (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
             (Term.app (Term.proj `D "." `t) [`j `i])
             " ≫ "
             (Term.app (Term.proj `D "." `f) [`i `j])))
           "."
           `c)
          "."
          `app)
         [(Term.app `op [`U])])
        " ≫ "
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         (Term.app
          (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₂⁻¹_,_,_»
           "π₂⁻¹ "
           `j
           ", "
           `i
           ", "
           `k)
          [(Term.app `unop [(Term.hole "_")])])
         " ≫ "
         (Term.app
          (Term.proj
           (Term.proj
            (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`j "," [`k]] ")")])
            "."
            `Presheaf)
           "."
           `map)
          [(Term.app `eqToHom [`Eq])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app
        (Term.proj
         (Term.proj
          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
           (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁_,_,_»
            "π₁ "
            `j
            ", "
            `i
            ", "
            `k)
           " ≫ "
           (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
            (Term.app (Term.proj `D "." `t) [`j `i])
            " ≫ "
            (Term.app (Term.proj `D "." `f) [`i `j])))
          "."
          `c)
         "."
         `app)
        [(Term.app `op [`U])])
       " ≫ "
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app
         (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₂⁻¹_,_,_»
          "π₂⁻¹ "
          `j
          ", "
          `i
          ", "
          `k)
         [(Term.app `unop [(Term.hole "_")])])
        " ≫ "
        (Term.app
         (Term.proj
          (Term.proj
           (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`j "," [`k]] ")")])
           "."
           `Presheaf)
          "."
          `map)
         [(Term.app `eqToHom [`Eq])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app
        (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₂⁻¹_,_,_»
         "π₂⁻¹ "
         `j
         ", "
         `i
         ", "
         `k)
        [(Term.app `unop [(Term.hole "_")])])
       " ≫ "
       (Term.app
        (Term.proj
         (Term.proj
          (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`j "," [`k]] ")")])
          "."
          `Presheaf)
         "."
         `map)
        [(Term.app `eqToHom [`Eq])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.proj
         (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`j "," [`k]] ")")])
         "."
         `Presheaf)
        "."
        `map)
       [(Term.app `eqToHom [`Eq])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `eqToHom [`Eq])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Eq
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eqToHom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `eqToHom [`Eq]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.proj
        (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`j "," [`k]] ")")])
        "."
        `Presheaf)
       "."
       `map)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`j "," [`k]] ")")])
       "."
       `Presheaf)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`j "," [`k]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`j "," [`k]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `D "." `V)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `D
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`j "," [`k]] ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app
       (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₂⁻¹_,_,_»
        "π₂⁻¹ "
        `j
        ", "
        `i
        ", "
        `k)
       [(Term.app `unop [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `unop [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `unop
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `unop [(Term.hole "_")]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₂⁻¹_,_,_»
       "π₂⁻¹ "
       `j
       ", "
       `i
       ", "
       `k)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₂⁻¹_,_,_»', expected 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.termπ₂⁻¹_,_,_._@.AlgebraicGeometry.PresheafedSpace.Gluing._hyg.281'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  opens_image_preimage_map_app'
  ( i j k : D . J ) ( U : Opens D . U i . carrier )
    :
      ∃
        eq
        ,
        D . opensImagePreimageMap i j U ≫ D . f j k . c . app _
          =
          π₁ j , i , k ≫ D . t j i ≫ D . f i j . c . app op U
            ≫
            π₂⁻¹ j , i , k unop _ ≫ D . V ( j , k ) . Presheaf . map eqToHom Eq
  :=
    by
      constructor
        delta opens_image_preimage_map
        simp_rw [ category.assoc ]
        rw [ D.f j k . c . naturality , f_inv_app_f_app_assoc ]
        erw [ ← D.V ( j , k ) . Presheaf . map_comp ]
        simp_rw [ ← category.assoc ]
        erw [ ← comp_c_app , ← comp_c_app ]
        simp_rw [ category.assoc ]
        dsimp only [ functor.op , unop_op , Quiver.Hom.unop_op ]
        rw [ eq_to_hom_map opens.map _ , eq_to_hom_op , eq_to_hom_trans ]
        congr
#align
  algebraic_geometry.PresheafedSpace.glue_data.opens_image_preimage_map_app' AlgebraicGeometry.PresheafedSpaceCat.GlueData.opens_image_preimage_map_app'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The red and the blue arrows in ![this diagram](https://i.imgur.com/mBzV1Rx.png) commute. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `opens_image_preimage_map_app [])
      (Command.declSig
       [(Term.explicitBinder "(" [`i `j `k] [":" (Term.proj `D "." `J)] [] ")")
        (Term.explicitBinder
         "("
         [`U]
         [":" (Term.app `Opens [(Term.proj (Term.app (Term.proj `D "." `U) [`i]) "." `carrier)])]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app (Term.proj `D "." `opensImagePreimageMap) [`i `j `U])
          " ≫ "
          (Term.app
           (Term.proj (Term.proj (Term.app (Term.proj `D "." `f) [`j `k]) "." `c) "." `app)
           [(Term.hole "_")]))
         "="
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app
           (Term.proj
            (Term.proj
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
              (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁_,_,_»
               "π₁ "
               `j
               ", "
               `i
               ", "
               `k)
              " ≫ "
              (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
               (Term.app (Term.proj `D "." `t) [`j `i])
               " ≫ "
               (Term.app (Term.proj `D "." `f) [`i `j])))
             "."
             `c)
            "."
            `app)
           [(Term.app `op [`U])])
          " ≫ "
          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
           (Term.app
            (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₂⁻¹_,_,_»
             "π₂⁻¹ "
             `j
             ", "
             `i
             ", "
             `k)
            [(Term.app `unop [(Term.hole "_")])])
           " ≫ "
           (Term.app
            (Term.proj
             (Term.proj
              (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`j "," [`k]] ")")])
              "."
              `Presheaf)
             "."
             `map)
            [(Term.app
              `eqToHom
              [(Term.proj
                (Term.app `opens_image_preimage_map_app' [`D `i `j `k `U])
                "."
                `some)])]))))))
      (Command.declValSimple
       ":="
       (Term.proj (Term.app `opens_image_preimage_map_app' [`D `i `j `k `U]) "." `some_spec)
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `opens_image_preimage_map_app' [`D `i `j `k `U]) "." `some_spec)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `opens_image_preimage_map_app' [`D `i `j `k `U])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `D
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `opens_image_preimage_map_app'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `opens_image_preimage_map_app' [`D `i `j `k `U])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app (Term.proj `D "." `opensImagePreimageMap) [`i `j `U])
        " ≫ "
        (Term.app
         (Term.proj (Term.proj (Term.app (Term.proj `D "." `f) [`j `k]) "." `c) "." `app)
         [(Term.hole "_")]))
       "="
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app
         (Term.proj
          (Term.proj
           (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
            (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁_,_,_»
             "π₁ "
             `j
             ", "
             `i
             ", "
             `k)
            " ≫ "
            (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
             (Term.app (Term.proj `D "." `t) [`j `i])
             " ≫ "
             (Term.app (Term.proj `D "." `f) [`i `j])))
           "."
           `c)
          "."
          `app)
         [(Term.app `op [`U])])
        " ≫ "
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         (Term.app
          (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₂⁻¹_,_,_»
           "π₂⁻¹ "
           `j
           ", "
           `i
           ", "
           `k)
          [(Term.app `unop [(Term.hole "_")])])
         " ≫ "
         (Term.app
          (Term.proj
           (Term.proj
            (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`j "," [`k]] ")")])
            "."
            `Presheaf)
           "."
           `map)
          [(Term.app
            `eqToHom
            [(Term.proj (Term.app `opens_image_preimage_map_app' [`D `i `j `k `U]) "." `some)])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app
        (Term.proj
         (Term.proj
          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
           (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁_,_,_»
            "π₁ "
            `j
            ", "
            `i
            ", "
            `k)
           " ≫ "
           (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
            (Term.app (Term.proj `D "." `t) [`j `i])
            " ≫ "
            (Term.app (Term.proj `D "." `f) [`i `j])))
          "."
          `c)
         "."
         `app)
        [(Term.app `op [`U])])
       " ≫ "
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app
         (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₂⁻¹_,_,_»
          "π₂⁻¹ "
          `j
          ", "
          `i
          ", "
          `k)
         [(Term.app `unop [(Term.hole "_")])])
        " ≫ "
        (Term.app
         (Term.proj
          (Term.proj
           (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`j "," [`k]] ")")])
           "."
           `Presheaf)
          "."
          `map)
         [(Term.app
           `eqToHom
           [(Term.proj (Term.app `opens_image_preimage_map_app' [`D `i `j `k `U]) "." `some)])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app
        (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₂⁻¹_,_,_»
         "π₂⁻¹ "
         `j
         ", "
         `i
         ", "
         `k)
        [(Term.app `unop [(Term.hole "_")])])
       " ≫ "
       (Term.app
        (Term.proj
         (Term.proj
          (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`j "," [`k]] ")")])
          "."
          `Presheaf)
         "."
         `map)
        [(Term.app
          `eqToHom
          [(Term.proj (Term.app `opens_image_preimage_map_app' [`D `i `j `k `U]) "." `some)])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.proj
         (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`j "," [`k]] ")")])
         "."
         `Presheaf)
        "."
        `map)
       [(Term.app
         `eqToHom
         [(Term.proj (Term.app `opens_image_preimage_map_app' [`D `i `j `k `U]) "." `some)])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `eqToHom
       [(Term.proj (Term.app `opens_image_preimage_map_app' [`D `i `j `k `U]) "." `some)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `opens_image_preimage_map_app' [`D `i `j `k `U]) "." `some)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `opens_image_preimage_map_app' [`D `i `j `k `U])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `D
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `opens_image_preimage_map_app'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `opens_image_preimage_map_app' [`D `i `j `k `U])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eqToHom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `eqToHom
      [(Term.proj
        (Term.paren "(" (Term.app `opens_image_preimage_map_app' [`D `i `j `k `U]) ")")
        "."
        `some)])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.proj
        (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`j "," [`k]] ")")])
        "."
        `Presheaf)
       "."
       `map)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`j "," [`k]] ")")])
       "."
       `Presheaf)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`j "," [`k]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`j "," [`k]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `D "." `V)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `D
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`j "," [`k]] ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app
       (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₂⁻¹_,_,_»
        "π₂⁻¹ "
        `j
        ", "
        `i
        ", "
        `k)
       [(Term.app `unop [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `unop [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `unop
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `unop [(Term.hole "_")]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₂⁻¹_,_,_»
       "π₂⁻¹ "
       `j
       ", "
       `i
       ", "
       `k)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₂⁻¹_,_,_»', expected 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.termπ₂⁻¹_,_,_._@.AlgebraicGeometry.PresheafedSpace.Gluing._hyg.281'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The red and the blue arrows in ![this diagram](https://i.imgur.com/mBzV1Rx.png) commute. -/
  theorem
    opens_image_preimage_map_app
    ( i j k : D . J ) ( U : Opens D . U i . carrier )
      :
        D . opensImagePreimageMap i j U ≫ D . f j k . c . app _
          =
          π₁ j , i , k ≫ D . t j i ≫ D . f i j . c . app op U
            ≫
            π₂⁻¹ j , i , k unop _
              ≫
              D . V ( j , k ) . Presheaf . map
                eqToHom opens_image_preimage_map_app' D i j k U . some
    := opens_image_preimage_map_app' D i j k U . some_spec
#align
  algebraic_geometry.PresheafedSpace.glue_data.opens_image_preimage_map_app AlgebraicGeometry.PresheafedSpaceCat.GlueData.opens_image_preimage_map_app

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `opens_image_preimage_map_app_assoc [])
      (Command.declSig
       [(Term.explicitBinder "(" [`i `j `k] [":" (Term.proj `D "." `J)] [] ")")
        (Term.explicitBinder
         "("
         [`U]
         [":" (Term.app `Opens [(Term.proj (Term.app (Term.proj `D "." `U) [`i]) "." `carrier)])]
         []
         ")")
        (Term.implicitBinder "{" [`X'] [":" `C] "}")
        (Term.explicitBinder
         "("
         [`f']
         [":" (Combinatorics.Quiver.Basic.«term_⟶_» (Term.hole "_") " ⟶ " `X')]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app (Term.proj `D "." `opensImagePreimageMap) [`i `j `U])
          " ≫ "
          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
           (Term.app
            (Term.proj (Term.proj (Term.app (Term.proj `D "." `f) [`j `k]) "." `c) "." `app)
            [(Term.hole "_")])
           " ≫ "
           `f'))
         "="
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app
           (Term.proj
            (Term.proj
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
              (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁_,_,_»
               "π₁ "
               `j
               ", "
               `i
               ", "
               `k)
              " ≫ "
              (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
               (Term.app (Term.proj `D "." `t) [`j `i])
               " ≫ "
               (Term.app (Term.proj `D "." `f) [`i `j])))
             "."
             `c)
            "."
            `app)
           [(Term.app `op [`U])])
          " ≫ "
          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
           (Term.app
            (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₂⁻¹_,_,_»
             "π₂⁻¹ "
             `j
             ", "
             `i
             ", "
             `k)
            [(Term.app `unop [(Term.hole "_")])])
           " ≫ "
           (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
            (Term.app
             (Term.proj
              (Term.proj
               (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`j "," [`k]] ")")])
               "."
               `Presheaf)
              "."
              `map)
             [(Term.app
               `eqToHom
               [(Term.proj (Term.app `opens_image_preimage_map_app' [`D `i `j `k `U]) "." `some)])])
            " ≫ "
            `f'))))))
      (Command.declValSimple
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
             ["only"]
             [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `category.assoc)] "]")]
             ["using"
              (Term.app
               `congr_arg
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [`g]
                  []
                  "=>"
                  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `g " ≫ " `f')))
                (Term.app `opens_image_preimage_map_app [`D `i `j `k `U])])]))])))
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
         [(Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            ["only"]
            [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `category.assoc)] "]")]
            ["using"
             (Term.app
              `congr_arg
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`g]
                 []
                 "=>"
                 (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `g " ≫ " `f')))
               (Term.app `opens_image_preimage_map_app [`D `i `j `k `U])])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        ["only"]
        [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `category.assoc)] "]")]
        ["using"
         (Term.app
          `congr_arg
          [(Term.fun
            "fun"
            (Term.basicFun
             [`g]
             []
             "=>"
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `g " ≫ " `f')))
           (Term.app `opens_image_preimage_map_app [`D `i `j `k `U])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `congr_arg
       [(Term.fun
         "fun"
         (Term.basicFun
          [`g]
          []
          "=>"
          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `g " ≫ " `f')))
        (Term.app `opens_image_preimage_map_app [`D `i `j `k `U])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `opens_image_preimage_map_app [`D `i `j `k `U])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `D
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `opens_image_preimage_map_app
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `opens_image_preimage_map_app [`D `i `j `k `U])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`g]
        []
        "=>"
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `g " ≫ " `f')))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `g " ≫ " `f')
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`g]
       []
       "=>"
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_» `g " ≫ " `f')))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `congr_arg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `category.assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app (Term.proj `D "." `opensImagePreimageMap) [`i `j `U])
        " ≫ "
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         (Term.app
          (Term.proj (Term.proj (Term.app (Term.proj `D "." `f) [`j `k]) "." `c) "." `app)
          [(Term.hole "_")])
         " ≫ "
         `f'))
       "="
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app
         (Term.proj
          (Term.proj
           (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
            (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁_,_,_»
             "π₁ "
             `j
             ", "
             `i
             ", "
             `k)
            " ≫ "
            (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
             (Term.app (Term.proj `D "." `t) [`j `i])
             " ≫ "
             (Term.app (Term.proj `D "." `f) [`i `j])))
           "."
           `c)
          "."
          `app)
         [(Term.app `op [`U])])
        " ≫ "
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         (Term.app
          (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₂⁻¹_,_,_»
           "π₂⁻¹ "
           `j
           ", "
           `i
           ", "
           `k)
          [(Term.app `unop [(Term.hole "_")])])
         " ≫ "
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app
           (Term.proj
            (Term.proj
             (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`j "," [`k]] ")")])
             "."
             `Presheaf)
            "."
            `map)
           [(Term.app
             `eqToHom
             [(Term.proj (Term.app `opens_image_preimage_map_app' [`D `i `j `k `U]) "." `some)])])
          " ≫ "
          `f'))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app
        (Term.proj
         (Term.proj
          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
           (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁_,_,_»
            "π₁ "
            `j
            ", "
            `i
            ", "
            `k)
           " ≫ "
           (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
            (Term.app (Term.proj `D "." `t) [`j `i])
            " ≫ "
            (Term.app (Term.proj `D "." `f) [`i `j])))
          "."
          `c)
         "."
         `app)
        [(Term.app `op [`U])])
       " ≫ "
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app
         (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₂⁻¹_,_,_»
          "π₂⁻¹ "
          `j
          ", "
          `i
          ", "
          `k)
         [(Term.app `unop [(Term.hole "_")])])
        " ≫ "
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         (Term.app
          (Term.proj
           (Term.proj
            (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`j "," [`k]] ")")])
            "."
            `Presheaf)
           "."
           `map)
          [(Term.app
            `eqToHom
            [(Term.proj (Term.app `opens_image_preimage_map_app' [`D `i `j `k `U]) "." `some)])])
         " ≫ "
         `f')))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app
        (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₂⁻¹_,_,_»
         "π₂⁻¹ "
         `j
         ", "
         `i
         ", "
         `k)
        [(Term.app `unop [(Term.hole "_")])])
       " ≫ "
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.app
         (Term.proj
          (Term.proj
           (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`j "," [`k]] ")")])
           "."
           `Presheaf)
          "."
          `map)
         [(Term.app
           `eqToHom
           [(Term.proj (Term.app `opens_image_preimage_map_app' [`D `i `j `k `U]) "." `some)])])
        " ≫ "
        `f'))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.app
        (Term.proj
         (Term.proj
          (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`j "," [`k]] ")")])
          "."
          `Presheaf)
         "."
         `map)
        [(Term.app
          `eqToHom
          [(Term.proj (Term.app `opens_image_preimage_map_app' [`D `i `j `k `U]) "." `some)])])
       " ≫ "
       `f')
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app
       (Term.proj
        (Term.proj
         (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`j "," [`k]] ")")])
         "."
         `Presheaf)
        "."
        `map)
       [(Term.app
         `eqToHom
         [(Term.proj (Term.app `opens_image_preimage_map_app' [`D `i `j `k `U]) "." `some)])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `eqToHom
       [(Term.proj (Term.app `opens_image_preimage_map_app' [`D `i `j `k `U]) "." `some)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `opens_image_preimage_map_app' [`D `i `j `k `U]) "." `some)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `opens_image_preimage_map_app' [`D `i `j `k `U])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `D
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `opens_image_preimage_map_app'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `opens_image_preimage_map_app' [`D `i `j `k `U])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eqToHom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `eqToHom
      [(Term.proj
        (Term.paren "(" (Term.app `opens_image_preimage_map_app' [`D `i `j `k `U]) ")")
        "."
        `some)])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.proj
        (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`j "," [`k]] ")")])
        "."
        `Presheaf)
       "."
       `map)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`j "," [`k]] ")")])
       "."
       `Presheaf)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`j "," [`k]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`j "," [`k]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `D "." `V)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `D
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `D "." `V) [(Term.tuple "(" [`j "," [`k]] ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app
       (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₂⁻¹_,_,_»
        "π₂⁻¹ "
        `j
        ", "
        `i
        ", "
        `k)
       [(Term.app `unop [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `unop [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `unop
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `unop [(Term.hole "_")]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₂⁻¹_,_,_»
       "π₂⁻¹ "
       `j
       ", "
       `i
       ", "
       `k)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₂⁻¹_,_,_»', expected 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.termπ₂⁻¹_,_,_._@.AlgebraicGeometry.PresheafedSpace.Gluing._hyg.281'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  opens_image_preimage_map_app_assoc
  ( i j k : D . J ) ( U : Opens D . U i . carrier ) { X' : C } ( f' : _ ⟶ X' )
    :
      D . opensImagePreimageMap i j U ≫ D . f j k . c . app _ ≫ f'
        =
        π₁ j , i , k ≫ D . t j i ≫ D . f i j . c . app op U
          ≫
          π₂⁻¹ j , i , k unop _
            ≫
            D . V ( j , k ) . Presheaf . map eqToHom opens_image_preimage_map_app' D i j k U . some
              ≫
              f'
  :=
    by
      simpa
        only
          [ category.assoc ]
          using congr_arg fun g => g ≫ f' opens_image_preimage_map_app D i j k U
#align
  algebraic_geometry.PresheafedSpace.glue_data.opens_image_preimage_map_app_assoc AlgebraicGeometry.PresheafedSpaceCat.GlueData.opens_image_preimage_map_app_assoc

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "(Implementation) Given an open subset of one of the spaces `U ⊆ Uᵢ`, the sheaf component of\nthe image `ι '' U` in the glued space is the limit of this diagram. -/")]
      []
      []
      []
      []
      [])
     (Command.abbrev
      "abbrev"
      (Command.declId `diagramOverOpen [])
      (Command.optDeclSig
       [(Term.implicitBinder "{" [`i] [":" (Term.proj `D "." `J)] "}")
        (Term.explicitBinder
         "("
         [`U]
         [":" (Term.app `Opens [(Term.proj (Term.app (Term.proj `D "." `U) [`i]) "." `carrier)])]
         []
         ")")]
       [(Term.typeSpec
         ":"
         (CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_»
          (Data.Opposite.«term_ᵒᵖ»
           (Term.app `WalkingMultispan [(Term.hole "_") (Term.hole "_")])
           "ᵒᵖ")
          " ⥤ "
          `C))])
      (Command.declValSimple
       ":="
       (Term.app
        `componentwiseDiagram
        [(Term.proj
          (Term.proj
           (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
            "𝖣")
           "."
           `diagram)
          "."
          `multispan)
         (Term.app
          (Term.proj
           (Term.proj
            (Term.proj (Term.app (Term.proj `D "." `ι_open_embedding) [`i]) "." `IsOpenMap)
            "."
            `Functor)
           "."
           `obj)
          [`U])])
       [])
      []
      []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `componentwiseDiagram
       [(Term.proj
         (Term.proj
          (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
           "𝖣")
          "."
          `diagram)
         "."
         `multispan)
        (Term.app
         (Term.proj
          (Term.proj
           (Term.proj (Term.app (Term.proj `D "." `ι_open_embedding) [`i]) "." `IsOpenMap)
           "."
           `Functor)
          "."
          `obj)
         [`U])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.proj
         (Term.proj (Term.app (Term.proj `D "." `ι_open_embedding) [`i]) "." `IsOpenMap)
         "."
         `Functor)
        "."
        `obj)
       [`U])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.proj
        (Term.proj (Term.app (Term.proj `D "." `ι_open_embedding) [`i]) "." `IsOpenMap)
        "."
        `Functor)
       "."
       `obj)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.proj (Term.app (Term.proj `D "." `ι_open_embedding) [`i]) "." `IsOpenMap)
       "."
       `Functor)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app (Term.proj `D "." `ι_open_embedding) [`i]) "." `IsOpenMap)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `D "." `ι_open_embedding) [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `D "." `ι_open_embedding)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `D
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `D "." `ι_open_embedding) [`i])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj
       (Term.proj
        (Term.proj
         (Term.paren "(" (Term.app (Term.proj `D "." `ι_open_embedding) [`i]) ")")
         "."
         `IsOpenMap)
        "."
        `Functor)
       "."
       `obj)
      [`U])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.proj
        (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
         "𝖣")
        "."
        `diagram)
       "."
       `multispan)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
        "𝖣")
       "."
       `diagram)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
       "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»', expected 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.term𝖣._@.AlgebraicGeometry.PresheafedSpace.Gluing._hyg.31'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    (Implementation) Given an open subset of one of the spaces `U ⊆ Uᵢ`, the sheaf component of
    the image `ι '' U` in the glued space is the limit of this diagram. -/
  abbrev
    diagramOverOpen
    { i : D . J } ( U : Opens D . U i . carrier ) : WalkingMultispan _ _ ᵒᵖ ⥤ C
    :=
      componentwiseDiagram
        𝖣 . diagram . multispan D . ι_open_embedding i . IsOpenMap . Functor . obj U
#align
  algebraic_geometry.PresheafedSpace.glue_data.diagram_over_open AlgebraicGeometry.PresheafedSpaceCat.GlueData.diagramOverOpen

/-- (Implementation)
The projection from the limit of `diagram_over_open` to a component of `D.U j`. -/
abbrev diagramOverOpenπ {i : D.J} (U : Opens (D.U i).carrier) (j : D.J) :=
  limit.π (D.diagramOverOpen U) (op (WalkingMultispan.right j))
#align
  algebraic_geometry.PresheafedSpace.glue_data.diagram_over_open_π AlgebraicGeometry.PresheafedSpaceCat.GlueData.diagramOverOpenπ

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "(Implementation) We construct the map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_V, U_V)` for each `V` in the gluing\ndiagram. We will lift these maps into `ι_inv_app`. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `ιInvAppπApp [])
      (Command.optDeclSig
       [(Term.implicitBinder "{" [`i] [":" (Term.proj `D "." `J)] "}")
        (Term.explicitBinder
         "("
         [`U]
         [":" (Term.app `Opens [(Term.proj (Term.app (Term.proj `D "." `U) [`i]) "." `carrier)])]
         []
         ")")
        (Term.explicitBinder "(" [`j] [] [] ")")]
       [(Term.typeSpec
         ":"
         (Combinatorics.Quiver.Basic.«term_⟶_»
          (Term.app
           (Term.proj
            (Term.proj
             (Term.app
              (Term.proj
               (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                "𝖣")
               "."
               `U)
              [`i])
             "."
             `Presheaf)
            "."
            `obj)
           [(Term.app `op [`U])])
          " ⟶ "
          (Term.app
           (Term.proj (Term.app (Term.proj `D "." `diagramOverOpen) [`U]) "." `obj)
           [(Term.app `op [`j])])))])
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.rcases
            "rcases"
            [(Tactic.casesTarget [] `j)]
            ["with"
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.paren
                 "("
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                       [])]
                     "⟩")
                    "|"
                    (Std.Tactic.RCases.rcasesPat.one `j)])
                  [])
                 ")")])
              [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.refine'
              "refine'"
              (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
               (Term.app `D.opens_image_preimage_map [`i `j `U])
               " ≫ "
               (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                (Term.app
                 (Term.proj (Term.proj (Term.app `D.f [`j `k]) "." `c) "." `app)
                 [(Term.hole "_")])
                " ≫ "
                (Term.app
                 (Term.proj
                  (Term.proj (Term.app `D.V [(Term.tuple "(" [`j "," [`k]] ")")]) "." `Presheaf)
                  "."
                  `map)
                 [(Term.app `eq_to_hom [(Term.hole "_")])]))))
             []
             (Tactic.dsimp
              "dsimp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `functor.op)
                ","
                (Tactic.simpLemma [] [] `opens.map)
                ","
                (Tactic.simpLemma [] [] `unop_op)]
               "]"]
              [])
             []
             (Tactic.congr "congr" [(num "2")])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.preimage_preimage)] "]")
              [])
             []
             (Tactic.change
              "change"
              («term_=_»
               (Set.Data.Set.Image.«term_⁻¹'_»
                (Term.proj
                 (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                  (Term.app `D.f [`j `k])
                  " ≫ "
                  (Term.app
                   (Term.proj
                    (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                     "𝖣")
                    "."
                    `ι)
                   [`j]))
                 "."
                 `base)
                " ⁻¹' "
                (Term.hole "_"))
               "="
               (Term.hole "_"))
              [])
             []
             (Tactic.congr "congr" [(num "3")])
             []
             (Tactic.exact
              "exact"
              (Term.app
               `colimit.w
               [(Term.proj
                 (Term.proj
                  (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                   "𝖣")
                  "."
                  `diagram)
                 "."
                 `multispan)
                (Term.app `walking_multispan.hom.fst [(Term.tuple "(" [`j "," [`k]] ")")])]))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.exact "exact" (Term.app `D.opens_image_preimage_map [`i `j `U]))])])))
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
         [(Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] `j)]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.paren
                "("
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                      [])]
                    "⟩")
                   "|"
                   (Std.Tactic.RCases.rcasesPat.one `j)])
                 [])
                ")")])
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.refine'
             "refine'"
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
              (Term.app `D.opens_image_preimage_map [`i `j `U])
              " ≫ "
              (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
               (Term.app
                (Term.proj (Term.proj (Term.app `D.f [`j `k]) "." `c) "." `app)
                [(Term.hole "_")])
               " ≫ "
               (Term.app
                (Term.proj
                 (Term.proj (Term.app `D.V [(Term.tuple "(" [`j "," [`k]] ")")]) "." `Presheaf)
                 "."
                 `map)
                [(Term.app `eq_to_hom [(Term.hole "_")])]))))
            []
            (Tactic.dsimp
             "dsimp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `functor.op)
               ","
               (Tactic.simpLemma [] [] `opens.map)
               ","
               (Tactic.simpLemma [] [] `unop_op)]
              "]"]
             [])
            []
            (Tactic.congr "congr" [(num "2")])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.preimage_preimage)] "]")
             [])
            []
            (Tactic.change
             "change"
             («term_=_»
              (Set.Data.Set.Image.«term_⁻¹'_»
               (Term.proj
                (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                 (Term.app `D.f [`j `k])
                 " ≫ "
                 (Term.app
                  (Term.proj
                   (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                    "𝖣")
                   "."
                   `ι)
                  [`j]))
                "."
                `base)
               " ⁻¹' "
               (Term.hole "_"))
              "="
              (Term.hole "_"))
             [])
            []
            (Tactic.congr "congr" [(num "3")])
            []
            (Tactic.exact
             "exact"
             (Term.app
              `colimit.w
              [(Term.proj
                (Term.proj
                 (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                  "𝖣")
                 "."
                 `diagram)
                "."
                `multispan)
               (Term.app `walking_multispan.hom.fst [(Term.tuple "(" [`j "," [`k]] ")")])]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact "exact" (Term.app `D.opens_image_preimage_map [`i `j `U]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact "exact" (Term.app `D.opens_image_preimage_map [`i `j `U]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `D.opens_image_preimage_map [`i `j `U]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `D.opens_image_preimage_map [`i `j `U])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `D.opens_image_preimage_map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.refine'
         "refine'"
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app `D.opens_image_preimage_map [`i `j `U])
          " ≫ "
          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
           (Term.app
            (Term.proj (Term.proj (Term.app `D.f [`j `k]) "." `c) "." `app)
            [(Term.hole "_")])
           " ≫ "
           (Term.app
            (Term.proj
             (Term.proj (Term.app `D.V [(Term.tuple "(" [`j "," [`k]] ")")]) "." `Presheaf)
             "."
             `map)
            [(Term.app `eq_to_hom [(Term.hole "_")])]))))
        []
        (Tactic.dsimp
         "dsimp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `functor.op)
           ","
           (Tactic.simpLemma [] [] `opens.map)
           ","
           (Tactic.simpLemma [] [] `unop_op)]
          "]"]
         [])
        []
        (Tactic.congr "congr" [(num "2")])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.preimage_preimage)] "]")
         [])
        []
        (Tactic.change
         "change"
         («term_=_»
          (Set.Data.Set.Image.«term_⁻¹'_»
           (Term.proj
            (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
             (Term.app `D.f [`j `k])
             " ≫ "
             (Term.app
              (Term.proj
               (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                "𝖣")
               "."
               `ι)
              [`j]))
            "."
            `base)
           " ⁻¹' "
           (Term.hole "_"))
          "="
          (Term.hole "_"))
         [])
        []
        (Tactic.congr "congr" [(num "3")])
        []
        (Tactic.exact
         "exact"
         (Term.app
          `colimit.w
          [(Term.proj
            (Term.proj
             (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
              "𝖣")
             "."
             `diagram)
            "."
            `multispan)
           (Term.app `walking_multispan.hom.fst [(Term.tuple "(" [`j "," [`k]] ")")])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `colimit.w
        [(Term.proj
          (Term.proj
           (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
            "𝖣")
           "."
           `diagram)
          "."
          `multispan)
         (Term.app `walking_multispan.hom.fst [(Term.tuple "(" [`j "," [`k]] ")")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `colimit.w
       [(Term.proj
         (Term.proj
          (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
           "𝖣")
          "."
          `diagram)
         "."
         `multispan)
        (Term.app `walking_multispan.hom.fst [(Term.tuple "(" [`j "," [`k]] ")")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `walking_multispan.hom.fst [(Term.tuple "(" [`j "," [`k]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`j "," [`k]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `walking_multispan.hom.fst
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `walking_multispan.hom.fst [(Term.tuple "(" [`j "," [`k]] ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.proj
        (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
         "𝖣")
        "."
        `diagram)
       "."
       `multispan)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
        "𝖣")
       "."
       `diagram)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
       "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»', expected 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.term𝖣._@.AlgebraicGeometry.PresheafedSpace.Gluing._hyg.31'
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
    (Implementation) We construct the map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_V, U_V)` for each `V` in the gluing
    diagram. We will lift these maps into `ι_inv_app`. -/
  def
    ιInvAppπApp
    { i : D . J } ( U : Opens D . U i . carrier ) ( j )
      : 𝖣 . U i . Presheaf . obj op U ⟶ D . diagramOverOpen U . obj op j
    :=
      by
        rcases j with ( ⟨ j , k ⟩ | j )
          ·
            refine'
                D.opens_image_preimage_map i j U
                  ≫
                  D.f j k . c . app _ ≫ D.V ( j , k ) . Presheaf . map eq_to_hom _
              dsimp only [ functor.op , opens.map , unop_op ]
              congr 2
              rw [ Set.preimage_preimage ]
              change D.f j k ≫ 𝖣 . ι j . base ⁻¹' _ = _
              congr 3
              exact colimit.w 𝖣 . diagram . multispan walking_multispan.hom.fst ( j , k )
          · exact D.opens_image_preimage_map i j U
#align
  algebraic_geometry.PresheafedSpace.glue_data.ι_inv_app_π_app AlgebraicGeometry.PresheafedSpaceCat.GlueData.ιInvAppπApp

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "(Implementation) The natural map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_X, 𝖣.ι i '' U)`.\nThis forms the inverse of `(𝖣.ι i).c.app (op U)`. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `ιInvApp [])
      (Command.optDeclSig
       [(Term.implicitBinder "{" [`i] [":" (Term.proj `D "." `J)] "}")
        (Term.explicitBinder
         "("
         [`U]
         [":" (Term.app `Opens [(Term.proj (Term.app (Term.proj `D "." `U) [`i]) "." `carrier)])]
         []
         ")")]
       [(Term.typeSpec
         ":"
         (Combinatorics.Quiver.Basic.«term_⟶_»
          (Term.app
           (Term.proj (Term.proj (Term.app (Term.proj `D "." `U) [`i]) "." `Presheaf) "." `obj)
           [(Term.app `op [`U])])
          " ⟶ "
          (Term.app `limit [(Term.app (Term.proj `D "." `diagramOverOpen) [`U])])))])
      (Command.declValSimple
       ":="
       (Term.app
        `limit.lift
        [(Term.app (Term.proj `D "." `diagramOverOpen) [`U])
         (Term.structInst
          "{"
          []
          [(Term.structInstField
            (Term.structInstLVal `x [])
            ":="
            (Term.app
             (Term.proj (Term.proj (Term.app (Term.proj `D "." `U) [`i]) "." `Presheaf) "." `obj)
             [(Term.app `op [`U])]))
           []
           (Term.structInstField
            (Term.structInstLVal `π [])
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
                 (Term.app (Term.proj `D "." `ιInvAppπApp) [`U (Term.app `unop [`j])]))))
              []
              (Term.structInstField
               (Term.structInstLVal `naturality' [])
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [`X `Y `f']
                 []
                 "=>"
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.induction "induction" [`X] ["using" `Opposite.rec] [] [])
                     []
                     (Tactic.induction "induction" [`Y] ["using" `Opposite.rec] [] [])
                     []
                     (Tactic.tacticLet_
                      "let"
                      (Term.letDecl
                       (Term.letIdDecl
                        `f
                        []
                        [(Term.typeSpec ":" (Combinatorics.Quiver.Basic.«term_⟶_» `Y " ⟶ " `X))]
                        ":="
                        `f'.unop)))
                     []
                     (Tactic.tacticHave_
                      "have"
                      (Term.haveDecl
                       (Term.haveIdDecl
                        []
                        [(Term.typeSpec ":" («term_=_» `f' "=" `f.op))]
                        ":="
                        `rfl)))
                     []
                     (Tactic.clearValue "clear_value" [(group `f)])
                     []
                     (Tactic.subst "subst" [`this])
                     []
                     (Std.Tactic.rcases
                      "rcases"
                      [(Tactic.casesTarget [] `f)]
                      ["with"
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed
                         [(Std.Tactic.RCases.rcasesPat.paren
                           "("
                           (Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed
                             [(Std.Tactic.RCases.rcasesPat.ignore "_")
                              "|"
                              (Std.Tactic.RCases.rcasesPat.tuple
                               "⟨"
                               [(Std.Tactic.RCases.rcasesPatLo
                                 (Std.Tactic.RCases.rcasesPatMed
                                  [(Std.Tactic.RCases.rcasesPat.one `j)])
                                 [])
                                ","
                                (Std.Tactic.RCases.rcasesPatLo
                                 (Std.Tactic.RCases.rcasesPatMed
                                  [(Std.Tactic.RCases.rcasesPat.one `k)])
                                 [])]
                               "⟩")
                              "|"
                              (Std.Tactic.RCases.rcasesPat.tuple
                               "⟨"
                               [(Std.Tactic.RCases.rcasesPatLo
                                 (Std.Tactic.RCases.rcasesPatMed
                                  [(Std.Tactic.RCases.rcasesPat.one `j)])
                                 [])
                                ","
                                (Std.Tactic.RCases.rcasesPatLo
                                 (Std.Tactic.RCases.rcasesPatMed
                                  [(Std.Tactic.RCases.rcasesPat.one `k)])
                                 [])]
                               "⟩")])
                            [])
                           ")")])
                        [])])
                     []
                     (tactic__
                      (cdotTk (patternIgnore (token.«· » "·")))
                      [(Tactic.tacticErw__
                        "erw"
                        (Tactic.rwRuleSeq
                         "["
                         [(Tactic.rwRule [] `category.id_comp)
                          ","
                          (Tactic.rwRule [] `CategoryTheory.Functor.map_id)]
                         "]")
                        [])
                       []
                       (Tactic.rwSeq
                        "rw"
                        []
                        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.comp_id)] "]")
                        [])])
                     []
                     (tactic__
                      (cdotTk (patternIgnore (token.«· » "·")))
                      [(Tactic.tacticErw__
                        "erw"
                        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.id_comp)] "]")
                        [])
                       []
                       (Tactic.congr "congr" [(num "1")])])
                     []
                     (Tactic.tacticErw__
                      "erw"
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.id_comp)] "]")
                      [])
                     []
                     (Tactic.change
                      "change"
                      («term_=_»
                       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                        (Term.app `D.opens_image_preimage_map [`i `j `U])
                        " ≫ "
                        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                         (Term.app
                          (Term.proj (Term.proj (Term.app `D.f [`j `k]) "." `c) "." `app)
                          [(Term.hole "_")])
                         " ≫ "
                         (Term.app
                          (Term.proj
                           (Term.proj
                            (Term.app `D.V [(Term.tuple "(" [`j "," [`k]] ")")])
                            "."
                            `Presheaf)
                           "."
                           `map)
                          [(Term.app `eq_to_hom [(Term.hole "_")])])))
                       "="
                       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                        (Term.app
                         `D.opens_image_preimage_map
                         [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                        " ≫ "
                        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                          (Term.app
                           (Term.proj (Term.proj (Term.app `D.f [`k `j]) "." `c) "." `app)
                           [(Term.hole "_")])
                          " ≫ "
                          (Term.app
                           (Term.proj (Term.proj (Term.app `D.t [`j `k]) "." `c) "." `app)
                           [(Term.hole "_")]))
                         " ≫ "
                         (Term.app
                          (Term.proj
                           (Term.proj
                            (Term.app `D.V [(Term.tuple "(" [`j "," [`k]] ")")])
                            "."
                            `Presheaf)
                           "."
                           `map)
                          [(Term.app `eq_to_hom [(Term.hole "_")])]))))
                      [])
                     []
                     (Tactic.tacticErw__
                      "erw"
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [] `opens_image_preimage_map_app_assoc)]
                       "]")
                      [])
                     []
                     (Mathlib.Tactic.tacticSimp_rw__
                      "simp_rw"
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
                      [])
                     []
                     (Tactic.tacticErw__
                      "erw"
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [] `opens_image_preimage_map_app_assoc)
                        ","
                        (Tactic.rwRule
                         []
                         (Term.proj
                          (Term.proj (Term.app `D.t [`j `k]) "." `c)
                          "."
                          `naturality_assoc))]
                       "]")
                      [])
                     []
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `snd_inv_app_t_app_assoc)] "]")
                      [])
                     []
                     (Tactic.tacticErw__
                      "erw"
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule
                         [(patternIgnore (token.«← » "←"))]
                         `PresheafedSpace.comp_c_app_assoc)]
                       "]")
                      [])
                     []
                     (Tactic.tacticHave_
                      "have"
                      (Term.haveDecl
                       (Term.haveIdDecl
                        []
                        [(Term.typeSpec
                          ":"
                          («term_=_»
                           (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                            (Term.app `D.t' [`j `k `i])
                            " ≫ "
                            (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                             (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁_,_,_»
                              "π₁ "
                              `k
                              ", "
                              `i
                              ", "
                              `j)
                             " ≫ "
                             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                              (Term.app `D.t [`k `i])
                              " ≫ "
                              (Term.app
                               (Term.proj
                                (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                                 "𝖣")
                                "."
                                `f)
                               [`i `k]))))
                           "="
                           (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                            (Term.proj
                             (Term.app `pullback_symmetry [(Term.hole "_") (Term.hole "_")])
                             "."
                             `Hom)
                            " ≫ "
                            (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                             (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁_,_,_»
                              "π₁ "
                              `j
                              ", "
                              `i
                              ", "
                              `k)
                             " ≫ "
                             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                              (Term.app `D.t [`j `i])
                              " ≫ "
                              (Term.app `D.f [`i `j]))))))]
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
                                (Term.proj
                                 (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                                  "𝖣")
                                 "."
                                 `t_fac_assoc))
                               ","
                               (Tactic.rwRule
                                []
                                (Term.proj
                                 (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                                  "𝖣")
                                 "."
                                 `t'_comp_eq_pullback_symmetry_assoc))
                               ","
                               (Tactic.rwRule [] `pullback_symmetry_hom_comp_snd_assoc)
                               ","
                               (Tactic.rwRule [] `pullback.condition)
                               ","
                               (Tactic.rwRule
                                []
                                (Term.proj
                                 (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                                  "𝖣")
                                 "."
                                 `t_fac_assoc))]
                              "]")
                             [])]))))))
                     []
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `congr_app [`this]))] "]")
                      [])
                     []
                     (Tactic.tacticErw__
                      "erw"
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule
                         []
                         (Term.app
                          `PresheafedSpace.comp_c_app_assoc
                          [(Term.proj
                            (Term.app `pullback_symmetry [(Term.hole "_") (Term.hole "_")])
                            "."
                            `Hom)]))]
                       "]")
                      [])
                     []
                     (Mathlib.Tactic.tacticSimp_rw__
                      "simp_rw"
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
                      [])
                     []
                     (Tactic.congr "congr" [(num "1")])
                     []
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `is_iso.eq_inv_comp)]
                       "]")
                      [])
                     []
                     (Tactic.tacticErw__
                      "erw"
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `is_open_immersion.inv_inv_app)] "]")
                      [])
                     []
                     (Mathlib.Tactic.tacticSimp_rw__
                      "simp_rw"
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
                      [])
                     []
                     (Tactic.tacticErw__
                      "erw"
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [] `nat_trans.naturality_assoc)
                        ","
                        (Tactic.rwRule
                         [(patternIgnore (token.«← » "←"))]
                         `PresheafedSpace.comp_c_app_assoc)
                        ","
                        (Tactic.rwRule
                         []
                         (Term.app
                          `congr_app
                          [(Term.app
                            `pullback_symmetry_hom_comp_snd
                            [(Term.hole "_") (Term.hole "_")])]))]
                       "]")
                      [])
                     []
                     (Mathlib.Tactic.tacticSimp_rw__
                      "simp_rw"
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
                      [])
                     []
                     (Tactic.tacticErw__
                      "erw"
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [] `is_open_immersion.inv_naturality_assoc)
                        ","
                        (Tactic.rwRule [] `is_open_immersion.inv_naturality_assoc)
                        ","
                        (Tactic.rwRule [] `is_open_immersion.inv_naturality_assoc)
                        ","
                        (Tactic.rwRule [] `is_open_immersion.app_inv_app_assoc)]
                       "]")
                      [])
                     []
                     (Std.Tactic.tacticRepeat'_
                      "repeat'"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.tacticErw__
                          "erw"
                          (Tactic.rwRuleSeq
                           "["
                           [(Tactic.rwRule
                             [(patternIgnore (token.«← » "←"))]
                             (Term.proj
                              (Term.proj
                               (Term.app `D.V [(Term.tuple "(" [`j "," [`k]] ")")])
                               "."
                               `Presheaf)
                              "."
                              `map_comp))]
                           "]")
                          [])])))
                     []
                     (Tactic.congr "congr" [])]))))))]
             (Term.optEllipsis [])
             []
             "}"))]
          (Term.optEllipsis [])
          []
          "}")])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `limit.lift
       [(Term.app (Term.proj `D "." `diagramOverOpen) [`U])
        (Term.structInst
         "{"
         []
         [(Term.structInstField
           (Term.structInstLVal `x [])
           ":="
           (Term.app
            (Term.proj (Term.proj (Term.app (Term.proj `D "." `U) [`i]) "." `Presheaf) "." `obj)
            [(Term.app `op [`U])]))
          []
          (Term.structInstField
           (Term.structInstLVal `π [])
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
                (Term.app (Term.proj `D "." `ιInvAppπApp) [`U (Term.app `unop [`j])]))))
             []
             (Term.structInstField
              (Term.structInstLVal `naturality' [])
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`X `Y `f']
                []
                "=>"
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.induction "induction" [`X] ["using" `Opposite.rec] [] [])
                    []
                    (Tactic.induction "induction" [`Y] ["using" `Opposite.rec] [] [])
                    []
                    (Tactic.tacticLet_
                     "let"
                     (Term.letDecl
                      (Term.letIdDecl
                       `f
                       []
                       [(Term.typeSpec ":" (Combinatorics.Quiver.Basic.«term_⟶_» `Y " ⟶ " `X))]
                       ":="
                       `f'.unop)))
                    []
                    (Tactic.tacticHave_
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       []
                       [(Term.typeSpec ":" («term_=_» `f' "=" `f.op))]
                       ":="
                       `rfl)))
                    []
                    (Tactic.clearValue "clear_value" [(group `f)])
                    []
                    (Tactic.subst "subst" [`this])
                    []
                    (Std.Tactic.rcases
                     "rcases"
                     [(Tactic.casesTarget [] `f)]
                     ["with"
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.paren
                          "("
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed
                            [(Std.Tactic.RCases.rcasesPat.ignore "_")
                             "|"
                             (Std.Tactic.RCases.rcasesPat.tuple
                              "⟨"
                              [(Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.one `j)])
                                [])
                               ","
                               (Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.one `k)])
                                [])]
                              "⟩")
                             "|"
                             (Std.Tactic.RCases.rcasesPat.tuple
                              "⟨"
                              [(Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.one `j)])
                                [])
                               ","
                               (Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.one `k)])
                                [])]
                              "⟩")])
                           [])
                          ")")])
                       [])])
                    []
                    (tactic__
                     (cdotTk (patternIgnore (token.«· » "·")))
                     [(Tactic.tacticErw__
                       "erw"
                       (Tactic.rwRuleSeq
                        "["
                        [(Tactic.rwRule [] `category.id_comp)
                         ","
                         (Tactic.rwRule [] `CategoryTheory.Functor.map_id)]
                        "]")
                       [])
                      []
                      (Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.comp_id)] "]")
                       [])])
                    []
                    (tactic__
                     (cdotTk (patternIgnore (token.«· » "·")))
                     [(Tactic.tacticErw__
                       "erw"
                       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.id_comp)] "]")
                       [])
                      []
                      (Tactic.congr "congr" [(num "1")])])
                    []
                    (Tactic.tacticErw__
                     "erw"
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.id_comp)] "]")
                     [])
                    []
                    (Tactic.change
                     "change"
                     («term_=_»
                      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                       (Term.app `D.opens_image_preimage_map [`i `j `U])
                       " ≫ "
                       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                        (Term.app
                         (Term.proj (Term.proj (Term.app `D.f [`j `k]) "." `c) "." `app)
                         [(Term.hole "_")])
                        " ≫ "
                        (Term.app
                         (Term.proj
                          (Term.proj
                           (Term.app `D.V [(Term.tuple "(" [`j "," [`k]] ")")])
                           "."
                           `Presheaf)
                          "."
                          `map)
                         [(Term.app `eq_to_hom [(Term.hole "_")])])))
                      "="
                      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                       (Term.app
                        `D.opens_image_preimage_map
                        [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                       " ≫ "
                       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                         (Term.app
                          (Term.proj (Term.proj (Term.app `D.f [`k `j]) "." `c) "." `app)
                          [(Term.hole "_")])
                         " ≫ "
                         (Term.app
                          (Term.proj (Term.proj (Term.app `D.t [`j `k]) "." `c) "." `app)
                          [(Term.hole "_")]))
                        " ≫ "
                        (Term.app
                         (Term.proj
                          (Term.proj
                           (Term.app `D.V [(Term.tuple "(" [`j "," [`k]] ")")])
                           "."
                           `Presheaf)
                          "."
                          `map)
                         [(Term.app `eq_to_hom [(Term.hole "_")])]))))
                     [])
                    []
                    (Tactic.tacticErw__
                     "erw"
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] `opens_image_preimage_map_app_assoc)]
                      "]")
                     [])
                    []
                    (Mathlib.Tactic.tacticSimp_rw__
                     "simp_rw"
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
                     [])
                    []
                    (Tactic.tacticErw__
                     "erw"
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] `opens_image_preimage_map_app_assoc)
                       ","
                       (Tactic.rwRule
                        []
                        (Term.proj
                         (Term.proj (Term.app `D.t [`j `k]) "." `c)
                         "."
                         `naturality_assoc))]
                      "]")
                     [])
                    []
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `snd_inv_app_t_app_assoc)] "]")
                     [])
                    []
                    (Tactic.tacticErw__
                     "erw"
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule
                        [(patternIgnore (token.«← » "←"))]
                        `PresheafedSpace.comp_c_app_assoc)]
                      "]")
                     [])
                    []
                    (Tactic.tacticHave_
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       []
                       [(Term.typeSpec
                         ":"
                         («term_=_»
                          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                           (Term.app `D.t' [`j `k `i])
                           " ≫ "
                           (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                            (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁_,_,_»
                             "π₁ "
                             `k
                             ", "
                             `i
                             ", "
                             `j)
                            " ≫ "
                            (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                             (Term.app `D.t [`k `i])
                             " ≫ "
                             (Term.app
                              (Term.proj
                               (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                                "𝖣")
                               "."
                               `f)
                              [`i `k]))))
                          "="
                          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                           (Term.proj
                            (Term.app `pullback_symmetry [(Term.hole "_") (Term.hole "_")])
                            "."
                            `Hom)
                           " ≫ "
                           (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                            (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁_,_,_»
                             "π₁ "
                             `j
                             ", "
                             `i
                             ", "
                             `k)
                            " ≫ "
                            (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                             (Term.app `D.t [`j `i])
                             " ≫ "
                             (Term.app `D.f [`i `j]))))))]
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
                               (Term.proj
                                (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                                 "𝖣")
                                "."
                                `t_fac_assoc))
                              ","
                              (Tactic.rwRule
                               []
                               (Term.proj
                                (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                                 "𝖣")
                                "."
                                `t'_comp_eq_pullback_symmetry_assoc))
                              ","
                              (Tactic.rwRule [] `pullback_symmetry_hom_comp_snd_assoc)
                              ","
                              (Tactic.rwRule [] `pullback.condition)
                              ","
                              (Tactic.rwRule
                               []
                               (Term.proj
                                (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                                 "𝖣")
                                "."
                                `t_fac_assoc))]
                             "]")
                            [])]))))))
                    []
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `congr_app [`this]))] "]")
                     [])
                    []
                    (Tactic.tacticErw__
                     "erw"
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule
                        []
                        (Term.app
                         `PresheafedSpace.comp_c_app_assoc
                         [(Term.proj
                           (Term.app `pullback_symmetry [(Term.hole "_") (Term.hole "_")])
                           "."
                           `Hom)]))]
                      "]")
                     [])
                    []
                    (Mathlib.Tactic.tacticSimp_rw__
                     "simp_rw"
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
                     [])
                    []
                    (Tactic.congr "congr" [(num "1")])
                    []
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `is_iso.eq_inv_comp)]
                      "]")
                     [])
                    []
                    (Tactic.tacticErw__
                     "erw"
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `is_open_immersion.inv_inv_app)] "]")
                     [])
                    []
                    (Mathlib.Tactic.tacticSimp_rw__
                     "simp_rw"
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
                     [])
                    []
                    (Tactic.tacticErw__
                     "erw"
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] `nat_trans.naturality_assoc)
                       ","
                       (Tactic.rwRule
                        [(patternIgnore (token.«← » "←"))]
                        `PresheafedSpace.comp_c_app_assoc)
                       ","
                       (Tactic.rwRule
                        []
                        (Term.app
                         `congr_app
                         [(Term.app
                           `pullback_symmetry_hom_comp_snd
                           [(Term.hole "_") (Term.hole "_")])]))]
                      "]")
                     [])
                    []
                    (Mathlib.Tactic.tacticSimp_rw__
                     "simp_rw"
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
                     [])
                    []
                    (Tactic.tacticErw__
                     "erw"
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] `is_open_immersion.inv_naturality_assoc)
                       ","
                       (Tactic.rwRule [] `is_open_immersion.inv_naturality_assoc)
                       ","
                       (Tactic.rwRule [] `is_open_immersion.inv_naturality_assoc)
                       ","
                       (Tactic.rwRule [] `is_open_immersion.app_inv_app_assoc)]
                      "]")
                     [])
                    []
                    (Std.Tactic.tacticRepeat'_
                     "repeat'"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.tacticErw__
                         "erw"
                         (Tactic.rwRuleSeq
                          "["
                          [(Tactic.rwRule
                            [(patternIgnore (token.«← » "←"))]
                            (Term.proj
                             (Term.proj
                              (Term.app `D.V [(Term.tuple "(" [`j "," [`k]] ")")])
                              "."
                              `Presheaf)
                             "."
                             `map_comp))]
                          "]")
                         [])])))
                    []
                    (Tactic.congr "congr" [])]))))))]
            (Term.optEllipsis [])
            []
            "}"))]
         (Term.optEllipsis [])
         []
         "}")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       []
       [(Term.structInstField
         (Term.structInstLVal `x [])
         ":="
         (Term.app
          (Term.proj (Term.proj (Term.app (Term.proj `D "." `U) [`i]) "." `Presheaf) "." `obj)
          [(Term.app `op [`U])]))
        []
        (Term.structInstField
         (Term.structInstLVal `π [])
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
              (Term.app (Term.proj `D "." `ιInvAppπApp) [`U (Term.app `unop [`j])]))))
           []
           (Term.structInstField
            (Term.structInstLVal `naturality' [])
            ":="
            (Term.fun
             "fun"
             (Term.basicFun
              [`X `Y `f']
              []
              "=>"
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.induction "induction" [`X] ["using" `Opposite.rec] [] [])
                  []
                  (Tactic.induction "induction" [`Y] ["using" `Opposite.rec] [] [])
                  []
                  (Tactic.tacticLet_
                   "let"
                   (Term.letDecl
                    (Term.letIdDecl
                     `f
                     []
                     [(Term.typeSpec ":" (Combinatorics.Quiver.Basic.«term_⟶_» `Y " ⟶ " `X))]
                     ":="
                     `f'.unop)))
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl [] [(Term.typeSpec ":" («term_=_» `f' "=" `f.op))] ":=" `rfl)))
                  []
                  (Tactic.clearValue "clear_value" [(group `f)])
                  []
                  (Tactic.subst "subst" [`this])
                  []
                  (Std.Tactic.rcases
                   "rcases"
                   [(Tactic.casesTarget [] `f)]
                   ["with"
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.paren
                        "("
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed
                          [(Std.Tactic.RCases.rcasesPat.ignore "_")
                           "|"
                           (Std.Tactic.RCases.rcasesPat.tuple
                            "⟨"
                            [(Std.Tactic.RCases.rcasesPatLo
                              (Std.Tactic.RCases.rcasesPatMed
                               [(Std.Tactic.RCases.rcasesPat.one `j)])
                              [])
                             ","
                             (Std.Tactic.RCases.rcasesPatLo
                              (Std.Tactic.RCases.rcasesPatMed
                               [(Std.Tactic.RCases.rcasesPat.one `k)])
                              [])]
                            "⟩")
                           "|"
                           (Std.Tactic.RCases.rcasesPat.tuple
                            "⟨"
                            [(Std.Tactic.RCases.rcasesPatLo
                              (Std.Tactic.RCases.rcasesPatMed
                               [(Std.Tactic.RCases.rcasesPat.one `j)])
                              [])
                             ","
                             (Std.Tactic.RCases.rcasesPatLo
                              (Std.Tactic.RCases.rcasesPatMed
                               [(Std.Tactic.RCases.rcasesPat.one `k)])
                              [])]
                            "⟩")])
                         [])
                        ")")])
                     [])])
                  []
                  (tactic__
                   (cdotTk (patternIgnore (token.«· » "·")))
                   [(Tactic.tacticErw__
                     "erw"
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] `category.id_comp)
                       ","
                       (Tactic.rwRule [] `CategoryTheory.Functor.map_id)]
                      "]")
                     [])
                    []
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.comp_id)] "]")
                     [])])
                  []
                  (tactic__
                   (cdotTk (patternIgnore (token.«· » "·")))
                   [(Tactic.tacticErw__
                     "erw"
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.id_comp)] "]")
                     [])
                    []
                    (Tactic.congr "congr" [(num "1")])])
                  []
                  (Tactic.tacticErw__
                   "erw"
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.id_comp)] "]")
                   [])
                  []
                  (Tactic.change
                   "change"
                   («term_=_»
                    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                     (Term.app `D.opens_image_preimage_map [`i `j `U])
                     " ≫ "
                     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                      (Term.app
                       (Term.proj (Term.proj (Term.app `D.f [`j `k]) "." `c) "." `app)
                       [(Term.hole "_")])
                      " ≫ "
                      (Term.app
                       (Term.proj
                        (Term.proj
                         (Term.app `D.V [(Term.tuple "(" [`j "," [`k]] ")")])
                         "."
                         `Presheaf)
                        "."
                        `map)
                       [(Term.app `eq_to_hom [(Term.hole "_")])])))
                    "="
                    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                     (Term.app
                      `D.opens_image_preimage_map
                      [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                     " ≫ "
                     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                       (Term.app
                        (Term.proj (Term.proj (Term.app `D.f [`k `j]) "." `c) "." `app)
                        [(Term.hole "_")])
                       " ≫ "
                       (Term.app
                        (Term.proj (Term.proj (Term.app `D.t [`j `k]) "." `c) "." `app)
                        [(Term.hole "_")]))
                      " ≫ "
                      (Term.app
                       (Term.proj
                        (Term.proj
                         (Term.app `D.V [(Term.tuple "(" [`j "," [`k]] ")")])
                         "."
                         `Presheaf)
                        "."
                        `map)
                       [(Term.app `eq_to_hom [(Term.hole "_")])]))))
                   [])
                  []
                  (Tactic.tacticErw__
                   "erw"
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `opens_image_preimage_map_app_assoc)]
                    "]")
                   [])
                  []
                  (Mathlib.Tactic.tacticSimp_rw__
                   "simp_rw"
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
                   [])
                  []
                  (Tactic.tacticErw__
                   "erw"
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `opens_image_preimage_map_app_assoc)
                     ","
                     (Tactic.rwRule
                      []
                      (Term.proj (Term.proj (Term.app `D.t [`j `k]) "." `c) "." `naturality_assoc))]
                    "]")
                   [])
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `snd_inv_app_t_app_assoc)] "]")
                   [])
                  []
                  (Tactic.tacticErw__
                   "erw"
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule
                      [(patternIgnore (token.«← » "←"))]
                      `PresheafedSpace.comp_c_app_assoc)]
                    "]")
                   [])
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     []
                     [(Term.typeSpec
                       ":"
                       («term_=_»
                        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                         (Term.app `D.t' [`j `k `i])
                         " ≫ "
                         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                          (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁_,_,_»
                           "π₁ "
                           `k
                           ", "
                           `i
                           ", "
                           `j)
                          " ≫ "
                          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                           (Term.app `D.t [`k `i])
                           " ≫ "
                           (Term.app
                            (Term.proj
                             (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                              "𝖣")
                             "."
                             `f)
                            [`i `k]))))
                        "="
                        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                         (Term.proj
                          (Term.app `pullback_symmetry [(Term.hole "_") (Term.hole "_")])
                          "."
                          `Hom)
                         " ≫ "
                         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                          (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁_,_,_»
                           "π₁ "
                           `j
                           ", "
                           `i
                           ", "
                           `k)
                          " ≫ "
                          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                           (Term.app `D.t [`j `i])
                           " ≫ "
                           (Term.app `D.f [`i `j]))))))]
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
                             (Term.proj
                              (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                               "𝖣")
                              "."
                              `t_fac_assoc))
                            ","
                            (Tactic.rwRule
                             []
                             (Term.proj
                              (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                               "𝖣")
                              "."
                              `t'_comp_eq_pullback_symmetry_assoc))
                            ","
                            (Tactic.rwRule [] `pullback_symmetry_hom_comp_snd_assoc)
                            ","
                            (Tactic.rwRule [] `pullback.condition)
                            ","
                            (Tactic.rwRule
                             []
                             (Term.proj
                              (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                               "𝖣")
                              "."
                              `t_fac_assoc))]
                           "]")
                          [])]))))))
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `congr_app [`this]))] "]")
                   [])
                  []
                  (Tactic.tacticErw__
                   "erw"
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule
                      []
                      (Term.app
                       `PresheafedSpace.comp_c_app_assoc
                       [(Term.proj
                         (Term.app `pullback_symmetry [(Term.hole "_") (Term.hole "_")])
                         "."
                         `Hom)]))]
                    "]")
                   [])
                  []
                  (Mathlib.Tactic.tacticSimp_rw__
                   "simp_rw"
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
                   [])
                  []
                  (Tactic.congr "congr" [(num "1")])
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `is_iso.eq_inv_comp)]
                    "]")
                   [])
                  []
                  (Tactic.tacticErw__
                   "erw"
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `is_open_immersion.inv_inv_app)] "]")
                   [])
                  []
                  (Mathlib.Tactic.tacticSimp_rw__
                   "simp_rw"
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
                   [])
                  []
                  (Tactic.tacticErw__
                   "erw"
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `nat_trans.naturality_assoc)
                     ","
                     (Tactic.rwRule
                      [(patternIgnore (token.«← » "←"))]
                      `PresheafedSpace.comp_c_app_assoc)
                     ","
                     (Tactic.rwRule
                      []
                      (Term.app
                       `congr_app
                       [(Term.app
                         `pullback_symmetry_hom_comp_snd
                         [(Term.hole "_") (Term.hole "_")])]))]
                    "]")
                   [])
                  []
                  (Mathlib.Tactic.tacticSimp_rw__
                   "simp_rw"
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
                   [])
                  []
                  (Tactic.tacticErw__
                   "erw"
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `is_open_immersion.inv_naturality_assoc)
                     ","
                     (Tactic.rwRule [] `is_open_immersion.inv_naturality_assoc)
                     ","
                     (Tactic.rwRule [] `is_open_immersion.inv_naturality_assoc)
                     ","
                     (Tactic.rwRule [] `is_open_immersion.app_inv_app_assoc)]
                    "]")
                   [])
                  []
                  (Std.Tactic.tacticRepeat'_
                   "repeat'"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.tacticErw__
                       "erw"
                       (Tactic.rwRuleSeq
                        "["
                        [(Tactic.rwRule
                          [(patternIgnore (token.«← » "←"))]
                          (Term.proj
                           (Term.proj
                            (Term.app `D.V [(Term.tuple "(" [`j "," [`k]] ")")])
                            "."
                            `Presheaf)
                           "."
                           `map_comp))]
                        "]")
                       [])])))
                  []
                  (Tactic.congr "congr" [])]))))))]
          (Term.optEllipsis [])
          []
          "}"))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
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
           (Term.app (Term.proj `D "." `ιInvAppπApp) [`U (Term.app `unop [`j])]))))
        []
        (Term.structInstField
         (Term.structInstLVal `naturality' [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`X `Y `f']
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.induction "induction" [`X] ["using" `Opposite.rec] [] [])
               []
               (Tactic.induction "induction" [`Y] ["using" `Opposite.rec] [] [])
               []
               (Tactic.tacticLet_
                "let"
                (Term.letDecl
                 (Term.letIdDecl
                  `f
                  []
                  [(Term.typeSpec ":" (Combinatorics.Quiver.Basic.«term_⟶_» `Y " ⟶ " `X))]
                  ":="
                  `f'.unop)))
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl [] [(Term.typeSpec ":" («term_=_» `f' "=" `f.op))] ":=" `rfl)))
               []
               (Tactic.clearValue "clear_value" [(group `f)])
               []
               (Tactic.subst "subst" [`this])
               []
               (Std.Tactic.rcases
                "rcases"
                [(Tactic.casesTarget [] `f)]
                ["with"
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.paren
                     "("
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed
                       [(Std.Tactic.RCases.rcasesPat.ignore "_")
                        "|"
                        (Std.Tactic.RCases.rcasesPat.tuple
                         "⟨"
                         [(Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j)])
                           [])
                          ","
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                           [])]
                         "⟩")
                        "|"
                        (Std.Tactic.RCases.rcasesPat.tuple
                         "⟨"
                         [(Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j)])
                           [])
                          ","
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                           [])]
                         "⟩")])
                      [])
                     ")")])
                  [])])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.tacticErw__
                  "erw"
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `category.id_comp)
                    ","
                    (Tactic.rwRule [] `CategoryTheory.Functor.map_id)]
                   "]")
                  [])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.comp_id)] "]")
                  [])])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.tacticErw__
                  "erw"
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.id_comp)] "]")
                  [])
                 []
                 (Tactic.congr "congr" [(num "1")])])
               []
               (Tactic.tacticErw__
                "erw"
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.id_comp)] "]")
                [])
               []
               (Tactic.change
                "change"
                («term_=_»
                 (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                  (Term.app `D.opens_image_preimage_map [`i `j `U])
                  " ≫ "
                  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                   (Term.app
                    (Term.proj (Term.proj (Term.app `D.f [`j `k]) "." `c) "." `app)
                    [(Term.hole "_")])
                   " ≫ "
                   (Term.app
                    (Term.proj
                     (Term.proj (Term.app `D.V [(Term.tuple "(" [`j "," [`k]] ")")]) "." `Presheaf)
                     "."
                     `map)
                    [(Term.app `eq_to_hom [(Term.hole "_")])])))
                 "="
                 (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                  (Term.app
                   `D.opens_image_preimage_map
                   [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                  " ≫ "
                  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                    (Term.app
                     (Term.proj (Term.proj (Term.app `D.f [`k `j]) "." `c) "." `app)
                     [(Term.hole "_")])
                    " ≫ "
                    (Term.app
                     (Term.proj (Term.proj (Term.app `D.t [`j `k]) "." `c) "." `app)
                     [(Term.hole "_")]))
                   " ≫ "
                   (Term.app
                    (Term.proj
                     (Term.proj (Term.app `D.V [(Term.tuple "(" [`j "," [`k]] ")")]) "." `Presheaf)
                     "."
                     `map)
                    [(Term.app `eq_to_hom [(Term.hole "_")])]))))
                [])
               []
               (Tactic.tacticErw__
                "erw"
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `opens_image_preimage_map_app_assoc)] "]")
                [])
               []
               (Mathlib.Tactic.tacticSimp_rw__
                "simp_rw"
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
                [])
               []
               (Tactic.tacticErw__
                "erw"
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `opens_image_preimage_map_app_assoc)
                  ","
                  (Tactic.rwRule
                   []
                   (Term.proj (Term.proj (Term.app `D.t [`j `k]) "." `c) "." `naturality_assoc))]
                 "]")
                [])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `snd_inv_app_t_app_assoc)] "]")
                [])
               []
               (Tactic.tacticErw__
                "erw"
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule
                   [(patternIgnore (token.«← » "←"))]
                   `PresheafedSpace.comp_c_app_assoc)]
                 "]")
                [])
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  []
                  [(Term.typeSpec
                    ":"
                    («term_=_»
                     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                      (Term.app `D.t' [`j `k `i])
                      " ≫ "
                      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                       (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁_,_,_»
                        "π₁ "
                        `k
                        ", "
                        `i
                        ", "
                        `j)
                       " ≫ "
                       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                        (Term.app `D.t [`k `i])
                        " ≫ "
                        (Term.app
                         (Term.proj
                          (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                           "𝖣")
                          "."
                          `f)
                         [`i `k]))))
                     "="
                     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                      (Term.proj
                       (Term.app `pullback_symmetry [(Term.hole "_") (Term.hole "_")])
                       "."
                       `Hom)
                      " ≫ "
                      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                       (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁_,_,_»
                        "π₁ "
                        `j
                        ", "
                        `i
                        ", "
                        `k)
                       " ≫ "
                       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                        (Term.app `D.t [`j `i])
                        " ≫ "
                        (Term.app `D.f [`i `j]))))))]
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
                          (Term.proj
                           (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                            "𝖣")
                           "."
                           `t_fac_assoc))
                         ","
                         (Tactic.rwRule
                          []
                          (Term.proj
                           (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                            "𝖣")
                           "."
                           `t'_comp_eq_pullback_symmetry_assoc))
                         ","
                         (Tactic.rwRule [] `pullback_symmetry_hom_comp_snd_assoc)
                         ","
                         (Tactic.rwRule [] `pullback.condition)
                         ","
                         (Tactic.rwRule
                          []
                          (Term.proj
                           (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                            "𝖣")
                           "."
                           `t_fac_assoc))]
                        "]")
                       [])]))))))
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `congr_app [`this]))] "]")
                [])
               []
               (Tactic.tacticErw__
                "erw"
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule
                   []
                   (Term.app
                    `PresheafedSpace.comp_c_app_assoc
                    [(Term.proj
                      (Term.app `pullback_symmetry [(Term.hole "_") (Term.hole "_")])
                      "."
                      `Hom)]))]
                 "]")
                [])
               []
               (Mathlib.Tactic.tacticSimp_rw__
                "simp_rw"
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
                [])
               []
               (Tactic.congr "congr" [(num "1")])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `is_iso.eq_inv_comp)]
                 "]")
                [])
               []
               (Tactic.tacticErw__
                "erw"
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `is_open_immersion.inv_inv_app)] "]")
                [])
               []
               (Mathlib.Tactic.tacticSimp_rw__
                "simp_rw"
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
                [])
               []
               (Tactic.tacticErw__
                "erw"
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `nat_trans.naturality_assoc)
                  ","
                  (Tactic.rwRule
                   [(patternIgnore (token.«← » "←"))]
                   `PresheafedSpace.comp_c_app_assoc)
                  ","
                  (Tactic.rwRule
                   []
                   (Term.app
                    `congr_app
                    [(Term.app
                      `pullback_symmetry_hom_comp_snd
                      [(Term.hole "_") (Term.hole "_")])]))]
                 "]")
                [])
               []
               (Mathlib.Tactic.tacticSimp_rw__
                "simp_rw"
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
                [])
               []
               (Tactic.tacticErw__
                "erw"
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `is_open_immersion.inv_naturality_assoc)
                  ","
                  (Tactic.rwRule [] `is_open_immersion.inv_naturality_assoc)
                  ","
                  (Tactic.rwRule [] `is_open_immersion.inv_naturality_assoc)
                  ","
                  (Tactic.rwRule [] `is_open_immersion.app_inv_app_assoc)]
                 "]")
                [])
               []
               (Std.Tactic.tacticRepeat'_
                "repeat'"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.tacticErw__
                    "erw"
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule
                       [(patternIgnore (token.«← » "←"))]
                       (Term.proj
                        (Term.proj
                         (Term.app `D.V [(Term.tuple "(" [`j "," [`k]] ")")])
                         "."
                         `Presheaf)
                        "."
                        `map_comp))]
                     "]")
                    [])])))
               []
               (Tactic.congr "congr" [])]))))))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`X `Y `f']
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.induction "induction" [`X] ["using" `Opposite.rec] [] [])
            []
            (Tactic.induction "induction" [`Y] ["using" `Opposite.rec] [] [])
            []
            (Tactic.tacticLet_
             "let"
             (Term.letDecl
              (Term.letIdDecl
               `f
               []
               [(Term.typeSpec ":" (Combinatorics.Quiver.Basic.«term_⟶_» `Y " ⟶ " `X))]
               ":="
               `f'.unop)))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl [] [(Term.typeSpec ":" («term_=_» `f' "=" `f.op))] ":=" `rfl)))
            []
            (Tactic.clearValue "clear_value" [(group `f)])
            []
            (Tactic.subst "subst" [`this])
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] `f)]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.paren
                  "("
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.ignore "_")
                     "|"
                     (Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                        [])]
                      "⟩")
                     "|"
                     (Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                        [])]
                      "⟩")])
                   [])
                  ")")])
               [])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.tacticErw__
               "erw"
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `category.id_comp)
                 ","
                 (Tactic.rwRule [] `CategoryTheory.Functor.map_id)]
                "]")
               [])
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.comp_id)] "]")
               [])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.tacticErw__
               "erw"
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.id_comp)] "]")
               [])
              []
              (Tactic.congr "congr" [(num "1")])])
            []
            (Tactic.tacticErw__
             "erw"
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.id_comp)] "]")
             [])
            []
            (Tactic.change
             "change"
             («term_=_»
              (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
               (Term.app `D.opens_image_preimage_map [`i `j `U])
               " ≫ "
               (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                (Term.app
                 (Term.proj (Term.proj (Term.app `D.f [`j `k]) "." `c) "." `app)
                 [(Term.hole "_")])
                " ≫ "
                (Term.app
                 (Term.proj
                  (Term.proj (Term.app `D.V [(Term.tuple "(" [`j "," [`k]] ")")]) "." `Presheaf)
                  "."
                  `map)
                 [(Term.app `eq_to_hom [(Term.hole "_")])])))
              "="
              (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
               (Term.app
                `D.opens_image_preimage_map
                [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
               " ≫ "
               (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                 (Term.app
                  (Term.proj (Term.proj (Term.app `D.f [`k `j]) "." `c) "." `app)
                  [(Term.hole "_")])
                 " ≫ "
                 (Term.app
                  (Term.proj (Term.proj (Term.app `D.t [`j `k]) "." `c) "." `app)
                  [(Term.hole "_")]))
                " ≫ "
                (Term.app
                 (Term.proj
                  (Term.proj (Term.app `D.V [(Term.tuple "(" [`j "," [`k]] ")")]) "." `Presheaf)
                  "."
                  `map)
                 [(Term.app `eq_to_hom [(Term.hole "_")])]))))
             [])
            []
            (Tactic.tacticErw__
             "erw"
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `opens_image_preimage_map_app_assoc)] "]")
             [])
            []
            (Mathlib.Tactic.tacticSimp_rw__
             "simp_rw"
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
             [])
            []
            (Tactic.tacticErw__
             "erw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `opens_image_preimage_map_app_assoc)
               ","
               (Tactic.rwRule
                []
                (Term.proj (Term.proj (Term.app `D.t [`j `k]) "." `c) "." `naturality_assoc))]
              "]")
             [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `snd_inv_app_t_app_assoc)] "]")
             [])
            []
            (Tactic.tacticErw__
             "erw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `PresheafedSpace.comp_c_app_assoc)]
              "]")
             [])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec
                 ":"
                 («term_=_»
                  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                   (Term.app `D.t' [`j `k `i])
                   " ≫ "
                   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                    (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁_,_,_»
                     "π₁ "
                     `k
                     ", "
                     `i
                     ", "
                     `j)
                    " ≫ "
                    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                     (Term.app `D.t [`k `i])
                     " ≫ "
                     (Term.app
                      (Term.proj
                       (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                        "𝖣")
                       "."
                       `f)
                      [`i `k]))))
                  "="
                  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                   (Term.proj
                    (Term.app `pullback_symmetry [(Term.hole "_") (Term.hole "_")])
                    "."
                    `Hom)
                   " ≫ "
                   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                    (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁_,_,_»
                     "π₁ "
                     `j
                     ", "
                     `i
                     ", "
                     `k)
                    " ≫ "
                    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                     (Term.app `D.t [`j `i])
                     " ≫ "
                     (Term.app `D.f [`i `j]))))))]
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
                       (Term.proj
                        (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                         "𝖣")
                        "."
                        `t_fac_assoc))
                      ","
                      (Tactic.rwRule
                       []
                       (Term.proj
                        (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                         "𝖣")
                        "."
                        `t'_comp_eq_pullback_symmetry_assoc))
                      ","
                      (Tactic.rwRule [] `pullback_symmetry_hom_comp_snd_assoc)
                      ","
                      (Tactic.rwRule [] `pullback.condition)
                      ","
                      (Tactic.rwRule
                       []
                       (Term.proj
                        (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                         "𝖣")
                        "."
                        `t_fac_assoc))]
                     "]")
                    [])]))))))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `congr_app [`this]))] "]")
             [])
            []
            (Tactic.tacticErw__
             "erw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                []
                (Term.app
                 `PresheafedSpace.comp_c_app_assoc
                 [(Term.proj
                   (Term.app `pullback_symmetry [(Term.hole "_") (Term.hole "_")])
                   "."
                   `Hom)]))]
              "]")
             [])
            []
            (Mathlib.Tactic.tacticSimp_rw__
             "simp_rw"
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
             [])
            []
            (Tactic.congr "congr" [(num "1")])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `is_iso.eq_inv_comp)]
              "]")
             [])
            []
            (Tactic.tacticErw__
             "erw"
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `is_open_immersion.inv_inv_app)] "]")
             [])
            []
            (Mathlib.Tactic.tacticSimp_rw__
             "simp_rw"
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
             [])
            []
            (Tactic.tacticErw__
             "erw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `nat_trans.naturality_assoc)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `PresheafedSpace.comp_c_app_assoc)
               ","
               (Tactic.rwRule
                []
                (Term.app
                 `congr_app
                 [(Term.app `pullback_symmetry_hom_comp_snd [(Term.hole "_") (Term.hole "_")])]))]
              "]")
             [])
            []
            (Mathlib.Tactic.tacticSimp_rw__
             "simp_rw"
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
             [])
            []
            (Tactic.tacticErw__
             "erw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `is_open_immersion.inv_naturality_assoc)
               ","
               (Tactic.rwRule [] `is_open_immersion.inv_naturality_assoc)
               ","
               (Tactic.rwRule [] `is_open_immersion.inv_naturality_assoc)
               ","
               (Tactic.rwRule [] `is_open_immersion.app_inv_app_assoc)]
              "]")
             [])
            []
            (Std.Tactic.tacticRepeat'_
             "repeat'"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.tacticErw__
                 "erw"
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule
                    [(patternIgnore (token.«← » "←"))]
                    (Term.proj
                     (Term.proj (Term.app `D.V [(Term.tuple "(" [`j "," [`k]] ")")]) "." `Presheaf)
                     "."
                     `map_comp))]
                  "]")
                 [])])))
            []
            (Tactic.congr "congr" [])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.induction "induction" [`X] ["using" `Opposite.rec] [] [])
          []
          (Tactic.induction "induction" [`Y] ["using" `Opposite.rec] [] [])
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `f
             []
             [(Term.typeSpec ":" (Combinatorics.Quiver.Basic.«term_⟶_» `Y " ⟶ " `X))]
             ":="
             `f'.unop)))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl [] [(Term.typeSpec ":" («term_=_» `f' "=" `f.op))] ":=" `rfl)))
          []
          (Tactic.clearValue "clear_value" [(group `f)])
          []
          (Tactic.subst "subst" [`this])
          []
          (Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] `f)]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.paren
                "("
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.ignore "_")
                   "|"
                   (Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                      [])]
                    "⟩")
                   "|"
                   (Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                      [])]
                    "⟩")])
                 [])
                ")")])
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.tacticErw__
             "erw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `category.id_comp)
               ","
               (Tactic.rwRule [] `CategoryTheory.Functor.map_id)]
              "]")
             [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.comp_id)] "]")
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.tacticErw__
             "erw"
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.id_comp)] "]")
             [])
            []
            (Tactic.congr "congr" [(num "1")])])
          []
          (Tactic.tacticErw__
           "erw"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.id_comp)] "]")
           [])
          []
          (Tactic.change
           "change"
           («term_=_»
            (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
             (Term.app `D.opens_image_preimage_map [`i `j `U])
             " ≫ "
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
              (Term.app
               (Term.proj (Term.proj (Term.app `D.f [`j `k]) "." `c) "." `app)
               [(Term.hole "_")])
              " ≫ "
              (Term.app
               (Term.proj
                (Term.proj (Term.app `D.V [(Term.tuple "(" [`j "," [`k]] ")")]) "." `Presheaf)
                "."
                `map)
               [(Term.app `eq_to_hom [(Term.hole "_")])])))
            "="
            (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
             (Term.app
              `D.opens_image_preimage_map
              [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
             " ≫ "
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
              (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
               (Term.app
                (Term.proj (Term.proj (Term.app `D.f [`k `j]) "." `c) "." `app)
                [(Term.hole "_")])
               " ≫ "
               (Term.app
                (Term.proj (Term.proj (Term.app `D.t [`j `k]) "." `c) "." `app)
                [(Term.hole "_")]))
              " ≫ "
              (Term.app
               (Term.proj
                (Term.proj (Term.app `D.V [(Term.tuple "(" [`j "," [`k]] ")")]) "." `Presheaf)
                "."
                `map)
               [(Term.app `eq_to_hom [(Term.hole "_")])]))))
           [])
          []
          (Tactic.tacticErw__
           "erw"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `opens_image_preimage_map_app_assoc)] "]")
           [])
          []
          (Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
           [])
          []
          (Tactic.tacticErw__
           "erw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `opens_image_preimage_map_app_assoc)
             ","
             (Tactic.rwRule
              []
              (Term.proj (Term.proj (Term.app `D.t [`j `k]) "." `c) "." `naturality_assoc))]
            "]")
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `snd_inv_app_t_app_assoc)] "]")
           [])
          []
          (Tactic.tacticErw__
           "erw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `PresheafedSpace.comp_c_app_assoc)]
            "]")
           [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               («term_=_»
                (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                 (Term.app `D.t' [`j `k `i])
                 " ≫ "
                 (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                  (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁_,_,_»
                   "π₁ "
                   `k
                   ", "
                   `i
                   ", "
                   `j)
                  " ≫ "
                  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                   (Term.app `D.t [`k `i])
                   " ≫ "
                   (Term.app
                    (Term.proj
                     (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                      "𝖣")
                     "."
                     `f)
                    [`i `k]))))
                "="
                (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                 (Term.proj
                  (Term.app `pullback_symmetry [(Term.hole "_") (Term.hole "_")])
                  "."
                  `Hom)
                 " ≫ "
                 (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                  (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁_,_,_»
                   "π₁ "
                   `j
                   ", "
                   `i
                   ", "
                   `k)
                  " ≫ "
                  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                   (Term.app `D.t [`j `i])
                   " ≫ "
                   (Term.app `D.f [`i `j]))))))]
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
                     (Term.proj
                      (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                       "𝖣")
                      "."
                      `t_fac_assoc))
                    ","
                    (Tactic.rwRule
                     []
                     (Term.proj
                      (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                       "𝖣")
                      "."
                      `t'_comp_eq_pullback_symmetry_assoc))
                    ","
                    (Tactic.rwRule [] `pullback_symmetry_hom_comp_snd_assoc)
                    ","
                    (Tactic.rwRule [] `pullback.condition)
                    ","
                    (Tactic.rwRule
                     []
                     (Term.proj
                      (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                       "𝖣")
                      "."
                      `t_fac_assoc))]
                   "]")
                  [])]))))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `congr_app [`this]))] "]")
           [])
          []
          (Tactic.tacticErw__
           "erw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.app
               `PresheafedSpace.comp_c_app_assoc
               [(Term.proj
                 (Term.app `pullback_symmetry [(Term.hole "_") (Term.hole "_")])
                 "."
                 `Hom)]))]
            "]")
           [])
          []
          (Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
           [])
          []
          (Tactic.congr "congr" [(num "1")])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `is_iso.eq_inv_comp)]
            "]")
           [])
          []
          (Tactic.tacticErw__
           "erw"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `is_open_immersion.inv_inv_app)] "]")
           [])
          []
          (Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
           [])
          []
          (Tactic.tacticErw__
           "erw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `nat_trans.naturality_assoc)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `PresheafedSpace.comp_c_app_assoc)
             ","
             (Tactic.rwRule
              []
              (Term.app
               `congr_app
               [(Term.app `pullback_symmetry_hom_comp_snd [(Term.hole "_") (Term.hole "_")])]))]
            "]")
           [])
          []
          (Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
           [])
          []
          (Tactic.tacticErw__
           "erw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `is_open_immersion.inv_naturality_assoc)
             ","
             (Tactic.rwRule [] `is_open_immersion.inv_naturality_assoc)
             ","
             (Tactic.rwRule [] `is_open_immersion.inv_naturality_assoc)
             ","
             (Tactic.rwRule [] `is_open_immersion.app_inv_app_assoc)]
            "]")
           [])
          []
          (Std.Tactic.tacticRepeat'_
           "repeat'"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.tacticErw__
               "erw"
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule
                  [(patternIgnore (token.«← » "←"))]
                  (Term.proj
                   (Term.proj (Term.app `D.V [(Term.tuple "(" [`j "," [`k]] ")")]) "." `Presheaf)
                   "."
                   `map_comp))]
                "]")
               [])])))
          []
          (Tactic.congr "congr" [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.congr "congr" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticRepeat'_
       "repeat'"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticErw__
           "erw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.proj
               (Term.proj (Term.app `D.V [(Term.tuple "(" [`j "," [`k]] ")")]) "." `Presheaf)
               "."
               `map_comp))]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticErw__
       "erw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.proj
           (Term.proj (Term.app `D.V [(Term.tuple "(" [`j "," [`k]] ")")]) "." `Presheaf)
           "."
           `map_comp))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.proj (Term.app `D.V [(Term.tuple "(" [`j "," [`k]] ")")]) "." `Presheaf)
       "."
       `map_comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app `D.V [(Term.tuple "(" [`j "," [`k]] ")")]) "." `Presheaf)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `D.V [(Term.tuple "(" [`j "," [`k]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`j "," [`k]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `D.V
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `D.V [(Term.tuple "(" [`j "," [`k]] ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticErw__
       "erw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `is_open_immersion.inv_naturality_assoc)
         ","
         (Tactic.rwRule [] `is_open_immersion.inv_naturality_assoc)
         ","
         (Tactic.rwRule [] `is_open_immersion.inv_naturality_assoc)
         ","
         (Tactic.rwRule [] `is_open_immersion.app_inv_app_assoc)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `is_open_immersion.app_inv_app_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `is_open_immersion.inv_naturality_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `is_open_immersion.inv_naturality_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `is_open_immersion.inv_naturality_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `category.assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticErw__
       "erw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `nat_trans.naturality_assoc)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `PresheafedSpace.comp_c_app_assoc)
         ","
         (Tactic.rwRule
          []
          (Term.app
           `congr_app
           [(Term.app `pullback_symmetry_hom_comp_snd [(Term.hole "_") (Term.hole "_")])]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `congr_app
       [(Term.app `pullback_symmetry_hom_comp_snd [(Term.hole "_") (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pullback_symmetry_hom_comp_snd [(Term.hole "_") (Term.hole "_")])
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
      `pullback_symmetry_hom_comp_snd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `pullback_symmetry_hom_comp_snd [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `congr_app
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `PresheafedSpace.comp_c_app_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nat_trans.naturality_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `category.assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticErw__
       "erw"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `is_open_immersion.inv_inv_app)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `is_open_immersion.inv_inv_app
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `is_iso.eq_inv_comp)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `is_iso.eq_inv_comp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.congr "congr" [(num "1")])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `category.assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticErw__
       "erw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          []
          (Term.app
           `PresheafedSpace.comp_c_app_assoc
           [(Term.proj (Term.app `pullback_symmetry [(Term.hole "_") (Term.hole "_")]) "." `Hom)]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `PresheafedSpace.comp_c_app_assoc
       [(Term.proj (Term.app `pullback_symmetry [(Term.hole "_") (Term.hole "_")]) "." `Hom)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `pullback_symmetry [(Term.hole "_") (Term.hole "_")]) "." `Hom)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `pullback_symmetry [(Term.hole "_") (Term.hole "_")])
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
      `pullback_symmetry
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `pullback_symmetry [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `PresheafedSpace.comp_c_app_assoc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `congr_app [`this]))] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `congr_app [`this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `congr_app
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_=_»
            (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
             (Term.app `D.t' [`j `k `i])
             " ≫ "
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
              (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁_,_,_»
               "π₁ "
               `k
               ", "
               `i
               ", "
               `j)
              " ≫ "
              (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
               (Term.app `D.t [`k `i])
               " ≫ "
               (Term.app
                (Term.proj
                 (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                  "𝖣")
                 "."
                 `f)
                [`i `k]))))
            "="
            (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
             (Term.proj (Term.app `pullback_symmetry [(Term.hole "_") (Term.hole "_")]) "." `Hom)
             " ≫ "
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
              (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«termπ₁_,_,_»
               "π₁ "
               `j
               ", "
               `i
               ", "
               `k)
              " ≫ "
              (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
               (Term.app `D.t [`j `i])
               " ≫ "
               (Term.app `D.f [`i `j]))))))]
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
                 (Term.proj
                  (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                   "𝖣")
                  "."
                  `t_fac_assoc))
                ","
                (Tactic.rwRule
                 []
                 (Term.proj
                  (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                   "𝖣")
                  "."
                  `t'_comp_eq_pullback_symmetry_assoc))
                ","
                (Tactic.rwRule [] `pullback_symmetry_hom_comp_snd_assoc)
                ","
                (Tactic.rwRule [] `pullback.condition)
                ","
                (Tactic.rwRule
                 []
                 (Term.proj
                  (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                   "𝖣")
                  "."
                  `t_fac_assoc))]
               "]")
              [])]))))))
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
              (Term.proj
               (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                "𝖣")
               "."
               `t_fac_assoc))
             ","
             (Tactic.rwRule
              []
              (Term.proj
               (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                "𝖣")
               "."
               `t'_comp_eq_pullback_symmetry_assoc))
             ","
             (Tactic.rwRule [] `pullback_symmetry_hom_comp_snd_assoc)
             ","
             (Tactic.rwRule [] `pullback.condition)
             ","
             (Tactic.rwRule
              []
              (Term.proj
               (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                "𝖣")
               "."
               `t_fac_assoc))]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.proj
           (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
            "𝖣")
           "."
           `t_fac_assoc))
         ","
         (Tactic.rwRule
          []
          (Term.proj
           (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
            "𝖣")
           "."
           `t'_comp_eq_pullback_symmetry_assoc))
         ","
         (Tactic.rwRule [] `pullback_symmetry_hom_comp_snd_assoc)
         ","
         (Tactic.rwRule [] `pullback.condition)
         ","
         (Tactic.rwRule
          []
          (Term.proj
           (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
            "𝖣")
           "."
           `t_fac_assoc))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
        "𝖣")
       "."
       `t_fac_assoc)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
       "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»', expected 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.term𝖣._@.AlgebraicGeometry.PresheafedSpace.Gluing._hyg.31'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
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
    (Implementation) The natural map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_X, 𝖣.ι i '' U)`.
    This forms the inverse of `(𝖣.ι i).c.app (op U)`. -/
  def
    ιInvApp
    { i : D . J } ( U : Opens D . U i . carrier )
      : D . U i . Presheaf . obj op U ⟶ limit D . diagramOverOpen U
    :=
      limit.lift
        D . diagramOverOpen U
          {
            x := D . U i . Presheaf . obj op U
              π
                :=
                {
                  app := fun j => D . ιInvAppπApp U unop j
                    naturality'
                      :=
                      fun
                        X Y f'
                          =>
                          by
                            induction X using Opposite.rec
                              induction Y using Opposite.rec
                              let f : Y ⟶ X := f'.unop
                              have : f' = f.op := rfl
                              clear_value f
                              subst this
                              rcases f with ( _ | ⟨ j , k ⟩ | ⟨ j , k ⟩ )
                              ·
                                erw [ category.id_comp , CategoryTheory.Functor.map_id ]
                                  rw [ category.comp_id ]
                              · erw [ category.id_comp ] congr 1
                              erw [ category.id_comp ]
                              change
                                D.opens_image_preimage_map i j U
                                    ≫
                                    D.f j k . c . app _ ≫ D.V ( j , k ) . Presheaf . map eq_to_hom _
                                  =
                                  D.opens_image_preimage_map _ _ _
                                    ≫
                                    D.f k j . c . app _ ≫ D.t j k . c . app _
                                      ≫
                                      D.V ( j , k ) . Presheaf . map eq_to_hom _
                              erw [ opens_image_preimage_map_app_assoc ]
                              simp_rw [ category.assoc ]
                              erw
                                [
                                  opens_image_preimage_map_app_assoc
                                    ,
                                    D.t j k . c . naturality_assoc
                                  ]
                              rw [ snd_inv_app_t_app_assoc ]
                              erw [ ← PresheafedSpace.comp_c_app_assoc ]
                              have
                                :
                                    D.t' j k i ≫ π₁ k , i , j ≫ D.t k i ≫ 𝖣 . f i k
                                      =
                                      pullback_symmetry _ _ . Hom ≫ π₁ j , i , k ≫ D.t j i ≫ D.f i j
                                  :=
                                  by
                                    rw
                                      [
                                        ← 𝖣 . t_fac_assoc
                                          ,
                                          𝖣 . t'_comp_eq_pullback_symmetry_assoc
                                          ,
                                          pullback_symmetry_hom_comp_snd_assoc
                                          ,
                                          pullback.condition
                                          ,
                                          𝖣 . t_fac_assoc
                                        ]
                              rw [ congr_app this ]
                              erw [ PresheafedSpace.comp_c_app_assoc pullback_symmetry _ _ . Hom ]
                              simp_rw [ category.assoc ]
                              congr 1
                              rw [ ← is_iso.eq_inv_comp ]
                              erw [ is_open_immersion.inv_inv_app ]
                              simp_rw [ category.assoc ]
                              erw
                                [
                                  nat_trans.naturality_assoc
                                    ,
                                    ← PresheafedSpace.comp_c_app_assoc
                                    ,
                                    congr_app pullback_symmetry_hom_comp_snd _ _
                                  ]
                              simp_rw [ category.assoc ]
                              erw
                                [
                                  is_open_immersion.inv_naturality_assoc
                                    ,
                                    is_open_immersion.inv_naturality_assoc
                                    ,
                                    is_open_immersion.inv_naturality_assoc
                                    ,
                                    is_open_immersion.app_inv_app_assoc
                                  ]
                              repeat' erw [ ← D.V ( j , k ) . Presheaf . map_comp ]
                              congr
                  }
            }
#align
  algebraic_geometry.PresheafedSpace.glue_data.ι_inv_app AlgebraicGeometry.PresheafedSpaceCat.GlueData.ιInvApp

/-- `ι_inv_app` is the left inverse of `D.ι i` on `U`. -/
theorem ι_inv_app_π {i : D.J} (U : Opens (D.U i).carrier) :
    ∃ eq, D.ιInvApp U ≫ D.diagramOverOpenπ U i = (D.U i).Presheaf.map (eqToHom Eq) :=
  by
  constructor
  delta ι_inv_app
  rw [limit.lift_π]
  change D.opens_image_preimage_map i i U = _
  dsimp [opens_image_preimage_map]
  rw [congr_app (D.t_id _), id_c_app, ← functor.map_comp]
  erw [is_open_immersion.inv_naturality_assoc, is_open_immersion.app_inv_app'_assoc]
  simp only [eq_to_hom_op, eq_to_hom_trans, eq_to_hom_map (functor.op _), ← functor.map_comp]
  rw [set.range_iff_surjective.mpr _]
  · simp
  · rw [← TopCat.epi_iff_surjective]
    infer_instance
#align
  algebraic_geometry.PresheafedSpace.glue_data.ι_inv_app_π AlgebraicGeometry.PresheafedSpaceCat.GlueData.ι_inv_app_π

/-- The `eq_to_hom` given by `ι_inv_app_π`. -/
abbrev ιInvAppπEqMap {i : D.J} (U : Opens (D.U i).carrier) :=
  (D.U i).Presheaf.map (eqToIso (D.ι_inv_app_π U).some).inv
#align
  algebraic_geometry.PresheafedSpace.glue_data.ι_inv_app_π_eq_map AlgebraicGeometry.PresheafedSpaceCat.GlueData.ιInvAppπEqMap

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "`ι_inv_app` is the right inverse of `D.ι i` on `U`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `π_ι_inv_app_π [])
      (Command.declSig
       [(Term.explicitBinder "(" [`i `j] [":" (Term.proj `D "." `J)] [] ")")
        (Term.explicitBinder
         "("
         [`U]
         [":" (Term.app `Opens [(Term.proj (Term.app (Term.proj `D "." `U) [`i]) "." `carrier)])]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app (Term.proj `D "." `diagramOverOpenπ) [`U `i])
          " ≫ "
          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
           (Term.app (Term.proj `D "." `ιInvAppπEqMap) [`U])
           " ≫ "
           (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
            (Term.app (Term.proj `D "." `ιInvApp) [`U])
            " ≫ "
            (Term.app (Term.proj `D "." `diagramOverOpenπ) [`U `j]))))
         "="
         (Term.app (Term.proj `D "." `diagramOverOpenπ) [`U `j]))))
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
               (Term.app
                `cancel_mono
                [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                  (Term.app
                   (Term.proj
                    (Term.app
                     `componentwise_diagram
                     [(Term.proj
                       (Term.proj
                        (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                         "𝖣")
                        "."
                        `diagram)
                       "."
                       `multispan)
                      (Term.hole "_")])
                    "."
                    `map)
                   [(Term.app
                     `Quiver.Hom.op
                     [(Term.app `walking_multispan.hom.snd [(Term.tuple "(" [`i "," [`j]] ")")])])])
                  " ≫ "
                  (Term.app
                   (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
                   [(Term.hole "_")]))]))]
             "]")
            [])
           []
           (Mathlib.Tactic.tacticSimp_rw__
            "simp_rw"
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
            [])
           []
           (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `limit.w_assoc)] "]") [])
           []
           (Tactic.tacticErw__
            "erw"
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `limit.lift_π_assoc)] "]")
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `category.comp_id) "," (Tactic.rwRule [] `category.comp_id)]
             "]")
            [])
           []
           (Tactic.change
            "change"
            («term_=_»
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
              (Term.hole "_")
              " ≫ "
              (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
               (Term.hole "_")
               " ≫ "
               (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                 (Term.hole "_")
                 " ≫ "
                 (Term.hole "_"))
                " ≫ "
                (Term.hole "_"))))
             "="
             (Term.hole "_"))
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] (Term.app `congr_app [(Term.app `D.t_id [(Term.hole "_")])]))
              ","
              (Tactic.rwRule [] `id_c_app)]
             "]")
            [])
           []
           (Mathlib.Tactic.tacticSimp_rw__
            "simp_rw"
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `functor.map_comp_assoc)
              ","
              (Tactic.rwRule [] `is_open_immersion.inv_naturality_assoc)]
             "]")
            [])
           []
           (Tactic.tacticErw__
            "erw"
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `is_open_immersion.app_inv_app_assoc)] "]")
            [])
           []
           (Std.Tactic.tacticIterate____
            "iterate"
            [(num "3")]
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `functor.map_comp_assoc)]
                 "]")
                [])])))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `nat_trans.naturality_assoc)] "]")
            [])
           []
           (Tactic.tacticErw__
            "erw"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.proj
                (Term.proj (Term.app `D.V [(Term.tuple "(" [`i "," [`j]] ")")]) "." `Presheaf)
                "."
                `map_comp))]
             "]")
            [])
           []
           (convert
            "convert"
            []
            (Term.app
             `limit.w
             [(Term.app
               `componentwise_diagram
               [(Term.proj
                 (Term.proj
                  (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                   "𝖣")
                  "."
                  `diagram)
                 "."
                 `multispan)
                (Term.hole "_")])
              (Term.app
               `Quiver.Hom.op
               [(Term.app `walking_multispan.hom.fst [(Term.tuple "(" [`i "," [`j]] ")")])])])
            [])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.comp_id)] "]")
              [])
             []
             (Mathlib.Tactic.applyWith
              "apply"
              "("
              "config"
              ":="
              (Term.structInst
               "{"
               []
               [(Term.structInstField (Term.structInstLVal `instances []) ":=" `false)]
               (Term.optEllipsis [])
               []
               "}")
              ")"
              `mono_comp)
             []
             (Tactic.change
              "change"
              (Term.app
               `mono
               [(Term.app
                 (Term.proj
                  (Term.proj
                   (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                    (Term.hole "_")
                    " ≫ "
                    (Term.app `D.f [`j `i]))
                   "."
                   `c)
                  "."
                  `app)
                 [(Term.hole "_")])])
              [])
             []
             (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `comp_c_app)] "]") [])
             []
             (Mathlib.Tactic.applyWith
              "apply"
              "("
              "config"
              ":="
              (Term.structInst
               "{"
               []
               [(Term.structInstField (Term.structInstLVal `instances []) ":=" `false)]
               (Term.optEllipsis [])
               []
               "}")
              ")"
              `mono_comp)
             []
             (Tactic.tacticErw__
              "erw"
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] (Term.app `D.ι_image_preimage_eq [`i `j `U]))]
               "]")
              [])
             []
             (Tactic.allGoals
              "all_goals"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented [(Tactic.tacticInfer_instance "infer_instance")])))])])))
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
              (Term.app
               `cancel_mono
               [(CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                 (Term.app
                  (Term.proj
                   (Term.app
                    `componentwise_diagram
                    [(Term.proj
                      (Term.proj
                       (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                        "𝖣")
                       "."
                       `diagram)
                      "."
                      `multispan)
                     (Term.hole "_")])
                   "."
                   `map)
                  [(Term.app
                    `Quiver.Hom.op
                    [(Term.app `walking_multispan.hom.snd [(Term.tuple "(" [`i "," [`j]] ")")])])])
                 " ≫ "
                 (Term.app
                  (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙")
                  [(Term.hole "_")]))]))]
            "]")
           [])
          []
          (Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
           [])
          []
          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `limit.w_assoc)] "]") [])
          []
          (Tactic.tacticErw__
           "erw"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `limit.lift_π_assoc)] "]")
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `category.comp_id) "," (Tactic.rwRule [] `category.comp_id)]
            "]")
           [])
          []
          (Tactic.change
           "change"
           («term_=_»
            (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
             (Term.hole "_")
             " ≫ "
             (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
              (Term.hole "_")
              " ≫ "
              (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
               (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                (Term.hole "_")
                " ≫ "
                (Term.hole "_"))
               " ≫ "
               (Term.hole "_"))))
            "="
            (Term.hole "_"))
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] (Term.app `congr_app [(Term.app `D.t_id [(Term.hole "_")])]))
             ","
             (Tactic.rwRule [] `id_c_app)]
            "]")
           [])
          []
          (Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `functor.map_comp_assoc)
             ","
             (Tactic.rwRule [] `is_open_immersion.inv_naturality_assoc)]
            "]")
           [])
          []
          (Tactic.tacticErw__
           "erw"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `is_open_immersion.app_inv_app_assoc)] "]")
           [])
          []
          (Std.Tactic.tacticIterate____
           "iterate"
           [(num "3")]
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `functor.map_comp_assoc)]
                "]")
               [])])))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `nat_trans.naturality_assoc)] "]")
           [])
          []
          (Tactic.tacticErw__
           "erw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.proj
               (Term.proj (Term.app `D.V [(Term.tuple "(" [`i "," [`j]] ")")]) "." `Presheaf)
               "."
               `map_comp))]
            "]")
           [])
          []
          (convert
           "convert"
           []
           (Term.app
            `limit.w
            [(Term.app
              `componentwise_diagram
              [(Term.proj
                (Term.proj
                 (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                  "𝖣")
                 "."
                 `diagram)
                "."
                `multispan)
               (Term.hole "_")])
             (Term.app
              `Quiver.Hom.op
              [(Term.app `walking_multispan.hom.fst [(Term.tuple "(" [`i "," [`j]] ")")])])])
           [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.comp_id)] "]")
             [])
            []
            (Mathlib.Tactic.applyWith
             "apply"
             "("
             "config"
             ":="
             (Term.structInst
              "{"
              []
              [(Term.structInstField (Term.structInstLVal `instances []) ":=" `false)]
              (Term.optEllipsis [])
              []
              "}")
             ")"
             `mono_comp)
            []
            (Tactic.change
             "change"
             (Term.app
              `mono
              [(Term.app
                (Term.proj
                 (Term.proj
                  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                   (Term.hole "_")
                   " ≫ "
                   (Term.app `D.f [`j `i]))
                  "."
                  `c)
                 "."
                 `app)
                [(Term.hole "_")])])
             [])
            []
            (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `comp_c_app)] "]") [])
            []
            (Mathlib.Tactic.applyWith
             "apply"
             "("
             "config"
             ":="
             (Term.structInst
              "{"
              []
              [(Term.structInstField (Term.structInstLVal `instances []) ":=" `false)]
              (Term.optEllipsis [])
              []
              "}")
             ")"
             `mono_comp)
            []
            (Tactic.tacticErw__
             "erw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] (Term.app `D.ι_image_preimage_eq [`i `j `U]))]
              "]")
             [])
            []
            (Tactic.allGoals
             "all_goals"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented [(Tactic.tacticInfer_instance "infer_instance")])))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.comp_id)] "]") [])
        []
        (Mathlib.Tactic.applyWith
         "apply"
         "("
         "config"
         ":="
         (Term.structInst
          "{"
          []
          [(Term.structInstField (Term.structInstLVal `instances []) ":=" `false)]
          (Term.optEllipsis [])
          []
          "}")
         ")"
         `mono_comp)
        []
        (Tactic.change
         "change"
         (Term.app
          `mono
          [(Term.app
            (Term.proj
             (Term.proj
              (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
               (Term.hole "_")
               " ≫ "
               (Term.app `D.f [`j `i]))
              "."
              `c)
             "."
             `app)
            [(Term.hole "_")])])
         [])
        []
        (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `comp_c_app)] "]") [])
        []
        (Mathlib.Tactic.applyWith
         "apply"
         "("
         "config"
         ":="
         (Term.structInst
          "{"
          []
          [(Term.structInstField (Term.structInstLVal `instances []) ":=" `false)]
          (Term.optEllipsis [])
          []
          "}")
         ")"
         `mono_comp)
        []
        (Tactic.tacticErw__
         "erw"
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] (Term.app `D.ι_image_preimage_eq [`i `j `U]))]
          "]")
         [])
        []
        (Tactic.allGoals
         "all_goals"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented [(Tactic.tacticInfer_instance "infer_instance")])))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.allGoals
       "all_goals"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented [(Tactic.tacticInfer_instance "infer_instance")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticInfer_instance "infer_instance")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticErw__
       "erw"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `D.ι_image_preimage_eq [`i `j `U]))] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `D.ι_image_preimage_eq [`i `j `U])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `D.ι_image_preimage_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.applyWith
       "apply"
       "("
       "config"
       ":="
       (Term.structInst
        "{"
        []
        [(Term.structInstField (Term.structInstLVal `instances []) ":=" `false)]
        (Term.optEllipsis [])
        []
        "}")
       ")"
       `mono_comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mono_comp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       []
       [(Term.structInstField (Term.structInstLVal `instances []) ":=" `false)]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `false
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `comp_c_app)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `comp_c_app
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       (Term.app
        `mono
        [(Term.app
          (Term.proj
           (Term.proj
            (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
             (Term.hole "_")
             " ≫ "
             (Term.app `D.f [`j `i]))
            "."
            `c)
           "."
           `app)
          [(Term.hole "_")])])
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mono
       [(Term.app
         (Term.proj
          (Term.proj
           (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
            (Term.hole "_")
            " ≫ "
            (Term.app `D.f [`j `i]))
           "."
           `c)
          "."
          `app)
         [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.proj
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.hole "_")
          " ≫ "
          (Term.app `D.f [`j `i]))
         "."
         `c)
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
        (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
         (Term.hole "_")
         " ≫ "
         (Term.app `D.f [`j `i]))
        "."
        `c)
       "."
       `app)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
        (Term.hole "_")
        " ≫ "
        (Term.app `D.f [`j `i]))
       "."
       `c)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
       (Term.hole "_")
       " ≫ "
       (Term.app `D.f [`j `i]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `D.f [`j `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `D.f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
      (Term.hole "_")
      " ≫ "
      (Term.app `D.f [`j `i]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj
       (Term.proj
        (Term.paren
         "("
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.hole "_")
          " ≫ "
          (Term.app `D.f [`j `i]))
         ")")
        "."
        `c)
       "."
       `app)
      [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mono
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.applyWith
       "apply"
       "("
       "config"
       ":="
       (Term.structInst
        "{"
        []
        [(Term.structInstField (Term.structInstLVal `instances []) ":=" `false)]
        (Term.optEllipsis [])
        []
        "}")
       ")"
       `mono_comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mono_comp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       []
       [(Term.structInstField (Term.structInstLVal `instances []) ":=" `false)]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `false
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.comp_id)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `category.comp_id
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert
       "convert"
       []
       (Term.app
        `limit.w
        [(Term.app
          `componentwise_diagram
          [(Term.proj
            (Term.proj
             (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
              "𝖣")
             "."
             `diagram)
            "."
            `multispan)
           (Term.hole "_")])
         (Term.app
          `Quiver.Hom.op
          [(Term.app `walking_multispan.hom.fst [(Term.tuple "(" [`i "," [`j]] ")")])])])
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `limit.w
       [(Term.app
         `componentwise_diagram
         [(Term.proj
           (Term.proj
            (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
             "𝖣")
            "."
            `diagram)
           "."
           `multispan)
          (Term.hole "_")])
        (Term.app
         `Quiver.Hom.op
         [(Term.app `walking_multispan.hom.fst [(Term.tuple "(" [`i "," [`j]] ")")])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Quiver.Hom.op
       [(Term.app `walking_multispan.hom.fst [(Term.tuple "(" [`i "," [`j]] ")")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `walking_multispan.hom.fst [(Term.tuple "(" [`i "," [`j]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`i "," [`j]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `walking_multispan.hom.fst
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `walking_multispan.hom.fst [(Term.tuple "(" [`i "," [`j]] ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Quiver.Hom.op
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `Quiver.Hom.op
      [(Term.paren
        "("
        (Term.app `walking_multispan.hom.fst [(Term.tuple "(" [`i "," [`j]] ")")])
        ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `componentwise_diagram
       [(Term.proj
         (Term.proj
          (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
           "𝖣")
          "."
          `diagram)
         "."
         `multispan)
        (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.proj
       (Term.proj
        (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
         "𝖣")
        "."
        `diagram)
       "."
       `multispan)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
        "𝖣")
       "."
       `diagram)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
       "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»', expected 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.term𝖣._@.AlgebraicGeometry.PresheafedSpace.Gluing._hyg.31'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- `ι_inv_app` is the right inverse of `D.ι i` on `U`. -/
  theorem
    π_ι_inv_app_π
    ( i j : D . J ) ( U : Opens D . U i . carrier )
      :
        D . diagramOverOpenπ U i ≫ D . ιInvAppπEqMap U ≫ D . ιInvApp U ≫ D . diagramOverOpenπ U j
          =
          D . diagramOverOpenπ U j
    :=
      by
        rw
            [
              ←
                cancel_mono
                  componentwise_diagram 𝖣 . diagram . multispan _ . map
                      Quiver.Hom.op walking_multispan.hom.snd ( i , j )
                    ≫
                    𝟙 _
              ]
          simp_rw [ category.assoc ]
          rw [ limit.w_assoc ]
          erw [ limit.lift_π_assoc ]
          rw [ category.comp_id , category.comp_id ]
          change _ ≫ _ ≫ _ ≫ _ ≫ _ = _
          rw [ congr_app D.t_id _ , id_c_app ]
          simp_rw [ category.assoc ]
          rw [ ← functor.map_comp_assoc , is_open_immersion.inv_naturality_assoc ]
          erw [ is_open_immersion.app_inv_app_assoc ]
          iterate 3 rw [ ← functor.map_comp_assoc ]
          rw [ nat_trans.naturality_assoc ]
          erw [ ← D.V ( i , j ) . Presheaf . map_comp ]
          convert
            limit.w
              componentwise_diagram 𝖣 . diagram . multispan _
                Quiver.Hom.op walking_multispan.hom.fst ( i , j )
          ·
            rw [ category.comp_id ]
              apply ( config := { instances := false } ) mono_comp
              change mono _ ≫ D.f j i . c . app _
              rw [ comp_c_app ]
              apply ( config := { instances := false } ) mono_comp
              erw [ D.ι_image_preimage_eq i j U ]
              all_goals infer_instance
#align
  algebraic_geometry.PresheafedSpace.glue_data.π_ι_inv_app_π AlgebraicGeometry.PresheafedSpaceCat.GlueData.π_ι_inv_app_π

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "`ι_inv_app` is the inverse of `D.ι i` on `U`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `π_ι_inv_app_eq_id [])
      (Command.declSig
       [(Term.explicitBinder "(" [`i] [":" (Term.proj `D "." `J)] [] ")")
        (Term.explicitBinder
         "("
         [`U]
         [":" (Term.app `Opens [(Term.proj (Term.app (Term.proj `D "." `U) [`i]) "." `carrier)])]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app (Term.proj `D "." `diagramOverOpenπ) [`U `i])
          " ≫ "
          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
           (Term.app (Term.proj `D "." `ιInvAppπEqMap) [`U])
           " ≫ "
           (Term.app (Term.proj `D "." `ιInvApp) [`U])))
         "="
         (Term.app (CategoryTheory.CategoryTheory.Category.Basic.«term𝟙» "𝟙") [(Term.hole "_")]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.Ext.«tacticExt___:_»
            "ext"
            [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `j))]
            [])
           []
           (Tactic.induction "induction" [`j] ["using" `Opposite.rec] [] [])
           []
           (Std.Tactic.rcases
            "rcases"
            [(Tactic.casesTarget [] `j)]
            ["with"
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.paren
                 "("
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                       [])]
                     "⟩")
                    "|"
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j)])
                       [])]
                     "⟩")])
                  [])
                 ")")])
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
                  `limit.w
                  [(Term.app
                    `componentwise_diagram
                    [(Term.proj
                      (Term.proj
                       (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                        "𝖣")
                       "."
                       `diagram)
                      "."
                      `multispan)
                     (Term.hole "_")])
                   (Term.app
                    `Quiver.Hom.op
                    [(Term.app `walking_multispan.hom.fst [(Term.tuple "(" [`j "," [`k]] ")")])])]))
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `category.assoc)
                ","
                (Tactic.rwRule [] `category.id_comp)]
               "]")
              [])
             []
             (Tactic.congr "congr" [(num "1")])
             []
             (Mathlib.Tactic.tacticSimp_rw__
              "simp_rw"
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
              [])
             []
             (Tactic.apply "apply" `π_ι_inv_app_π)])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Mathlib.Tactic.tacticSimp_rw__
              "simp_rw"
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
              [])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.id_comp)] "]")
              [])
             []
             (Tactic.apply "apply" `π_ι_inv_app_π)])])))
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
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `j))]
           [])
          []
          (Tactic.induction "induction" [`j] ["using" `Opposite.rec] [] [])
          []
          (Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] `j)]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.paren
                "("
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                      [])]
                    "⟩")
                   "|"
                   (Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j)])
                      [])]
                    "⟩")])
                 [])
                ")")])
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
                 `limit.w
                 [(Term.app
                   `componentwise_diagram
                   [(Term.proj
                     (Term.proj
                      (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                       "𝖣")
                      "."
                      `diagram)
                     "."
                     `multispan)
                    (Term.hole "_")])
                  (Term.app
                   `Quiver.Hom.op
                   [(Term.app `walking_multispan.hom.fst [(Term.tuple "(" [`j "," [`k]] ")")])])]))
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `category.assoc)
               ","
               (Tactic.rwRule [] `category.id_comp)]
              "]")
             [])
            []
            (Tactic.congr "congr" [(num "1")])
            []
            (Mathlib.Tactic.tacticSimp_rw__
             "simp_rw"
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
             [])
            []
            (Tactic.apply "apply" `π_ι_inv_app_π)])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Mathlib.Tactic.tacticSimp_rw__
             "simp_rw"
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
             [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.id_comp)] "]")
             [])
            []
            (Tactic.apply "apply" `π_ι_inv_app_π)])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Mathlib.Tactic.tacticSimp_rw__
         "simp_rw"
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
         [])
        []
        (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.id_comp)] "]") [])
        []
        (Tactic.apply "apply" `π_ι_inv_app_π)])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `π_ι_inv_app_π)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `π_ι_inv_app_π
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.id_comp)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `category.id_comp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `category.assoc
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
             `limit.w
             [(Term.app
               `componentwise_diagram
               [(Term.proj
                 (Term.proj
                  (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                   "𝖣")
                  "."
                  `diagram)
                 "."
                 `multispan)
                (Term.hole "_")])
              (Term.app
               `Quiver.Hom.op
               [(Term.app `walking_multispan.hom.fst [(Term.tuple "(" [`j "," [`k]] ")")])])]))
           ","
           (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `category.assoc)
           ","
           (Tactic.rwRule [] `category.id_comp)]
          "]")
         [])
        []
        (Tactic.congr "congr" [(num "1")])
        []
        (Mathlib.Tactic.tacticSimp_rw__
         "simp_rw"
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
         [])
        []
        (Tactic.apply "apply" `π_ι_inv_app_π)])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `π_ι_inv_app_π)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `π_ι_inv_app_π
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `category.assoc)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `category.assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.congr "congr" [(num "1")])
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
           `limit.w
           [(Term.app
             `componentwise_diagram
             [(Term.proj
               (Term.proj
                (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                 "𝖣")
                "."
                `diagram)
               "."
               `multispan)
              (Term.hole "_")])
            (Term.app
             `Quiver.Hom.op
             [(Term.app `walking_multispan.hom.fst [(Term.tuple "(" [`j "," [`k]] ")")])])]))
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `category.assoc)
         ","
         (Tactic.rwRule [] `category.id_comp)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `category.id_comp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `category.assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `limit.w
       [(Term.app
         `componentwise_diagram
         [(Term.proj
           (Term.proj
            (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
             "𝖣")
            "."
            `diagram)
           "."
           `multispan)
          (Term.hole "_")])
        (Term.app
         `Quiver.Hom.op
         [(Term.app `walking_multispan.hom.fst [(Term.tuple "(" [`j "," [`k]] ")")])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Quiver.Hom.op
       [(Term.app `walking_multispan.hom.fst [(Term.tuple "(" [`j "," [`k]] ")")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `walking_multispan.hom.fst [(Term.tuple "(" [`j "," [`k]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`j "," [`k]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `walking_multispan.hom.fst
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `walking_multispan.hom.fst [(Term.tuple "(" [`j "," [`k]] ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Quiver.Hom.op
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `Quiver.Hom.op
      [(Term.paren
        "("
        (Term.app `walking_multispan.hom.fst [(Term.tuple "(" [`j "," [`k]] ")")])
        ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `componentwise_diagram
       [(Term.proj
         (Term.proj
          (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
           "𝖣")
          "."
          `diagram)
         "."
         `multispan)
        (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.proj
       (Term.proj
        (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
         "𝖣")
        "."
        `diagram)
       "."
       `multispan)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
        "𝖣")
       "."
       `diagram)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
       "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»', expected 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.term𝖣._@.AlgebraicGeometry.PresheafedSpace.Gluing._hyg.31'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- `ι_inv_app` is the inverse of `D.ι i` on `U`. -/
  theorem
    π_ι_inv_app_eq_id
    ( i : D . J ) ( U : Opens D . U i . carrier )
      : D . diagramOverOpenπ U i ≫ D . ιInvAppπEqMap U ≫ D . ιInvApp U = 𝟙 _
    :=
      by
        ext j
          induction j using Opposite.rec
          rcases j with ( ⟨ j , k ⟩ | ⟨ j ⟩ )
          ·
            rw
                [
                  ←
                      limit.w
                        componentwise_diagram 𝖣 . diagram . multispan _
                          Quiver.Hom.op walking_multispan.hom.fst ( j , k )
                    ,
                    ← category.assoc
                    ,
                    category.id_comp
                  ]
              congr 1
              simp_rw [ category.assoc ]
              apply π_ι_inv_app_π
          · simp_rw [ category.assoc ] rw [ category.id_comp ] apply π_ι_inv_app_π
#align
  algebraic_geometry.PresheafedSpace.glue_data.π_ι_inv_app_eq_id AlgebraicGeometry.PresheafedSpaceCat.GlueData.π_ι_inv_app_eq_id

instance componentwise_diagram_π_is_iso (i : D.J) (U : Opens (D.U i).carrier) :
    IsIso (D.diagramOverOpenπ U i) :=
  by
  use D.ι_inv_app_π_eq_map U ≫ D.ι_inv_app U
  constructor
  · apply π_ι_inv_app_eq_id
  · rw [category.assoc, (D.ι_inv_app_π _).some_spec]
    exact iso.inv_hom_id ((D.to_glue_data.U i).Presheaf.mapIso (eq_to_iso _))
#align
  algebraic_geometry.PresheafedSpace.glue_data.componentwise_diagram_π_is_iso AlgebraicGeometry.PresheafedSpaceCat.GlueData.componentwise_diagram_π_is_iso

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `ιIsOpenImmersion [])]
      (Command.declSig
       [(Term.explicitBinder "(" [`i] [":" (Term.proj `D "." `J)] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `IsOpenImmersion
         [(Term.app
           (Term.proj
            (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
             "𝖣")
            "."
            `ι)
           [`i])])))
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `base_open
           []
           []
           ":="
           (Term.app (Term.proj `D "." `ι_open_embedding) [`i]))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `c_iso
           [`U]
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.tacticErw__
                "erw"
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule
                   [(patternIgnore (token.«← » "←"))]
                   `colimit_presheaf_obj_iso_componentwise_limit_hom_π)]
                 "]")
                [])
               []
               (Tactic.tacticInfer_instance "infer_instance")]))))))]
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
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticErw__
           "erw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              `colimit_presheaf_obj_iso_componentwise_limit_hom_π)]
            "]")
           [])
          []
          (Tactic.tacticInfer_instance "infer_instance")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticInfer_instance "infer_instance")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticErw__
       "erw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          `colimit_presheaf_obj_iso_componentwise_limit_hom_π)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `colimit_presheaf_obj_iso_componentwise_limit_hom_π
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `D "." `ι_open_embedding) [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `D "." `ι_open_embedding)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `D
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `IsOpenImmersion
       [(Term.app
         (Term.proj
          (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
           "𝖣")
          "."
          `ι)
         [`i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
         "𝖣")
        "."
        `ι)
       [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
        "𝖣")
       "."
       `ι)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
       "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»', expected 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.term𝖣._@.AlgebraicGeometry.PresheafedSpace.Gluing._hyg.31'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  ιIsOpenImmersion
  ( i : D . J ) : IsOpenImmersion 𝖣 . ι i
  where
    base_open := D . ι_open_embedding i
      c_iso U := by erw [ ← colimit_presheaf_obj_iso_componentwise_limit_hom_π ] infer_instance
#align
  algebraic_geometry.PresheafedSpace.glue_data.ι_is_open_immersion AlgebraicGeometry.PresheafedSpaceCat.GlueData.ιIsOpenImmersion

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The following diagram is a pullback, i.e. `Vᵢⱼ` is the intersection of `Uᵢ` and `Uⱼ` in `X`.\n\nVᵢⱼ ⟶ Uᵢ\n |      |\n ↓      ↓\n Uⱼ ⟶ X\n-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `vPullbackConeIsLimit [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`i `j] [":" (Term.proj `D "." `J)] [] ")")]
       [(Term.typeSpec
         ":"
         (Term.app
          `IsLimit
          [(Term.app
            (Term.proj
             (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
              "𝖣")
             "."
             `vPullbackCone)
            [`i `j])]))])
      (Command.declValSimple
       ":="
       (Term.app
        (Term.app `PullbackCone.isLimitAux' [(Term.hole "_")])
        [(Term.fun
          "fun"
          (Term.basicFun
           [`s]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.refine'
                "refine'"
                (Term.anonymousCtor
                 "⟨"
                 [(Term.hole "_") "," (Term.hole "_") "," (Term.hole "_") "," (Term.hole "_")]
                 "⟩"))
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.refine'
                  "refine'"
                  (Term.app
                   `PresheafedSpace.is_open_immersion.lift
                   [(Term.app `D.f [`i `j]) `s.fst (Term.hole "_")]))
                 []
                 (Tactic.tacticErw__
                  "erw"
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     (Term.app `D.to_Top_glue_data.preimage_range [`j `i]))]
                   "]")
                  [])
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    []
                    [(Term.typeSpec
                      ":"
                      («term_=_»
                       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                        `s.fst.base
                        " ≫ "
                        (Term.app `D.to_Top_glue_data.to_glue_data.ι [`i]))
                       "="
                       (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                        `s.snd.base
                        " ≫ "
                        (Term.app `D.to_Top_glue_data.to_glue_data.ι [`j]))))]
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
                            (Term.app
                             (Term.proj
                              (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                               "𝖣")
                              "."
                              `ι_glued_iso_hom)
                             [(Term.app `PresheafedSpace.forget [(Term.hole "_")])
                              (Term.hole "_")]))
                           ","
                           (Tactic.rwRule
                            [(patternIgnore (token.«← » "←"))]
                            (Term.app
                             (Term.proj
                              (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                               "𝖣")
                              "."
                              `ι_glued_iso_hom)
                             [(Term.app `PresheafedSpace.forget [(Term.hole "_")])
                              (Term.hole "_")]))]
                          "]")
                         [])
                        []
                        (Tactic.tacticHave_
                         "have"
                         (Term.haveDecl
                          (Term.haveIdDecl
                           []
                           []
                           ":="
                           (Term.app `congr_arg [`PresheafedSpace.hom.base `s.condition]))))
                        []
                        (Tactic.rwSeq
                         "rw"
                         []
                         (Tactic.rwRuleSeq
                          "["
                          [(Tactic.rwRule [] `comp_base) "," (Tactic.rwRule [] `comp_base)]
                          "]")
                         [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
                        []
                        (Tactic.reassoc! "reassoc!" [(group `this)])
                        []
                        (Tactic.exact "exact" (Term.app `this [(Term.hole "_")]))]))))))
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_subset_iff)
                    ","
                    (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_univ)
                    ","
                    (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_comp)
                    ","
                    (Tactic.rwRule [] `Set.image_univ)
                    ","
                    (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `coe_comp)
                    ","
                    (Tactic.rwRule [] `this)
                    ","
                    (Tactic.rwRule [] `coe_comp)
                    ","
                    (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_univ)
                    ","
                    (Tactic.rwRule [] `Set.image_comp)]
                   "]")
                  [])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.app `Set.image_subset_range [(Term.hole "_") (Term.hole "_")]))])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.apply "apply" `is_open_immersion.lift_fac)])
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
                      `cancel_mono
                      [(Term.app
                        (Term.proj
                         (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                          "𝖣")
                         "."
                         `ι)
                        [`j])]))
                    ","
                    (Tactic.rwRule [] `category.assoc)
                    ","
                    (Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     (Term.proj
                      (Term.app
                       (Term.proj
                        (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                         "𝖣")
                        "."
                        `vPullbackCone)
                       [`i `j])
                      "."
                      `condition))]
                   "]")
                  [])
                 []
                 (Mathlib.Tactic.Conv.convRHS
                  "conv_rhs"
                  []
                  []
                  "=>"
                  (Tactic.Conv.convSeq
                   (Tactic.Conv.convSeq1Indented
                    [(Tactic.Conv.convRw__
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `s.condition)]
                       "]"))])))
                 []
                 (Tactic.tacticErw__
                  "erw"
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `is_open_immersion.lift_fac_assoc)] "]")
                  [])])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.intro "intro" [`m `e₁ `e₂])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     (Term.app `cancel_mono [(Term.app `D.f [`i `j])]))]
                   "]")
                  [])
                 []
                 (Tactic.tacticErw__ "erw" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `e₁)] "]") [])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `is_open_immersion.lift_fac)] "]")
                  [])])])))))])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app `PullbackCone.isLimitAux' [(Term.hole "_")])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`s]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.refine'
               "refine'"
               (Term.anonymousCtor
                "⟨"
                [(Term.hole "_") "," (Term.hole "_") "," (Term.hole "_") "," (Term.hole "_")]
                "⟩"))
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.refine'
                 "refine'"
                 (Term.app
                  `PresheafedSpace.is_open_immersion.lift
                  [(Term.app `D.f [`i `j]) `s.fst (Term.hole "_")]))
                []
                (Tactic.tacticErw__
                 "erw"
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule
                    [(patternIgnore (token.«← » "←"))]
                    (Term.app `D.to_Top_glue_data.preimage_range [`j `i]))]
                  "]")
                 [])
                []
                (Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   []
                   [(Term.typeSpec
                     ":"
                     («term_=_»
                      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                       `s.fst.base
                       " ≫ "
                       (Term.app `D.to_Top_glue_data.to_glue_data.ι [`i]))
                      "="
                      (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                       `s.snd.base
                       " ≫ "
                       (Term.app `D.to_Top_glue_data.to_glue_data.ι [`j]))))]
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
                           (Term.app
                            (Term.proj
                             (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                              "𝖣")
                             "."
                             `ι_glued_iso_hom)
                            [(Term.app `PresheafedSpace.forget [(Term.hole "_")]) (Term.hole "_")]))
                          ","
                          (Tactic.rwRule
                           [(patternIgnore (token.«← » "←"))]
                           (Term.app
                            (Term.proj
                             (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                              "𝖣")
                             "."
                             `ι_glued_iso_hom)
                            [(Term.app `PresheafedSpace.forget [(Term.hole "_")])
                             (Term.hole "_")]))]
                         "]")
                        [])
                       []
                       (Tactic.tacticHave_
                        "have"
                        (Term.haveDecl
                         (Term.haveIdDecl
                          []
                          []
                          ":="
                          (Term.app `congr_arg [`PresheafedSpace.hom.base `s.condition]))))
                       []
                       (Tactic.rwSeq
                        "rw"
                        []
                        (Tactic.rwRuleSeq
                         "["
                         [(Tactic.rwRule [] `comp_base) "," (Tactic.rwRule [] `comp_base)]
                         "]")
                        [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
                       []
                       (Tactic.reassoc! "reassoc!" [(group `this)])
                       []
                       (Tactic.exact "exact" (Term.app `this [(Term.hole "_")]))]))))))
                []
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_subset_iff)
                   ","
                   (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_univ)
                   ","
                   (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_comp)
                   ","
                   (Tactic.rwRule [] `Set.image_univ)
                   ","
                   (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `coe_comp)
                   ","
                   (Tactic.rwRule [] `this)
                   ","
                   (Tactic.rwRule [] `coe_comp)
                   ","
                   (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_univ)
                   ","
                   (Tactic.rwRule [] `Set.image_comp)]
                  "]")
                 [])
                []
                (Tactic.exact
                 "exact"
                 (Term.app `Set.image_subset_range [(Term.hole "_") (Term.hole "_")]))])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.apply "apply" `is_open_immersion.lift_fac)])
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
                     `cancel_mono
                     [(Term.app
                       (Term.proj
                        (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                         "𝖣")
                        "."
                        `ι)
                       [`j])]))
                   ","
                   (Tactic.rwRule [] `category.assoc)
                   ","
                   (Tactic.rwRule
                    [(patternIgnore (token.«← » "←"))]
                    (Term.proj
                     (Term.app
                      (Term.proj
                       (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                        "𝖣")
                       "."
                       `vPullbackCone)
                      [`i `j])
                     "."
                     `condition))]
                  "]")
                 [])
                []
                (Mathlib.Tactic.Conv.convRHS
                 "conv_rhs"
                 []
                 []
                 "=>"
                 (Tactic.Conv.convSeq
                  (Tactic.Conv.convSeq1Indented
                   [(Tactic.Conv.convRw__
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `s.condition)]
                      "]"))])))
                []
                (Tactic.tacticErw__
                 "erw"
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `is_open_immersion.lift_fac_assoc)] "]")
                 [])])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.intro "intro" [`m `e₁ `e₂])
                []
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule
                    [(patternIgnore (token.«← » "←"))]
                    (Term.app `cancel_mono [(Term.app `D.f [`i `j])]))]
                  "]")
                 [])
                []
                (Tactic.tacticErw__ "erw" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `e₁)] "]") [])
                []
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `is_open_immersion.lift_fac)] "]")
                 [])])])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`s]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.refine'
             "refine'"
             (Term.anonymousCtor
              "⟨"
              [(Term.hole "_") "," (Term.hole "_") "," (Term.hole "_") "," (Term.hole "_")]
              "⟩"))
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.refine'
               "refine'"
               (Term.app
                `PresheafedSpace.is_open_immersion.lift
                [(Term.app `D.f [`i `j]) `s.fst (Term.hole "_")]))
              []
              (Tactic.tacticErw__
               "erw"
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule
                  [(patternIgnore (token.«← » "←"))]
                  (Term.app `D.to_Top_glue_data.preimage_range [`j `i]))]
                "]")
               [])
              []
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 []
                 [(Term.typeSpec
                   ":"
                   («term_=_»
                    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                     `s.fst.base
                     " ≫ "
                     (Term.app `D.to_Top_glue_data.to_glue_data.ι [`i]))
                    "="
                    (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                     `s.snd.base
                     " ≫ "
                     (Term.app `D.to_Top_glue_data.to_glue_data.ι [`j]))))]
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
                         (Term.app
                          (Term.proj
                           (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                            "𝖣")
                           "."
                           `ι_glued_iso_hom)
                          [(Term.app `PresheafedSpace.forget [(Term.hole "_")]) (Term.hole "_")]))
                        ","
                        (Tactic.rwRule
                         [(patternIgnore (token.«← » "←"))]
                         (Term.app
                          (Term.proj
                           (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                            "𝖣")
                           "."
                           `ι_glued_iso_hom)
                          [(Term.app `PresheafedSpace.forget [(Term.hole "_")]) (Term.hole "_")]))]
                       "]")
                      [])
                     []
                     (Tactic.tacticHave_
                      "have"
                      (Term.haveDecl
                       (Term.haveIdDecl
                        []
                        []
                        ":="
                        (Term.app `congr_arg [`PresheafedSpace.hom.base `s.condition]))))
                     []
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [] `comp_base) "," (Tactic.rwRule [] `comp_base)]
                       "]")
                      [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
                     []
                     (Tactic.reassoc! "reassoc!" [(group `this)])
                     []
                     (Tactic.exact "exact" (Term.app `this [(Term.hole "_")]))]))))))
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_subset_iff)
                 ","
                 (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_univ)
                 ","
                 (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_comp)
                 ","
                 (Tactic.rwRule [] `Set.image_univ)
                 ","
                 (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `coe_comp)
                 ","
                 (Tactic.rwRule [] `this)
                 ","
                 (Tactic.rwRule [] `coe_comp)
                 ","
                 (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_univ)
                 ","
                 (Tactic.rwRule [] `Set.image_comp)]
                "]")
               [])
              []
              (Tactic.exact
               "exact"
               (Term.app `Set.image_subset_range [(Term.hole "_") (Term.hole "_")]))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.apply "apply" `is_open_immersion.lift_fac)])
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
                   `cancel_mono
                   [(Term.app
                     (Term.proj
                      (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                       "𝖣")
                      "."
                      `ι)
                     [`j])]))
                 ","
                 (Tactic.rwRule [] `category.assoc)
                 ","
                 (Tactic.rwRule
                  [(patternIgnore (token.«← » "←"))]
                  (Term.proj
                   (Term.app
                    (Term.proj
                     (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                      "𝖣")
                     "."
                     `vPullbackCone)
                    [`i `j])
                   "."
                   `condition))]
                "]")
               [])
              []
              (Mathlib.Tactic.Conv.convRHS
               "conv_rhs"
               []
               []
               "=>"
               (Tactic.Conv.convSeq
                (Tactic.Conv.convSeq1Indented
                 [(Tactic.Conv.convRw__
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `s.condition)]
                    "]"))])))
              []
              (Tactic.tacticErw__
               "erw"
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `is_open_immersion.lift_fac_assoc)] "]")
               [])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.intro "intro" [`m `e₁ `e₂])
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule
                  [(patternIgnore (token.«← » "←"))]
                  (Term.app `cancel_mono [(Term.app `D.f [`i `j])]))]
                "]")
               [])
              []
              (Tactic.tacticErw__ "erw" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `e₁)] "]") [])
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `is_open_immersion.lift_fac)] "]")
               [])])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.refine'
           "refine'"
           (Term.anonymousCtor
            "⟨"
            [(Term.hole "_") "," (Term.hole "_") "," (Term.hole "_") "," (Term.hole "_")]
            "⟩"))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.refine'
             "refine'"
             (Term.app
              `PresheafedSpace.is_open_immersion.lift
              [(Term.app `D.f [`i `j]) `s.fst (Term.hole "_")]))
            []
            (Tactic.tacticErw__
             "erw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.app `D.to_Top_glue_data.preimage_range [`j `i]))]
              "]")
             [])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec
                 ":"
                 («term_=_»
                  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                   `s.fst.base
                   " ≫ "
                   (Term.app `D.to_Top_glue_data.to_glue_data.ι [`i]))
                  "="
                  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                   `s.snd.base
                   " ≫ "
                   (Term.app `D.to_Top_glue_data.to_glue_data.ι [`j]))))]
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
                       (Term.app
                        (Term.proj
                         (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                          "𝖣")
                         "."
                         `ι_glued_iso_hom)
                        [(Term.app `PresheafedSpace.forget [(Term.hole "_")]) (Term.hole "_")]))
                      ","
                      (Tactic.rwRule
                       [(patternIgnore (token.«← » "←"))]
                       (Term.app
                        (Term.proj
                         (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                          "𝖣")
                         "."
                         `ι_glued_iso_hom)
                        [(Term.app `PresheafedSpace.forget [(Term.hole "_")]) (Term.hole "_")]))]
                     "]")
                    [])
                   []
                   (Tactic.tacticHave_
                    "have"
                    (Term.haveDecl
                     (Term.haveIdDecl
                      []
                      []
                      ":="
                      (Term.app `congr_arg [`PresheafedSpace.hom.base `s.condition]))))
                   []
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] `comp_base) "," (Tactic.rwRule [] `comp_base)]
                     "]")
                    [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
                   []
                   (Tactic.reassoc! "reassoc!" [(group `this)])
                   []
                   (Tactic.exact "exact" (Term.app `this [(Term.hole "_")]))]))))))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_subset_iff)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_univ)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_comp)
               ","
               (Tactic.rwRule [] `Set.image_univ)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `coe_comp)
               ","
               (Tactic.rwRule [] `this)
               ","
               (Tactic.rwRule [] `coe_comp)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Set.image_univ)
               ","
               (Tactic.rwRule [] `Set.image_comp)]
              "]")
             [])
            []
            (Tactic.exact
             "exact"
             (Term.app `Set.image_subset_range [(Term.hole "_") (Term.hole "_")]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.apply "apply" `is_open_immersion.lift_fac)])
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
                 `cancel_mono
                 [(Term.app
                   (Term.proj
                    (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                     "𝖣")
                    "."
                    `ι)
                   [`j])]))
               ","
               (Tactic.rwRule [] `category.assoc)
               ","
               (Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.proj
                 (Term.app
                  (Term.proj
                   (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                    "𝖣")
                   "."
                   `vPullbackCone)
                  [`i `j])
                 "."
                 `condition))]
              "]")
             [])
            []
            (Mathlib.Tactic.Conv.convRHS
             "conv_rhs"
             []
             []
             "=>"
             (Tactic.Conv.convSeq
              (Tactic.Conv.convSeq1Indented
               [(Tactic.Conv.convRw__
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `s.condition)]
                  "]"))])))
            []
            (Tactic.tacticErw__
             "erw"
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `is_open_immersion.lift_fac_assoc)] "]")
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro "intro" [`m `e₁ `e₂])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.app `cancel_mono [(Term.app `D.f [`i `j])]))]
              "]")
             [])
            []
            (Tactic.tacticErw__ "erw" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `e₁)] "]") [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `is_open_immersion.lift_fac)] "]")
             [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.intro "intro" [`m `e₁ `e₂])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            [(patternIgnore (token.«← » "←"))]
            (Term.app `cancel_mono [(Term.app `D.f [`i `j])]))]
          "]")
         [])
        []
        (Tactic.tacticErw__ "erw" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `e₁)] "]") [])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `is_open_immersion.lift_fac)] "]")
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `is_open_immersion.lift_fac)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `is_open_immersion.lift_fac
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticErw__ "erw" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `e₁)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e₁
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
          [(patternIgnore (token.«← » "←"))]
          (Term.app `cancel_mono [(Term.app `D.f [`i `j])]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `cancel_mono [(Term.app `D.f [`i `j])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `D.f [`i `j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `D.f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `D.f [`i `j]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `cancel_mono
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`m `e₁ `e₂])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `e₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `m
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
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
             `cancel_mono
             [(Term.app
               (Term.proj
                (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                 "𝖣")
                "."
                `ι)
               [`j])]))
           ","
           (Tactic.rwRule [] `category.assoc)
           ","
           (Tactic.rwRule
            [(patternIgnore (token.«← » "←"))]
            (Term.proj
             (Term.app
              (Term.proj
               (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                "𝖣")
               "."
               `vPullbackCone)
              [`i `j])
             "."
             `condition))]
          "]")
         [])
        []
        (Mathlib.Tactic.Conv.convRHS
         "conv_rhs"
         []
         []
         "=>"
         (Tactic.Conv.convSeq
          (Tactic.Conv.convSeq1Indented
           [(Tactic.Conv.convRw__
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `s.condition)]
              "]"))])))
        []
        (Tactic.tacticErw__
         "erw"
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `is_open_immersion.lift_fac_assoc)] "]")
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticErw__
       "erw"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `is_open_immersion.lift_fac_assoc)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `is_open_immersion.lift_fac_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.Conv.convRHS
       "conv_rhs"
       []
       []
       "=>"
       (Tactic.Conv.convSeq
        (Tactic.Conv.convSeq1Indented
         [(Tactic.Conv.convRw__
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `s.condition)]
            "]"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convSeq1Indented', expected 'Lean.Parser.Tactic.Conv.convSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s.condition
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
          [(patternIgnore (token.«← » "←"))]
          (Term.app
           `cancel_mono
           [(Term.app
             (Term.proj
              (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
               "𝖣")
              "."
              `ι)
             [`j])]))
         ","
         (Tactic.rwRule [] `category.assoc)
         ","
         (Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.proj
           (Term.app
            (Term.proj
             (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
              "𝖣")
             "."
             `vPullbackCone)
            [`i `j])
           "."
           `condition))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        (Term.proj
         (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
          "𝖣")
         "."
         `vPullbackCone)
        [`i `j])
       "."
       `condition)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
         "𝖣")
        "."
        `vPullbackCone)
       [`i `j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
        "𝖣")
       "."
       `vPullbackCone)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
       "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»', expected 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.term𝖣._@.AlgebraicGeometry.PresheafedSpace.Gluing._hyg.31'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
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
    The following diagram is a pullback, i.e. `Vᵢⱼ` is the intersection of `Uᵢ` and `Uⱼ` in `X`.
    
    Vᵢⱼ ⟶ Uᵢ
     |      |
     ↓      ↓
     Uⱼ ⟶ X
    -/
  def
    vPullbackConeIsLimit
    ( i j : D . J ) : IsLimit 𝖣 . vPullbackCone i j
    :=
      PullbackCone.isLimitAux' _
        fun
          s
            =>
            by
              refine' ⟨ _ , _ , _ , _ ⟩
                ·
                  refine' PresheafedSpace.is_open_immersion.lift D.f i j s.fst _
                    erw [ ← D.to_Top_glue_data.preimage_range j i ]
                    have
                      :
                          s.fst.base ≫ D.to_Top_glue_data.to_glue_data.ι i
                            =
                            s.snd.base ≫ D.to_Top_glue_data.to_glue_data.ι j
                        :=
                        by
                          rw
                              [
                                ← 𝖣 . ι_glued_iso_hom PresheafedSpace.forget _ _
                                  ,
                                  ← 𝖣 . ι_glued_iso_hom PresheafedSpace.forget _ _
                                ]
                            have := congr_arg PresheafedSpace.hom.base s.condition
                            rw [ comp_base , comp_base ] at this
                            reassoc! this
                            exact this _
                    rw
                      [
                        ← Set.image_subset_iff
                          ,
                          ← Set.image_univ
                          ,
                          ← Set.image_comp
                          ,
                          Set.image_univ
                          ,
                          ← coe_comp
                          ,
                          this
                          ,
                          coe_comp
                          ,
                          ← Set.image_univ
                          ,
                          Set.image_comp
                        ]
                    exact Set.image_subset_range _ _
                · apply is_open_immersion.lift_fac
                ·
                  rw
                      [
                        ← cancel_mono 𝖣 . ι j , category.assoc , ← 𝖣 . vPullbackCone i j . condition
                        ]
                    conv_rhs => rw [ ← s.condition ]
                    erw [ is_open_immersion.lift_fac_assoc ]
                ·
                  intro m e₁ e₂
                    rw [ ← cancel_mono D.f i j ]
                    erw [ e₁ ]
                    rw [ is_open_immersion.lift_fac ]
#align
  algebraic_geometry.PresheafedSpace.glue_data.V_pullback_cone_is_limit AlgebraicGeometry.PresheafedSpaceCat.GlueData.vPullbackConeIsLimit

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `ι_jointly_surjective [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`x]
         [":"
          (Term.proj
           (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
            "𝖣")
           "."
           `glued)]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders
          [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i)] ":" (Term.proj `D "." `J) ")")
           (Lean.bracketedExplicitBinders
            "("
            [(Lean.binderIdent `y)]
            ":"
            (Term.app (Term.proj `D "." `U) [`i])
            ")")])
         ","
         («term_=_»
          (Term.app
           (Term.proj
            (Term.app
             (Term.proj
              (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
               "𝖣")
              "."
              `ι)
             [`i])
            "."
            `base)
           [`y])
          "="
          `x))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
          "𝖣")
         "."
         `ι_jointly_surjective)
        [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
          (Term.app `PresheafedSpaceCat.forget [(Term.hole "_")])
          " ⋙ "
          (Term.app `CategoryTheory.forget [`TopCat]))
         `x])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
         "𝖣")
        "."
        `ι_jointly_surjective)
       [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
         (Term.app `PresheafedSpaceCat.forget [(Term.hole "_")])
         " ⋙ "
         (Term.app `CategoryTheory.forget [`TopCat]))
        `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
       (Term.app `PresheafedSpaceCat.forget [(Term.hole "_")])
       " ⋙ "
       (Term.app `CategoryTheory.forget [`TopCat]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `CategoryTheory.forget [`TopCat])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `TopCat
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `CategoryTheory.forget
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `PresheafedSpaceCat.forget [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `PresheafedSpaceCat.forget
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
      (Term.app `PresheafedSpaceCat.forget [(Term.hole "_")])
      " ⋙ "
      (Term.app `CategoryTheory.forget [`TopCat]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
        "𝖣")
       "."
       `ι_jointly_surjective)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
       "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»', expected 'AlgebraicGeometry.PresheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.term𝖣._@.AlgebraicGeometry.PresheafedSpace.Gluing._hyg.31'
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
  ι_jointly_surjective
  ( x : 𝖣 . glued ) : ∃ ( i : D . J ) ( y : D . U i ) , 𝖣 . ι i . base y = x
  := 𝖣 . ι_jointly_surjective PresheafedSpaceCat.forget _ ⋙ CategoryTheory.forget TopCat x
#align
  algebraic_geometry.PresheafedSpace.glue_data.ι_jointly_surjective AlgebraicGeometry.PresheafedSpaceCat.GlueData.ι_jointly_surjective

end GlueData

end PresheafedSpaceCat

namespace SheafedSpaceCat

variable (C) [HasProducts.{v} C]

/-- A family of gluing data consists of
1. An index type `J`
2. A sheafed space `U i` for each `i : J`.
3. A sheafed space `V i j` for each `i j : J`.
  (Note that this is `J × J → SheafedSpace C` rather than `J → J → SheafedSpace C` to
  connect to the limits library easier.)
4. An open immersion `f i j : V i j ⟶ U i` for each `i j : ι`.
5. A transition map `t i j : V i j ⟶ V j i` for each `i j : ι`.
such that
6. `f i i` is an isomorphism.
7. `t i i` is the identity.
8. `V i j ×[U i] V i k ⟶ V i j ⟶ V j i` factors through `V j k ×[U j] V j i ⟶ V j i` via some
    `t' : V i j ×[U i] V i k ⟶ V j k ×[U j] V j i`.
9. `t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _`.

We can then glue the spaces `U i` together by identifying `V i j` with `V j i`, such
that the `U i`'s are open subspaces of the glued space.
-/
@[nolint has_nonempty_instance]
structure GlueData extends GlueData (SheafedSpaceCat.{v} C) where
  f_open : ∀ i j, SheafedSpaceCat.IsOpenImmersion (f i j)
#align algebraic_geometry.SheafedSpace.glue_data AlgebraicGeometry.SheafedSpaceCat.GlueData

attribute [instance] glue_data.f_open

namespace GlueData

variable {C} (D : GlueData C)

-- mathport name: «expr𝖣»
local notation "𝖣" => D.toGlueData

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The glue data of presheafed spaces associated to a family of glue data of sheafed spaces. -/")]
      []
      []
      []
      []
      [])
     (Command.abbrev
      "abbrev"
      (Command.declId `toPresheafedSpaceGlueData [])
      (Command.optDeclSig [] [(Term.typeSpec ":" (Term.app `PresheafedSpaceCat.GlueData [`C]))])
      (Command.declValSimple
       ":="
       (Term.structInst
        "{"
        []
        [(Term.structInstField (Term.structInstLVal `f_open []) ":=" (Term.proj `D "." `f_open))
         []
         (Term.structInstField
          (Term.structInstLVal `toGlueData [])
          ":="
          (Term.app
           (Term.proj
            (AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
             "𝖣")
            "."
            `mapGlueData)
           [`forgetToPresheafedSpace]))]
        (Term.optEllipsis [])
        []
        "}")
       [])
      []
      []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       []
       [(Term.structInstField (Term.structInstLVal `f_open []) ":=" (Term.proj `D "." `f_open))
        []
        (Term.structInstField
         (Term.structInstLVal `toGlueData [])
         ":="
         (Term.app
          (Term.proj
           (AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
            "𝖣")
           "."
           `mapGlueData)
          [`forgetToPresheafedSpace]))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
         "𝖣")
        "."
        `mapGlueData)
       [`forgetToPresheafedSpace])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `forgetToPresheafedSpace
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
        "𝖣")
       "."
       `mapGlueData)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
       "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»', expected 'AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.term𝖣._@.AlgebraicGeometry.PresheafedSpace.Gluing._hyg.351'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The glue data of presheafed spaces associated to a family of glue data of sheafed spaces. -/
  abbrev
    toPresheafedSpaceGlueData
    : PresheafedSpaceCat.GlueData C
    := { f_open := D . f_open toGlueData := 𝖣 . mapGlueData forgetToPresheafedSpace }
#align
  algebraic_geometry.SheafedSpace.glue_data.to_PresheafedSpace_glue_data AlgebraicGeometry.SheafedSpaceCat.GlueData.toPresheafedSpaceGlueData

variable [HasLimits C]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The gluing as sheafed spaces is isomorphic to the gluing as presheafed spaces. -/")]
      []
      []
      []
      []
      [])
     (Command.abbrev
      "abbrev"
      (Command.declId `isoPresheafedSpace [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (CategoryTheory.CategoryTheory.Isomorphism.«term_≅_»
          (Term.proj
           (Term.proj
            (AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
             "𝖣")
            "."
            `glued)
           "."
           `toPresheafedSpace)
          " ≅ "
          (Term.proj
           (Term.proj (Term.proj `D "." `toPresheafedSpaceGlueData) "." `toGlueData)
           "."
           `glued)))])
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
          "𝖣")
         "."
         `gluedIso)
        [`forgetToPresheafedSpace])
       [])
      []
      []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
         "𝖣")
        "."
        `gluedIso)
       [`forgetToPresheafedSpace])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `forgetToPresheafedSpace
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
        "𝖣")
       "."
       `gluedIso)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
       "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»', expected 'AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.term𝖣._@.AlgebraicGeometry.PresheafedSpace.Gluing._hyg.351'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The gluing as sheafed spaces is isomorphic to the gluing as presheafed spaces. -/
  abbrev
    isoPresheafedSpace
    : 𝖣 . glued . toPresheafedSpace ≅ D . toPresheafedSpaceGlueData . toGlueData . glued
    := 𝖣 . gluedIso forgetToPresheafedSpace
#align
  algebraic_geometry.SheafedSpace.glue_data.iso_PresheafedSpace AlgebraicGeometry.SheafedSpaceCat.GlueData.isoPresheafedSpace

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `ι_iso_PresheafedSpace_inv [])
      (Command.declSig
       [(Term.explicitBinder "(" [`i] [":" (Term.proj `D "." `J)] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app
           (Term.proj
            (Term.proj (Term.proj `D "." `toPresheafedSpaceGlueData) "." `toGlueData)
            "."
            `ι)
           [`i])
          " ≫ "
          (Term.proj (Term.proj `D "." `isoPresheafedSpace) "." `inv))
         "="
         (Term.app
          (Term.proj
           (AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
            "𝖣")
           "."
           `ι)
          [`i]))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
          "𝖣")
         "."
         `ι_glued_iso_inv)
        [(Term.hole "_") (Term.hole "_")])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
         "𝖣")
        "."
        `ι_glued_iso_inv)
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
       (AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
        "𝖣")
       "."
       `ι_glued_iso_inv)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
       "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»', expected 'AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.term𝖣._@.AlgebraicGeometry.PresheafedSpace.Gluing._hyg.351'
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
  ι_iso_PresheafedSpace_inv
  ( i : D . J )
    : D . toPresheafedSpaceGlueData . toGlueData . ι i ≫ D . isoPresheafedSpace . inv = 𝖣 . ι i
  := 𝖣 . ι_glued_iso_inv _ _
#align
  algebraic_geometry.SheafedSpace.glue_data.ι_iso_PresheafedSpace_inv AlgebraicGeometry.SheafedSpaceCat.GlueData.ι_iso_PresheafedSpace_inv

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `ι_is_open_immersion [])]
      (Command.declSig
       [(Term.explicitBinder "(" [`i] [":" (Term.proj `D "." `J)] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `IsOpenImmersion
         [(Term.app
           (Term.proj
            (AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
             "𝖣")
            "."
            `ι)
           [`i])])))
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
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `D.ι_iso_PresheafedSpace_inv)]
             "]")
            [])
           []
           (Tactic.tacticInfer_instance "infer_instance")])))
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
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `D.ι_iso_PresheafedSpace_inv)]
            "]")
           [])
          []
          (Tactic.tacticInfer_instance "infer_instance")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticInfer_instance "infer_instance")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `D.ι_iso_PresheafedSpace_inv)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `D.ι_iso_PresheafedSpace_inv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `IsOpenImmersion
       [(Term.app
         (Term.proj
          (AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
           "𝖣")
          "."
          `ι)
         [`i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
         "𝖣")
        "."
        `ι)
       [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
        "𝖣")
       "."
       `ι)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
       "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»', expected 'AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.term𝖣._@.AlgebraicGeometry.PresheafedSpace.Gluing._hyg.351'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  ι_is_open_immersion
  ( i : D . J ) : IsOpenImmersion 𝖣 . ι i
  := by rw [ ← D.ι_iso_PresheafedSpace_inv ] infer_instance
#align
  algebraic_geometry.SheafedSpace.glue_data.ι_is_open_immersion AlgebraicGeometry.SheafedSpaceCat.GlueData.ι_is_open_immersion

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `ι_jointly_surjective [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`x]
         [":"
          (Term.proj
           (AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
            "𝖣")
           "."
           `glued)]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders
          [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i)] ":" (Term.proj `D "." `J) ")")
           (Lean.bracketedExplicitBinders
            "("
            [(Lean.binderIdent `y)]
            ":"
            (Term.app (Term.proj `D "." `U) [`i])
            ")")])
         ","
         («term_=_»
          (Term.app
           (Term.proj
            (Term.app
             (Term.proj
              (AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
               "𝖣")
              "."
              `ι)
             [`i])
            "."
            `base)
           [`y])
          "="
          `x))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
          "𝖣")
         "."
         `ι_jointly_surjective)
        [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
          (Term.app `SheafedSpaceCat.forget [(Term.hole "_")])
          " ⋙ "
          (Term.app `CategoryTheory.forget [`TopCat]))
         `x])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
         "𝖣")
        "."
        `ι_jointly_surjective)
       [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
         (Term.app `SheafedSpaceCat.forget [(Term.hole "_")])
         " ⋙ "
         (Term.app `CategoryTheory.forget [`TopCat]))
        `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
       (Term.app `SheafedSpaceCat.forget [(Term.hole "_")])
       " ⋙ "
       (Term.app `CategoryTheory.forget [`TopCat]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `CategoryTheory.forget [`TopCat])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `TopCat
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `CategoryTheory.forget
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `SheafedSpaceCat.forget [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `SheafedSpaceCat.forget
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
      (Term.app `SheafedSpaceCat.forget [(Term.hole "_")])
      " ⋙ "
      (Term.app `CategoryTheory.forget [`TopCat]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
        "𝖣")
       "."
       `ι_jointly_surjective)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
       "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»', expected 'AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.term𝖣._@.AlgebraicGeometry.PresheafedSpace.Gluing._hyg.351'
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
  ι_jointly_surjective
  ( x : 𝖣 . glued ) : ∃ ( i : D . J ) ( y : D . U i ) , 𝖣 . ι i . base y = x
  := 𝖣 . ι_jointly_surjective SheafedSpaceCat.forget _ ⋙ CategoryTheory.forget TopCat x
#align
  algebraic_geometry.SheafedSpace.glue_data.ι_jointly_surjective AlgebraicGeometry.SheafedSpaceCat.GlueData.ι_jointly_surjective

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The following diagram is a pullback, i.e. `Vᵢⱼ` is the intersection of `Uᵢ` and `Uⱼ` in `X`.\n\nVᵢⱼ ⟶ Uᵢ\n |      |\n ↓      ↓\n Uⱼ ⟶ X\n-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `vPullbackConeIsLimit [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`i `j] [":" (Term.proj `D "." `J)] [] ")")]
       [(Term.typeSpec
         ":"
         (Term.app
          `IsLimit
          [(Term.app
            (Term.proj
             (AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
              "𝖣")
             "."
             `vPullbackCone)
            [`i `j])]))])
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
          "𝖣")
         "."
         `vPullbackConeIsLimitOfMap)
        [`forgetToPresheafedSpace
         `i
         `j
         (Term.app
          (Term.proj (Term.proj `D "." `toPresheafedSpaceGlueData) "." `vPullbackConeIsLimit)
          [(Term.hole "_") (Term.hole "_")])])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
         "𝖣")
        "."
        `vPullbackConeIsLimitOfMap)
       [`forgetToPresheafedSpace
        `i
        `j
        (Term.app
         (Term.proj (Term.proj `D "." `toPresheafedSpaceGlueData) "." `vPullbackConeIsLimit)
         [(Term.hole "_") (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.proj `D "." `toPresheafedSpaceGlueData) "." `vPullbackConeIsLimit)
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
      (Term.proj (Term.proj `D "." `toPresheafedSpaceGlueData) "." `vPullbackConeIsLimit)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `D "." `toPresheafedSpaceGlueData)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `D
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.proj `D "." `toPresheafedSpaceGlueData) "." `vPullbackConeIsLimit)
      [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `forgetToPresheafedSpace
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
        "𝖣")
       "."
       `vPullbackConeIsLimitOfMap)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
       "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»', expected 'AlgebraicGeometry.SheafedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.term𝖣._@.AlgebraicGeometry.PresheafedSpace.Gluing._hyg.351'
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
    The following diagram is a pullback, i.e. `Vᵢⱼ` is the intersection of `Uᵢ` and `Uⱼ` in `X`.
    
    Vᵢⱼ ⟶ Uᵢ
     |      |
     ↓      ↓
     Uⱼ ⟶ X
    -/
  def
    vPullbackConeIsLimit
    ( i j : D . J ) : IsLimit 𝖣 . vPullbackCone i j
    :=
      𝖣 . vPullbackConeIsLimitOfMap
        forgetToPresheafedSpace i j D . toPresheafedSpaceGlueData . vPullbackConeIsLimit _ _
#align
  algebraic_geometry.SheafedSpace.glue_data.V_pullback_cone_is_limit AlgebraicGeometry.SheafedSpaceCat.GlueData.vPullbackConeIsLimit

end GlueData

end SheafedSpaceCat

namespace LocallyRingedSpaceCat

/-- A family of gluing data consists of
1. An index type `J`
2. A locally ringed space `U i` for each `i : J`.
3. A locally ringed space `V i j` for each `i j : J`.
  (Note that this is `J × J → LocallyRingedSpace` rather than `J → J → LocallyRingedSpace` to
  connect to the limits library easier.)
4. An open immersion `f i j : V i j ⟶ U i` for each `i j : ι`.
5. A transition map `t i j : V i j ⟶ V j i` for each `i j : ι`.
such that
6. `f i i` is an isomorphism.
7. `t i i` is the identity.
8. `V i j ×[U i] V i k ⟶ V i j ⟶ V j i` factors through `V j k ×[U j] V j i ⟶ V j i` via some
    `t' : V i j ×[U i] V i k ⟶ V j k ×[U j] V j i`.
9. `t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _`.

We can then glue the spaces `U i` together by identifying `V i j` with `V j i`, such
that the `U i`'s are open subspaces of the glued space.
-/
@[nolint has_nonempty_instance]
structure GlueData extends GlueData LocallyRingedSpaceCat where
  f_open : ∀ i j, LocallyRingedSpaceCat.IsOpenImmersion (f i j)
#align
  algebraic_geometry.LocallyRingedSpace.glue_data AlgebraicGeometry.LocallyRingedSpaceCat.GlueData

attribute [instance] glue_data.f_open

namespace GlueData

variable (D : GlueData)

-- mathport name: «expr𝖣»
local notation "𝖣" => D.toGlueData

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The glue data of ringed spaces associated to a family of glue data of locally ringed spaces. -/")]
      []
      []
      []
      []
      [])
     (Command.abbrev
      "abbrev"
      (Command.declId `toSheafedSpaceGlueData [])
      (Command.optDeclSig
       []
       [(Term.typeSpec ":" (Term.app `SheafedSpaceCat.GlueData [`CommRingCat]))])
      (Command.declValSimple
       ":="
       (Term.structInst
        "{"
        []
        [(Term.structInstField (Term.structInstLVal `f_open []) ":=" (Term.proj `D "." `f_open))
         []
         (Term.structInstField
          (Term.structInstLVal `toGlueData [])
          ":="
          (Term.app
           (Term.proj
            (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
             "𝖣")
            "."
            `mapGlueData)
           [`forgetToSheafedSpace]))]
        (Term.optEllipsis [])
        []
        "}")
       [])
      []
      []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       []
       [(Term.structInstField (Term.structInstLVal `f_open []) ":=" (Term.proj `D "." `f_open))
        []
        (Term.structInstField
         (Term.structInstLVal `toGlueData [])
         ":="
         (Term.app
          (Term.proj
           (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
            "𝖣")
           "."
           `mapGlueData)
          [`forgetToSheafedSpace]))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
         "𝖣")
        "."
        `mapGlueData)
       [`forgetToSheafedSpace])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `forgetToSheafedSpace
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
        "𝖣")
       "."
       `mapGlueData)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
       "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»', expected 'AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.term𝖣._@.AlgebraicGeometry.PresheafedSpace.Gluing._hyg.398'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The glue data of ringed spaces associated to a family of glue data of locally ringed spaces. -/
  abbrev
    toSheafedSpaceGlueData
    : SheafedSpaceCat.GlueData CommRingCat
    := { f_open := D . f_open toGlueData := 𝖣 . mapGlueData forgetToSheafedSpace }
#align
  algebraic_geometry.LocallyRingedSpace.glue_data.to_SheafedSpace_glue_data AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.toSheafedSpaceGlueData

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The gluing as locally ringed spaces is isomorphic to the gluing as ringed spaces. -/")]
      []
      []
      []
      []
      [])
     (Command.abbrev
      "abbrev"
      (Command.declId `isoSheafedSpace [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (CategoryTheory.CategoryTheory.Isomorphism.«term_≅_»
          (Term.proj
           (Term.proj
            (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
             "𝖣")
            "."
            `glued)
           "."
           `toSheafedSpace)
          " ≅ "
          (Term.proj
           (Term.proj (Term.proj `D "." `toSheafedSpaceGlueData) "." `toGlueData)
           "."
           `glued)))])
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
          "𝖣")
         "."
         `gluedIso)
        [`forgetToSheafedSpace])
       [])
      []
      []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
         "𝖣")
        "."
        `gluedIso)
       [`forgetToSheafedSpace])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `forgetToSheafedSpace
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
        "𝖣")
       "."
       `gluedIso)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
       "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»', expected 'AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.term𝖣._@.AlgebraicGeometry.PresheafedSpace.Gluing._hyg.398'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.abbrev', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The gluing as locally ringed spaces is isomorphic to the gluing as ringed spaces. -/
  abbrev
    isoSheafedSpace
    : 𝖣 . glued . toSheafedSpace ≅ D . toSheafedSpaceGlueData . toGlueData . glued
    := 𝖣 . gluedIso forgetToSheafedSpace
#align
  algebraic_geometry.LocallyRingedSpace.glue_data.iso_SheafedSpace AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.isoSheafedSpace

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `ι_iso_SheafedSpace_inv [])
      (Command.declSig
       [(Term.explicitBinder "(" [`i] [":" (Term.proj `D "." `J)] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app
           (Term.proj (Term.proj (Term.proj `D "." `toSheafedSpaceGlueData) "." `toGlueData) "." `ι)
           [`i])
          " ≫ "
          (Term.proj (Term.proj `D "." `isoSheafedSpace) "." `inv))
         "="
         (Term.proj
          (Term.app
           (Term.proj
            (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
             "𝖣")
            "."
            `ι)
           [`i])
          "."
          (fieldIdx "1")))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
          "𝖣")
         "."
         `ι_glued_iso_inv)
        [`forgetToSheafedSpace `i])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
         "𝖣")
        "."
        `ι_glued_iso_inv)
       [`forgetToSheafedSpace `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `forgetToSheafedSpace
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
        "𝖣")
       "."
       `ι_glued_iso_inv)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
       "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»', expected 'AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.term𝖣._@.AlgebraicGeometry.PresheafedSpace.Gluing._hyg.398'
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
  ι_iso_SheafedSpace_inv
  ( i : D . J )
    : D . toSheafedSpaceGlueData . toGlueData . ι i ≫ D . isoSheafedSpace . inv = 𝖣 . ι i . 1
  := 𝖣 . ι_glued_iso_inv forgetToSheafedSpace i
#align
  algebraic_geometry.LocallyRingedSpace.glue_data.ι_iso_SheafedSpace_inv AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.ι_iso_SheafedSpace_inv

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `ι_is_open_immersion [])]
      (Command.declSig
       [(Term.explicitBinder "(" [`i] [":" (Term.proj `D "." `J)] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `IsOpenImmersion
         [(Term.app
           (Term.proj
            (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
             "𝖣")
            "."
            `ι)
           [`i])])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.delta "delta" [`is_open_immersion] [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `D.ι_iso_SheafedSpace_inv)]
             "]")
            [])
           []
           (Tactic.apply "apply" `PresheafedSpace.is_open_immersion.comp)])))
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
         [(Tactic.delta "delta" [`is_open_immersion] [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `D.ι_iso_SheafedSpace_inv)]
            "]")
           [])
          []
          (Tactic.apply "apply" `PresheafedSpace.is_open_immersion.comp)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `PresheafedSpace.is_open_immersion.comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `PresheafedSpace.is_open_immersion.comp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `D.ι_iso_SheafedSpace_inv)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `D.ι_iso_SheafedSpace_inv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.delta "delta" [`is_open_immersion] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `IsOpenImmersion
       [(Term.app
         (Term.proj
          (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
           "𝖣")
          "."
          `ι)
         [`i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
         "𝖣")
        "."
        `ι)
       [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
        "𝖣")
       "."
       `ι)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
       "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»', expected 'AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.term𝖣._@.AlgebraicGeometry.PresheafedSpace.Gluing._hyg.398'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  ι_is_open_immersion
  ( i : D . J ) : IsOpenImmersion 𝖣 . ι i
  :=
    by
      delta is_open_immersion
        rw [ ← D.ι_iso_SheafedSpace_inv ]
        apply PresheafedSpace.is_open_immersion.comp
#align
  algebraic_geometry.LocallyRingedSpace.glue_data.ι_is_open_immersion AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.ι_is_open_immersion

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       [(Term.explicitBinder "(" [`i `j `k] [":" (Term.proj `D "." `J)] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `PreservesLimit
         [(Term.app
           `cospan
           [(Term.app
             (Term.proj
              (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
               "𝖣")
              "."
              `f)
             [`i `j])
            (Term.app
             (Term.proj
              (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
               "𝖣")
              "."
              `f)
             [`i `k])])
          `forgetToSheafedSpace])))
      (Command.declValSimple ":=" `inferInstance [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inferInstance
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `PreservesLimit
       [(Term.app
         `cospan
         [(Term.app
           (Term.proj
            (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
             "𝖣")
            "."
            `f)
           [`i `j])
          (Term.app
           (Term.proj
            (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
             "𝖣")
            "."
            `f)
           [`i `k])])
        `forgetToSheafedSpace])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `forgetToSheafedSpace
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `cospan
       [(Term.app
         (Term.proj
          (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
           "𝖣")
          "."
          `f)
         [`i `j])
        (Term.app
         (Term.proj
          (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
           "𝖣")
          "."
          `f)
         [`i `k])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
         "𝖣")
        "."
        `f)
       [`i `k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
        "𝖣")
       "."
       `f)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
       "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»', expected 'AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.term𝖣._@.AlgebraicGeometry.PresheafedSpace.Gluing._hyg.398'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  ( i j k : D . J ) : PreservesLimit cospan 𝖣 . f i j 𝖣 . f i k forgetToSheafedSpace
  := inferInstance

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `ι_jointly_surjective [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`x]
         [":"
          (Term.proj
           (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
            "𝖣")
           "."
           `glued)]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders
          [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i)] ":" (Term.proj `D "." `J) ")")
           (Lean.bracketedExplicitBinders
            "("
            [(Lean.binderIdent `y)]
            ":"
            (Term.app (Term.proj `D "." `U) [`i])
            ")")])
         ","
         («term_=_»
          (Term.app
           (Term.proj
            (Term.proj
             (Term.app
              (Term.proj
               (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
                "𝖣")
               "."
               `ι)
              [`i])
             "."
             (fieldIdx "1"))
            "."
            `base)
           [`y])
          "="
          `x))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
          "𝖣")
         "."
         `ι_jointly_surjective)
        [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
          (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
           `LocallyRingedSpace.forget_to_SheafedSpace
           " ⋙ "
           (Term.app `SheafedSpaceCat.forget [(Term.hole "_")]))
          " ⋙ "
          (Term.app `forget [`TopCat]))
         `x])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
         "𝖣")
        "."
        `ι_jointly_surjective)
       [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
         (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
          `LocallyRingedSpace.forget_to_SheafedSpace
          " ⋙ "
          (Term.app `SheafedSpaceCat.forget [(Term.hole "_")]))
         " ⋙ "
         (Term.app `forget [`TopCat]))
        `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
       (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
        `LocallyRingedSpace.forget_to_SheafedSpace
        " ⋙ "
        (Term.app `SheafedSpaceCat.forget [(Term.hole "_")]))
       " ⋙ "
       (Term.app `forget [`TopCat]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `forget [`TopCat])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `TopCat
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `forget
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
       `LocallyRingedSpace.forget_to_SheafedSpace
       " ⋙ "
       (Term.app `SheafedSpaceCat.forget [(Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `SheafedSpaceCat.forget [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `SheafedSpaceCat.forget
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `LocallyRingedSpace.forget_to_SheafedSpace
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 80, (some 80, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
      `LocallyRingedSpace.forget_to_SheafedSpace
      " ⋙ "
      (Term.app `SheafedSpaceCat.forget [(Term.hole "_")]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
      (Term.paren
       "("
       (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
        `LocallyRingedSpace.forget_to_SheafedSpace
        " ⋙ "
        (Term.app `SheafedSpaceCat.forget [(Term.hole "_")]))
       ")")
      " ⋙ "
      (Term.app `forget [`TopCat]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
        "𝖣")
       "."
       `ι_jointly_surjective)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
       "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»', expected 'AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.term𝖣._@.AlgebraicGeometry.PresheafedSpace.Gluing._hyg.398'
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
  ι_jointly_surjective
  ( x : 𝖣 . glued ) : ∃ ( i : D . J ) ( y : D . U i ) , 𝖣 . ι i . 1 . base y = x
  :=
    𝖣 . ι_jointly_surjective
      LocallyRingedSpace.forget_to_SheafedSpace ⋙ SheafedSpaceCat.forget _ ⋙ forget TopCat x
#align
  algebraic_geometry.LocallyRingedSpace.glue_data.ι_jointly_surjective AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.ι_jointly_surjective

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The following diagram is a pullback, i.e. `Vᵢⱼ` is the intersection of `Uᵢ` and `Uⱼ` in `X`.\n\nVᵢⱼ ⟶ Uᵢ\n |      |\n ↓      ↓\n Uⱼ ⟶ X\n-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `vPullbackConeIsLimit [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`i `j] [":" (Term.proj `D "." `J)] [] ")")]
       [(Term.typeSpec
         ":"
         (Term.app
          `IsLimit
          [(Term.app
            (Term.proj
             (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
              "𝖣")
             "."
             `vPullbackCone)
            [`i `j])]))])
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
          "𝖣")
         "."
         `vPullbackConeIsLimitOfMap)
        [`forgetToSheafedSpace
         `i
         `j
         (Term.app
          (Term.proj (Term.proj `D "." `toSheafedSpaceGlueData) "." `vPullbackConeIsLimit)
          [(Term.hole "_") (Term.hole "_")])])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
         "𝖣")
        "."
        `vPullbackConeIsLimitOfMap)
       [`forgetToSheafedSpace
        `i
        `j
        (Term.app
         (Term.proj (Term.proj `D "." `toSheafedSpaceGlueData) "." `vPullbackConeIsLimit)
         [(Term.hole "_") (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.proj `D "." `toSheafedSpaceGlueData) "." `vPullbackConeIsLimit)
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
      (Term.proj (Term.proj `D "." `toSheafedSpaceGlueData) "." `vPullbackConeIsLimit)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `D "." `toSheafedSpaceGlueData)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `D
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.proj `D "." `toSheafedSpaceGlueData) "." `vPullbackConeIsLimit)
      [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `forgetToSheafedSpace
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
        "𝖣")
       "."
       `vPullbackConeIsLimitOfMap)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»
       "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.«term𝖣»', expected 'AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.AlgebraicGeometry.PresheafedSpace.Gluing.term𝖣._@.AlgebraicGeometry.PresheafedSpace.Gluing._hyg.398'
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
    The following diagram is a pullback, i.e. `Vᵢⱼ` is the intersection of `Uᵢ` and `Uⱼ` in `X`.
    
    Vᵢⱼ ⟶ Uᵢ
     |      |
     ↓      ↓
     Uⱼ ⟶ X
    -/
  def
    vPullbackConeIsLimit
    ( i j : D . J ) : IsLimit 𝖣 . vPullbackCone i j
    :=
      𝖣 . vPullbackConeIsLimitOfMap
        forgetToSheafedSpace i j D . toSheafedSpaceGlueData . vPullbackConeIsLimit _ _
#align
  algebraic_geometry.LocallyRingedSpace.glue_data.V_pullback_cone_is_limit AlgebraicGeometry.LocallyRingedSpaceCat.GlueData.vPullbackConeIsLimit

end GlueData

end LocallyRingedSpaceCat

end AlgebraicGeometry

