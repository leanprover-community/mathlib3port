/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module algebraic_geometry.gluing
! leanprover-community/mathlib commit 6d0adfa76594f304b4650d098273d4366edeb61b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicGeometry.PresheafedSpace.Gluing

/-!
# Gluing Schemes

Given a family of gluing data of schemes, we may glue them together.

## Main definitions

* `algebraic_geometry.Scheme.glue_data`: A structure containing the family of gluing data.
* `algebraic_geometry.Scheme.glue_data.glued`: The glued scheme.
    This is defined as the multicoequalizer of `∐ V i j ⇉ ∐ U i`, so that the general colimit API
    can be used.
* `algebraic_geometry.Scheme.glue_data.ι`: The immersion `ι i : U i ⟶ glued` for each `i : J`.
* `algebraic_geometry.Scheme.glue_data.iso_carrier`: The isomorphism between the underlying space
  of the glued scheme and the gluing of the underlying topological spaces.
* `algebraic_geometry.Scheme.open_cover.glue_data`: The glue data associated with an open cover.
* `algebraic_geometry.Scheme.open_cover.from_glue_data`: The canonical morphism
  `𝒰.glue_data.glued ⟶ X`. This has an `is_iso` instance.
* `algebraic_geometry.Scheme.open_cover.glue_morphisms`: We may glue a family of compatible
  morphisms defined on an open cover of a scheme.

## Main results

* `algebraic_geometry.Scheme.glue_data.ι_is_open_immersion`: The map `ι i : U i ⟶ glued`
  is an open immersion for each `i : J`.
* `algebraic_geometry.Scheme.glue_data.ι_jointly_surjective` : The underlying maps of
  `ι i : U i ⟶ glued` are jointly surjective.
* `algebraic_geometry.Scheme.glue_data.V_pullback_cone_is_limit` : `V i j` is the pullback
  (intersection) of `U i` and `U j` over the glued space.
* `algebraic_geometry.Scheme.glue_data.ι_eq_iff_rel` : `ι i x = ι j y` if and only if they coincide
  when restricted to `V i i`.
* `algebraic_geometry.Scheme.glue_data.is_open_iff` : An subset of the glued scheme is open iff
  all its preimages in `U i` are open.

## Implementation details

All the hard work is done in `algebraic_geometry/presheafed_space/gluing.lean` where we glue
presheafed spaces, sheafed spaces, and locally ringed spaces.

-/


noncomputable section

universe u

open TopologicalSpace CategoryTheory Opposite

open CategoryTheory.Limits AlgebraicGeometry.PresheafedSpaceCat

open CategoryTheory.GlueData

namespace AlgebraicGeometry

namespace SchemeCat

/-- A family of gluing data consists of
1. An index type `J`
2. An scheme `U i` for each `i : J`.
3. An scheme `V i j` for each `i j : J`.
  (Note that this is `J × J → Scheme` rather than `J → J → Scheme` to connect to the
  limits library easier.)
4. An open immersion `f i j : V i j ⟶ U i` for each `i j : ι`.
5. A transition map `t i j : V i j ⟶ V j i` for each `i j : ι`.
such that
6. `f i i` is an isomorphism.
7. `t i i` is the identity.
8. `V i j ×[U i] V i k ⟶ V i j ⟶ V j i` factors through `V j k ×[U j] V j i ⟶ V j i` via some
    `t' : V i j ×[U i] V i k ⟶ V j k ×[U j] V j i`.
9. `t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _`.

We can then glue the schemes `U i` together by identifying `V i j` with `V j i`, such
that the `U i`'s are open subschemes of the glued space.
-/
@[nolint has_nonempty_instance]
structure GlueData extends CategoryTheory.GlueData SchemeCat where
  f_open : ∀ i j, IsOpenImmersion (f i j)
#align algebraic_geometry.Scheme.glue_data AlgebraicGeometry.SchemeCat.GlueData

attribute [instance] glue_data.f_open

namespace GlueData

variable (D : GlueData)

include D

-- mathport name: «expr𝖣»
local notation "𝖣" => D.toGlueData

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The glue data of locally ringed spaces spaces associated to a family of glue data of schemes. -/")]
      []
      []
      []
      []
      [])
     (Command.abbrev
      "abbrev"
      (Command.declId `toLocallyRingedSpaceGlueData [])
      (Command.optDeclSig [] [(Term.typeSpec ":" `LocallyRingedSpaceCat.GlueData)])
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
            (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
            "."
            `mapGlueData)
           [`forgetToLocallyRingedSpace]))]
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
           (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
           "."
           `mapGlueData)
          [`forgetToLocallyRingedSpace]))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
        "."
        `mapGlueData)
       [`forgetToLocallyRingedSpace])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `forgetToLocallyRingedSpace
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
       "."
       `mapGlueData)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣»', expected 'AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.term𝖣._@.AlgebraicGeometry.Gluing._hyg.11'
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
/-- The glue data of locally ringed spaces spaces associated to a family of glue data of schemes. -/
  abbrev
    toLocallyRingedSpaceGlueData
    : LocallyRingedSpaceCat.GlueData
    := { f_open := D . f_open toGlueData := 𝖣 . mapGlueData forgetToLocallyRingedSpace }
#align
  algebraic_geometry.Scheme.glue_data.to_LocallyRingedSpace_glue_data AlgebraicGeometry.SchemeCat.GlueData.toLocallyRingedSpaceGlueData

/-- (Implementation). The glued scheme of a glue data.
This should not be used outside this file. Use `Scheme.glue_data.glued` instead. -/
def gluedScheme : SchemeCat :=
  by
  apply
    LocallyRingedSpace.is_open_immersion.Scheme D.to_LocallyRingedSpace_glue_data.to_glue_data.glued
  intro x
  obtain ⟨i, y, rfl⟩ := D.to_LocallyRingedSpace_glue_data.ι_jointly_surjective x
  refine' ⟨_, _ ≫ D.to_LocallyRingedSpace_glue_data.to_glue_data.ι i, _⟩
  swap; exact (D.U i).affineCover.map y
  constructor
  · dsimp [-Set.mem_range]
    rw [coe_comp, Set.range_comp]
    refine' Set.mem_image_of_mem _ _
    exact (D.U i).affineCover.Covers y
  · infer_instance
#align
  algebraic_geometry.Scheme.glue_data.glued_Scheme AlgebraicGeometry.SchemeCat.GlueData.gluedScheme

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `CreatesColimit
         [(Term.proj
           (Term.proj
            (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
            "."
            `diagram)
           "."
           `multispan)
          `forgetToLocallyRingedSpace])))
      (Command.declValSimple
       ":="
       (Term.app
        `createsColimitOfFullyFaithfulOfIso
        [(Term.proj `D "." `gluedScheme)
         (Term.app
          `HasColimit.isoOfNatIso
          [(Term.proj
            (Term.app
             (Term.proj
              (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
              "."
              `diagramIso)
             [`forgetToLocallyRingedSpace])
            "."
            `symm)])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `createsColimitOfFullyFaithfulOfIso
       [(Term.proj `D "." `gluedScheme)
        (Term.app
         `HasColimit.isoOfNatIso
         [(Term.proj
           (Term.app
            (Term.proj
             (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
             "."
             `diagramIso)
            [`forgetToLocallyRingedSpace])
           "."
           `symm)])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `HasColimit.isoOfNatIso
       [(Term.proj
         (Term.app
          (Term.proj
           (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
           "."
           `diagramIso)
          [`forgetToLocallyRingedSpace])
         "."
         `symm)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        (Term.proj
         (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
         "."
         `diagramIso)
        [`forgetToLocallyRingedSpace])
       "."
       `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
        "."
        `diagramIso)
       [`forgetToLocallyRingedSpace])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `forgetToLocallyRingedSpace
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
       "."
       `diagramIso)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣»', expected 'AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.term𝖣._@.AlgebraicGeometry.Gluing._hyg.11'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  : CreatesColimit 𝖣 . diagram . multispan forgetToLocallyRingedSpace
  :=
    createsColimitOfFullyFaithfulOfIso
      D . gluedScheme HasColimit.isoOfNatIso 𝖣 . diagramIso forgetToLocallyRingedSpace . symm

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `PreservesColimit
         [(Term.proj
           (Term.proj
            (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
            "."
            `diagram)
           "."
           `multispan)
          `forgetToTop])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.delta "delta" [`forget_to_Top `LocallyRingedSpace.forget_to_Top] [])
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
         [(Tactic.delta "delta" [`forget_to_Top `LocallyRingedSpace.forget_to_Top] [])
          []
          (Tactic.tacticInfer_instance "infer_instance")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticInfer_instance "infer_instance")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.delta "delta" [`forget_to_Top `LocallyRingedSpace.forget_to_Top] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `PreservesColimit
       [(Term.proj
         (Term.proj
          (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
          "."
          `diagram)
         "."
         `multispan)
        `forgetToTop])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `forgetToTop
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.proj
        (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
        "."
        `diagram)
       "."
       `multispan)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
       "."
       `diagram)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣»', expected 'AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.term𝖣._@.AlgebraicGeometry.Gluing._hyg.11'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  : PreservesColimit 𝖣 . diagram . multispan forgetToTop
  := by delta forget_to_Top LocallyRingedSpace.forget_to_Top infer_instance

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `HasMulticoequalizer
         [(Term.proj
           (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
           "."
           `diagram)])))
      (Command.declValSimple
       ":="
       (Term.app `hasColimitOfCreated [(Term.hole "_") `forgetToLocallyRingedSpace])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hasColimitOfCreated [(Term.hole "_") `forgetToLocallyRingedSpace])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `forgetToLocallyRingedSpace
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hasColimitOfCreated
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `HasMulticoequalizer
       [(Term.proj
         (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
         "."
         `diagram)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
       "."
       `diagram)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣»', expected 'AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.term𝖣._@.AlgebraicGeometry.Gluing._hyg.11'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance : HasMulticoequalizer 𝖣 . diagram := hasColimitOfCreated _ forgetToLocallyRingedSpace

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "The glued scheme of a glued space. -/")]
      []
      []
      []
      []
      [])
     (Command.abbrev
      "abbrev"
      (Command.declId `glued [])
      (Command.optDeclSig [] [(Term.typeSpec ":" `SchemeCat)])
      (Command.declValSimple
       ":="
       (Term.proj
        (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
        "."
        `glued)
       [])
      []
      []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
       "."
       `glued)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣»', expected 'AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.term𝖣._@.AlgebraicGeometry.Gluing._hyg.11'
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
/-- The glued scheme of a glued space. -/ abbrev glued : SchemeCat := 𝖣 . glued
#align algebraic_geometry.Scheme.glue_data.glued AlgebraicGeometry.SchemeCat.GlueData.glued

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "The immersion from `D.U i` into the glued space. -/")]
      []
      []
      []
      []
      [])
     (Command.abbrev
      "abbrev"
      (Command.declId `ι [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`i] [":" (Term.proj `D "." `J)] [] ")")]
       [(Term.typeSpec
         ":"
         (Combinatorics.Quiver.Basic.«term_⟶_»
          (Term.app (Term.proj `D "." `U) [`i])
          " ⟶ "
          (Term.proj `D "." `glued)))])
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
         "."
         `ι)
        [`i])
       [])
      []
      []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
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
      (Term.proj (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣") "." `ι)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣»', expected 'AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.term𝖣._@.AlgebraicGeometry.Gluing._hyg.11'
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
/-- The immersion from `D.U i` into the glued space. -/
  abbrev ι ( i : D . J ) : D . U i ⟶ D . glued := 𝖣 . ι i
#align algebraic_geometry.Scheme.glue_data.ι AlgebraicGeometry.SchemeCat.GlueData.ι

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
      (Command.declId `isoLocallyRingedSpace [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (CategoryTheory.CategoryTheory.Isomorphism.«term_≅_»
          (Term.proj (Term.proj `D "." `glued) "." `toLocallyRingedSpace)
          " ≅ "
          (Term.proj
           (Term.proj (Term.proj `D "." `toLocallyRingedSpaceGlueData) "." `toGlueData)
           "."
           `glued)))])
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
         "."
         `gluedIso)
        [`forgetToLocallyRingedSpace])
       [])
      []
      []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
        "."
        `gluedIso)
       [`forgetToLocallyRingedSpace])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `forgetToLocallyRingedSpace
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
       "."
       `gluedIso)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣»', expected 'AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.term𝖣._@.AlgebraicGeometry.Gluing._hyg.11'
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
    isoLocallyRingedSpace
    : D . glued . toLocallyRingedSpace ≅ D . toLocallyRingedSpaceGlueData . toGlueData . glued
    := 𝖣 . gluedIso forgetToLocallyRingedSpace
#align
  algebraic_geometry.Scheme.glue_data.iso_LocallyRingedSpace AlgebraicGeometry.SchemeCat.GlueData.isoLocallyRingedSpace

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `ι_iso_LocallyRingedSpace_inv [])
      (Command.declSig
       [(Term.explicitBinder "(" [`i] [":" (Term.proj `D "." `J)] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app
           (Term.proj
            (Term.proj (Term.proj `D "." `toLocallyRingedSpaceGlueData) "." `toGlueData)
            "."
            `ι)
           [`i])
          " ≫ "
          (Term.proj (Term.proj `D "." `isoLocallyRingedSpace) "." `inv))
         "="
         (Term.app
          (Term.proj
           (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
           "."
           `ι)
          [`i]))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
         "."
         `ι_glued_iso_inv)
        [`forgetToLocallyRingedSpace `i])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
        "."
        `ι_glued_iso_inv)
       [`forgetToLocallyRingedSpace `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `forgetToLocallyRingedSpace
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
       "."
       `ι_glued_iso_inv)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣»', expected 'AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.term𝖣._@.AlgebraicGeometry.Gluing._hyg.11'
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
  ι_iso_LocallyRingedSpace_inv
  ( i : D . J )
    :
      D . toLocallyRingedSpaceGlueData . toGlueData . ι i ≫ D . isoLocallyRingedSpace . inv
        =
        𝖣 . ι i
  := 𝖣 . ι_glued_iso_inv forgetToLocallyRingedSpace i
#align
  algebraic_geometry.Scheme.glue_data.ι_iso_LocallyRingedSpace_inv AlgebraicGeometry.SchemeCat.GlueData.ι_iso_LocallyRingedSpace_inv

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
            (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
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
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `D.ι_iso_LocallyRingedSpace_inv)]
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
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `D.ι_iso_LocallyRingedSpace_inv)]
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
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `D.ι_iso_LocallyRingedSpace_inv)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `D.ι_iso_LocallyRingedSpace_inv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `IsOpenImmersion
       [(Term.app
         (Term.proj
          (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
          "."
          `ι)
         [`i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
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
      (Term.proj (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣") "." `ι)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣»', expected 'AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.term𝖣._@.AlgebraicGeometry.Gluing._hyg.11'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  ι_is_open_immersion
  ( i : D . J ) : IsOpenImmersion 𝖣 . ι i
  := by rw [ ← D.ι_iso_LocallyRingedSpace_inv ] infer_instance
#align
  algebraic_geometry.Scheme.glue_data.ι_is_open_immersion AlgebraicGeometry.SchemeCat.GlueData.ι_is_open_immersion

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
           (Term.proj
            (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
            "."
            `glued)
           "."
           `carrier)]
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
            (Term.proj (Term.app (Term.proj `D "." `U) [`i]) "." `carrier)
            ")")])
         ","
         («term_=_»
          (Term.app
           (Term.proj
            (Term.proj (Term.app (Term.proj `D "." `ι) [`i]) "." (fieldIdx "1"))
            "."
            `base)
           [`y])
          "="
          `x))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
         "."
         `ι_jointly_surjective)
        [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
          `forget_to_Top
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
        (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
        "."
        `ι_jointly_surjective)
       [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
         `forget_to_Top
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
       `forget_to_Top
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
      `forget_to_Top
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
      `forget_to_Top
      " ⋙ "
      (Term.app `forget [`TopCat]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
       "."
       `ι_jointly_surjective)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣»', expected 'AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.term𝖣._@.AlgebraicGeometry.Gluing._hyg.11'
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
  ( x : 𝖣 . glued . carrier ) : ∃ ( i : D . J ) ( y : D . U i . carrier ) , D . ι i . 1 . base y = x
  := 𝖣 . ι_jointly_surjective forget_to_Top ⋙ forget TopCat x
#align
  algebraic_geometry.Scheme.glue_data.ι_jointly_surjective AlgebraicGeometry.SchemeCat.GlueData.ι_jointly_surjective

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
          (Attr.simple `reassoc._@.AlgebraicGeometry.Gluing._hyg.1 []))]
        "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `glue_condition [])
      (Command.declSig
       [(Term.explicitBinder "(" [`i `j] [":" (Term.proj `D "." `J)] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app (Term.proj `D "." `t) [`i `j])
          " ≫ "
          (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
           (Term.app (Term.proj `D "." `f) [`j `i])
           " ≫ "
           (Term.app (Term.proj `D "." `ι) [`j])))
         "="
         (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
          (Term.app (Term.proj `D "." `f) [`i `j])
          " ≫ "
          (Term.app (Term.proj `D "." `ι) [`i])))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
         "."
         `glue_condition)
        [`i `j])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
        "."
        `glue_condition)
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
       (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
       "."
       `glue_condition)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣»', expected 'AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.term𝖣._@.AlgebraicGeometry.Gluing._hyg.11'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp , reassoc ]
  theorem
    glue_condition
    ( i j : D . J ) : D . t i j ≫ D . f j i ≫ D . ι j = D . f i j ≫ D . ι i
    := 𝖣 . glue_condition i j
#align
  algebraic_geometry.Scheme.glue_data.glue_condition AlgebraicGeometry.SchemeCat.GlueData.glue_condition

/-- The pullback cone spanned by `V i j ⟶ U i` and `V i j ⟶ U j`.
This is a pullback diagram (`V_pullback_cone_is_limit`). -/
def vPullbackCone (i j : D.J) : PullbackCone (D.ι i) (D.ι j) :=
  PullbackCone.mk (D.f i j) (D.t i j ≫ D.f j i) (by simp)
#align
  algebraic_geometry.Scheme.glue_data.V_pullback_cone AlgebraicGeometry.SchemeCat.GlueData.vPullbackCone

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
         (Term.app `IsLimit [(Term.app (Term.proj `D "." `vPullbackCone) [`i `j])]))])
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
         "."
         `vPullbackConeIsLimitOfMap)
        [`forgetToLocallyRingedSpace
         `i
         `j
         (Term.app
          (Term.proj (Term.proj `D "." `toLocallyRingedSpaceGlueData) "." `vPullbackConeIsLimit)
          [(Term.hole "_") (Term.hole "_")])])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
        "."
        `vPullbackConeIsLimitOfMap)
       [`forgetToLocallyRingedSpace
        `i
        `j
        (Term.app
         (Term.proj (Term.proj `D "." `toLocallyRingedSpaceGlueData) "." `vPullbackConeIsLimit)
         [(Term.hole "_") (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.proj `D "." `toLocallyRingedSpaceGlueData) "." `vPullbackConeIsLimit)
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
      (Term.proj (Term.proj `D "." `toLocallyRingedSpaceGlueData) "." `vPullbackConeIsLimit)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `D "." `toLocallyRingedSpaceGlueData)
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
      (Term.proj (Term.proj `D "." `toLocallyRingedSpaceGlueData) "." `vPullbackConeIsLimit)
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
      `forgetToLocallyRingedSpace
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
       "."
       `vPullbackConeIsLimitOfMap)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣»', expected 'AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.term𝖣._@.AlgebraicGeometry.Gluing._hyg.11'
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
    ( i j : D . J ) : IsLimit D . vPullbackCone i j
    :=
      𝖣 . vPullbackConeIsLimitOfMap
        forgetToLocallyRingedSpace i j D . toLocallyRingedSpaceGlueData . vPullbackConeIsLimit _ _
#align
  algebraic_geometry.Scheme.glue_data.V_pullback_cone_is_limit AlgebraicGeometry.SchemeCat.GlueData.vPullbackConeIsLimit

/-- The underlying topological space of the glued scheme is isomorphic to the gluing of the
underlying spacess -/
def isoCarrier :
    D.glued.carrier ≅
      D.toLocallyRingedSpaceGlueData.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toTopGlueData.toGlueData.glued :=
  by
  refine' (PresheafedSpace.forget _).mapIso _ ≪≫ glue_data.glued_iso _ (PresheafedSpace.forget _)
  refine'
    SheafedSpace.forget_to_PresheafedSpace.map_iso _ ≪≫ SheafedSpace.glue_data.iso_PresheafedSpace _
  refine'
    LocallyRingedSpace.forget_to_SheafedSpace.map_iso _ ≪≫
      LocallyRingedSpace.glue_data.iso_SheafedSpace _
  exact Scheme.glue_data.iso_LocallyRingedSpace _
#align
  algebraic_geometry.Scheme.glue_data.iso_carrier AlgebraicGeometry.SchemeCat.GlueData.isoCarrier

@[simp]
theorem ι_iso_carrier_inv (i : D.J) :
    D.toLocallyRingedSpaceGlueData.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toTopGlueData.toGlueData.ι
          i ≫
        D.isoCarrier.inv =
      (D.ι i).1.base :=
  by
  delta iso_carrier
  simp only [functor.map_iso_inv, iso.trans_inv, iso.trans_assoc, glue_data.ι_glued_iso_inv_assoc,
    functor.map_iso_trans, category.assoc]
  iterate 3 erw [← comp_base]
  simp_rw [← category.assoc]
  rw [D.to_LocallyRingedSpace_glue_data.to_SheafedSpace_glue_data.ι_iso_PresheafedSpace_inv i]
  erw [D.to_LocallyRingedSpace_glue_data.ι_iso_SheafedSpace_inv i]
  change (_ ≫ D.iso_LocallyRingedSpace.inv).1.base = _
  rw [D.ι_iso_LocallyRingedSpace_inv i]
#align
  algebraic_geometry.Scheme.glue_data.ι_iso_carrier_inv AlgebraicGeometry.SchemeCat.GlueData.ι_iso_carrier_inv

/-- An equivalence relation on `Σ i, D.U i` that holds iff `𝖣 .ι i x = 𝖣 .ι j y`.
See `Scheme.gluing_data.ι_eq_iff`. -/
def Rel (a b : Σi, ((D.U i).carrier : Type _)) : Prop :=
  a = b ∨
    ∃ x : (D.V (a.1, b.1)).carrier, (D.f _ _).1.base x = a.2 ∧ (D.t _ _ ≫ D.f _ _).1.base x = b.2
#align algebraic_geometry.Scheme.glue_data.rel AlgebraicGeometry.SchemeCat.GlueData.Rel

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `ι_eq_iff [])
      (Command.declSig
       [(Term.explicitBinder "(" [`i `j] [":" (Term.proj `D "." `J)] [] ")")
        (Term.explicitBinder
         "("
         [`x]
         [":" (Term.proj (Term.app (Term.proj `D "." `U) [`i]) "." `carrier)]
         []
         ")")
        (Term.explicitBinder
         "("
         [`y]
         [":" (Term.proj (Term.app (Term.proj `D "." `U) [`j]) "." `carrier)]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_=_»
          (Term.app
           (Term.proj
            (Term.proj
             (Term.app
              (Term.proj
               (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
               "."
               `ι)
              [`i])
             "."
             (fieldIdx "1"))
            "."
            `base)
           [`x])
          "="
          (Term.app
           (Term.proj
            (Term.proj
             (Term.app
              (Term.proj
               (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
               "."
               `ι)
              [`j])
             "."
             (fieldIdx "1"))
            "."
            `base)
           [`y]))
         "↔"
         (Term.app
          (Term.proj `D "." `Rel)
          [(Term.anonymousCtor "⟨" [`i "," `x] "⟩") (Term.anonymousCtor "⟨" [`j "," `y] "⟩")]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.app
             `Iff.trans
             [(Term.hole "_")
              (Term.app
               (Term.proj
                (Term.proj
                 (Term.proj
                  `D.to_LocallyRingedSpace_glue_data.to_SheafedSpace_glue_data
                  "."
                  `toPresheafedSpaceGlueData)
                 "."
                 `toTopGlueData)
                "."
                `ι_eq_iff_rel)
               [`i `j `x `y])]))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.proj
                (Term.app
                 (Term.proj (Term.app `TopCat.mono_iff_injective [`D.iso_carrier.inv]) "." `mp)
                 [`inferInstance])
                "."
                `eq_iff))]
             "]")
            [])
           []
           (Mathlib.Tactic.tacticSimp_rw__
            "simp_rw"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `comp_apply)
              ","
              (Tactic.rwRule [] `D.ι_iso_carrier_inv)]
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
         [(Tactic.refine'
           "refine'"
           (Term.app
            `Iff.trans
            [(Term.hole "_")
             (Term.app
              (Term.proj
               (Term.proj
                (Term.proj
                 `D.to_LocallyRingedSpace_glue_data.to_SheafedSpace_glue_data
                 "."
                 `toPresheafedSpaceGlueData)
                "."
                `toTopGlueData)
               "."
               `ι_eq_iff_rel)
              [`i `j `x `y])]))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.proj
               (Term.app
                (Term.proj (Term.app `TopCat.mono_iff_injective [`D.iso_carrier.inv]) "." `mp)
                [`inferInstance])
               "."
               `eq_iff))]
            "]")
           [])
          []
          (Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `comp_apply)
             ","
             (Tactic.rwRule [] `D.ι_iso_carrier_inv)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `comp_apply)
         ","
         (Tactic.rwRule [] `D.ι_iso_carrier_inv)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `D.ι_iso_carrier_inv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `comp_apply
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
          (Term.proj
           (Term.app
            (Term.proj (Term.app `TopCat.mono_iff_injective [`D.iso_carrier.inv]) "." `mp)
            [`inferInstance])
           "."
           `eq_iff))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        (Term.proj (Term.app `TopCat.mono_iff_injective [`D.iso_carrier.inv]) "." `mp)
        [`inferInstance])
       "."
       `eq_iff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj (Term.app `TopCat.mono_iff_injective [`D.iso_carrier.inv]) "." `mp)
       [`inferInstance])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inferInstance
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `TopCat.mono_iff_injective [`D.iso_carrier.inv]) "." `mp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `TopCat.mono_iff_injective [`D.iso_carrier.inv])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `D.iso_carrier.inv
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `TopCat.mono_iff_injective
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `TopCat.mono_iff_injective [`D.iso_carrier.inv])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj
       (Term.paren "(" (Term.app `TopCat.mono_iff_injective [`D.iso_carrier.inv]) ")")
       "."
       `mp)
      [`inferInstance])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `Iff.trans
        [(Term.hole "_")
         (Term.app
          (Term.proj
           (Term.proj
            (Term.proj
             `D.to_LocallyRingedSpace_glue_data.to_SheafedSpace_glue_data
             "."
             `toPresheafedSpaceGlueData)
            "."
            `toTopGlueData)
           "."
           `ι_eq_iff_rel)
          [`i `j `x `y])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Iff.trans
       [(Term.hole "_")
        (Term.app
         (Term.proj
          (Term.proj
           (Term.proj
            `D.to_LocallyRingedSpace_glue_data.to_SheafedSpace_glue_data
            "."
            `toPresheafedSpaceGlueData)
           "."
           `toTopGlueData)
          "."
          `ι_eq_iff_rel)
         [`i `j `x `y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.proj
         (Term.proj
          `D.to_LocallyRingedSpace_glue_data.to_SheafedSpace_glue_data
          "."
          `toPresheafedSpaceGlueData)
         "."
         `toTopGlueData)
        "."
        `ι_eq_iff_rel)
       [`i `j `x `y])
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
      (Term.proj
       (Term.proj
        (Term.proj
         `D.to_LocallyRingedSpace_glue_data.to_SheafedSpace_glue_data
         "."
         `toPresheafedSpaceGlueData)
        "."
        `toTopGlueData)
       "."
       `ι_eq_iff_rel)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.proj
        `D.to_LocallyRingedSpace_glue_data.to_SheafedSpace_glue_data
        "."
        `toPresheafedSpaceGlueData)
       "."
       `toTopGlueData)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       `D.to_LocallyRingedSpace_glue_data.to_SheafedSpace_glue_data
       "."
       `toPresheafedSpaceGlueData)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `D.to_LocallyRingedSpace_glue_data.to_SheafedSpace_glue_data
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
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
         `D.to_LocallyRingedSpace_glue_data.to_SheafedSpace_glue_data
         "."
         `toPresheafedSpaceGlueData)
        "."
        `toTopGlueData)
       "."
       `ι_eq_iff_rel)
      [`i `j `x `y])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Iff.trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_=_»
        (Term.app
         (Term.proj
          (Term.proj
           (Term.app
            (Term.proj
             (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
             "."
             `ι)
            [`i])
           "."
           (fieldIdx "1"))
          "."
          `base)
         [`x])
        "="
        (Term.app
         (Term.proj
          (Term.proj
           (Term.app
            (Term.proj
             (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
             "."
             `ι)
            [`j])
           "."
           (fieldIdx "1"))
          "."
          `base)
         [`y]))
       "↔"
       (Term.app
        (Term.proj `D "." `Rel)
        [(Term.anonymousCtor "⟨" [`i "," `x] "⟩") (Term.anonymousCtor "⟨" [`j "," `y] "⟩")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `D "." `Rel)
       [(Term.anonymousCtor "⟨" [`i "," `x] "⟩") (Term.anonymousCtor "⟨" [`j "," `y] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`j "," `y] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.anonymousCtor "⟨" [`i "," `x] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `D "." `Rel)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `D
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      («term_=_»
       (Term.app
        (Term.proj
         (Term.proj
          (Term.app
           (Term.proj
            (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
            "."
            `ι)
           [`i])
          "."
          (fieldIdx "1"))
         "."
         `base)
        [`x])
       "="
       (Term.app
        (Term.proj
         (Term.proj
          (Term.app
           (Term.proj
            (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
            "."
            `ι)
           [`j])
          "."
          (fieldIdx "1"))
         "."
         `base)
        [`y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.proj
         (Term.app
          (Term.proj
           (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
           "."
           `ι)
          [`j])
         "."
         (fieldIdx "1"))
        "."
        `base)
       [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.proj
        (Term.app
         (Term.proj
          (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
          "."
          `ι)
         [`j])
        "."
        (fieldIdx "1"))
       "."
       `base)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.app
        (Term.proj
         (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
         "."
         `ι)
        [`j])
       "."
       (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj
        (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
        "."
        `ι)
       [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣") "." `ι)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣» "𝖣")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.«term𝖣»', expected 'AlgebraicGeometry.SchemeCat.GlueData.AlgebraicGeometry.Gluing.term𝖣._@.AlgebraicGeometry.Gluing._hyg.11'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  ι_eq_iff
  ( i j : D . J ) ( x : D . U i . carrier ) ( y : D . U j . carrier )
    : 𝖣 . ι i . 1 . base x = 𝖣 . ι j . 1 . base y ↔ D . Rel ⟨ i , x ⟩ ⟨ j , y ⟩
  :=
    by
      refine'
          Iff.trans
            _
              D.to_LocallyRingedSpace_glue_data.to_SheafedSpace_glue_data
                      .
                      toPresheafedSpaceGlueData
                    .
                    toTopGlueData
                  .
                  ι_eq_iff_rel
                i j x y
        rw [ ← TopCat.mono_iff_injective D.iso_carrier.inv . mp inferInstance . eq_iff ]
        simp_rw [ ← comp_apply , D.ι_iso_carrier_inv ]
#align algebraic_geometry.Scheme.glue_data.ι_eq_iff AlgebraicGeometry.SchemeCat.GlueData.ι_eq_iff

theorem is_open_iff (U : Set D.glued.carrier) : IsOpen U ↔ ∀ i, IsOpen ((D.ι i).1.base ⁻¹' U) :=
  by
  rw [← (TopCat.homeoOfIso D.iso_carrier.symm).is_open_preimage]
  rw [TopCat.GlueData.is_open_iff]
  apply forall_congr'
  intro i
  erw [← Set.preimage_comp, ← coe_comp, ι_iso_carrier_inv]
#align
  algebraic_geometry.Scheme.glue_data.is_open_iff AlgebraicGeometry.SchemeCat.GlueData.is_open_iff

/-- The open cover of the glued space given by the glue data. -/
def openCover (D : SchemeCat.GlueData) : OpenCover D.glued
    where
  J := D.J
  obj := D.U
  map := D.ι
  f x := (D.ι_jointly_surjective x).some
  Covers x := ⟨_, (D.ι_jointly_surjective x).some_spec.some_spec⟩
#align algebraic_geometry.Scheme.glue_data.open_cover AlgebraicGeometry.SchemeCat.GlueData.openCover

end GlueData

namespace OpenCover

variable {X : SchemeCat.{u}} (𝒰 : OpenCover.{u} X)

/-- (Implementation) the transition maps in the glue data associated with an open cover. -/
def gluedCoverT' (x y z : 𝒰.J) :
    pullback (pullback.fst : pullback (𝒰.map x) (𝒰.map y) ⟶ _)
        (pullback.fst : pullback (𝒰.map x) (𝒰.map z) ⟶ _) ⟶
      pullback (pullback.fst : pullback (𝒰.map y) (𝒰.map z) ⟶ _)
        (pullback.fst : pullback (𝒰.map y) (𝒰.map x) ⟶ _) :=
  by
  refine' (pullback_right_pullback_fst_iso _ _ _).Hom ≫ _
  refine' _ ≫ (pullback_symmetry _ _).Hom
  refine' _ ≫ (pullback_right_pullback_fst_iso _ _ _).inv
  refine' pullback.map _ _ _ _ (pullback_symmetry _ _).Hom (𝟙 _) (𝟙 _) _ _
  · simp [pullback.condition]
  · simp
#align
  algebraic_geometry.Scheme.open_cover.glued_cover_t' AlgebraicGeometry.SchemeCat.OpenCover.gluedCoverT'

@[simp, reassoc.1]
theorem glued_cover_t'_fst_fst (x y z : 𝒰.J) :
    𝒰.gluedCoverT' x y z ≫ pullback.fst ≫ pullback.fst = pullback.fst ≫ pullback.snd :=
  by
  delta glued_cover_t'
  simp
#align
  algebraic_geometry.Scheme.open_cover.glued_cover_t'_fst_fst AlgebraicGeometry.SchemeCat.OpenCover.glued_cover_t'_fst_fst

@[simp, reassoc.1]
theorem glued_cover_t'_fst_snd (x y z : 𝒰.J) :
    gluedCoverT' 𝒰 x y z ≫ pullback.fst ≫ pullback.snd = pullback.snd ≫ pullback.snd :=
  by
  delta glued_cover_t'
  simp
#align
  algebraic_geometry.Scheme.open_cover.glued_cover_t'_fst_snd AlgebraicGeometry.SchemeCat.OpenCover.glued_cover_t'_fst_snd

@[simp, reassoc.1]
theorem glued_cover_t'_snd_fst (x y z : 𝒰.J) :
    gluedCoverT' 𝒰 x y z ≫ pullback.snd ≫ pullback.fst = pullback.fst ≫ pullback.snd :=
  by
  delta glued_cover_t'
  simp
#align
  algebraic_geometry.Scheme.open_cover.glued_cover_t'_snd_fst AlgebraicGeometry.SchemeCat.OpenCover.glued_cover_t'_snd_fst

@[simp, reassoc.1]
theorem glued_cover_t'_snd_snd (x y z : 𝒰.J) :
    gluedCoverT' 𝒰 x y z ≫ pullback.snd ≫ pullback.snd = pullback.fst ≫ pullback.fst :=
  by
  delta glued_cover_t'
  simp
#align
  algebraic_geometry.Scheme.open_cover.glued_cover_t'_snd_snd AlgebraicGeometry.SchemeCat.OpenCover.glued_cover_t'_snd_snd

theorem glued_cover_cocycle_fst (x y z : 𝒰.J) :
    gluedCoverT' 𝒰 x y z ≫ gluedCoverT' 𝒰 y z x ≫ gluedCoverT' 𝒰 z x y ≫ pullback.fst =
      pullback.fst :=
  by apply pullback.hom_ext <;> simp
#align
  algebraic_geometry.Scheme.open_cover.glued_cover_cocycle_fst AlgebraicGeometry.SchemeCat.OpenCover.glued_cover_cocycle_fst

theorem glued_cover_cocycle_snd (x y z : 𝒰.J) :
    gluedCoverT' 𝒰 x y z ≫ gluedCoverT' 𝒰 y z x ≫ gluedCoverT' 𝒰 z x y ≫ pullback.snd =
      pullback.snd :=
  by apply pullback.hom_ext <;> simp [pullback.condition]
#align
  algebraic_geometry.Scheme.open_cover.glued_cover_cocycle_snd AlgebraicGeometry.SchemeCat.OpenCover.glued_cover_cocycle_snd

theorem glued_cover_cocycle (x y z : 𝒰.J) :
    gluedCoverT' 𝒰 x y z ≫ gluedCoverT' 𝒰 y z x ≫ gluedCoverT' 𝒰 z x y = 𝟙 _ :=
  by
  apply pullback.hom_ext <;> simp_rw [category.id_comp, category.assoc]
  apply glued_cover_cocycle_fst
  apply glued_cover_cocycle_snd
#align
  algebraic_geometry.Scheme.open_cover.glued_cover_cocycle AlgebraicGeometry.SchemeCat.OpenCover.glued_cover_cocycle

/-- The glue data associated with an open cover.
The canonical isomorphism `𝒰.glued_cover.glued ⟶ X` is provided by `𝒰.from_glued`. -/
@[simps]
def gluedCover : SchemeCat.GlueData.{u} where
  J := 𝒰.J
  U := 𝒰.obj
  V := fun ⟨x, y⟩ => pullback (𝒰.map x) (𝒰.map y)
  f x y := pullback.fst
  f_id x := inferInstance
  t x y := (pullbackSymmetry _ _).Hom
  t_id x := by simpa
  t' x y z := gluedCoverT' 𝒰 x y z
  t_fac x y z := by apply pullback.hom_ext <;> simp
  -- The `cocycle` field could have been `by tidy` but lean timeouts.
  cocycle x y z := glued_cover_cocycle 𝒰 x y z
  f_open x := inferInstance
#align
  algebraic_geometry.Scheme.open_cover.glued_cover AlgebraicGeometry.SchemeCat.OpenCover.gluedCover

/-- The canonical morphism from the gluing of an open cover of `X` into `X`.
This is an isomorphism, as witnessed by an `is_iso` instance. -/
def fromGlued : 𝒰.gluedCover.glued ⟶ X :=
  by
  fapply multicoequalizer.desc
  exact fun x => 𝒰.map x
  rintro ⟨x, y⟩
  change pullback.fst ≫ _ = ((pullback_symmetry _ _).Hom ≫ pullback.fst) ≫ _
  simpa using pullback.condition
#align
  algebraic_geometry.Scheme.open_cover.from_glued AlgebraicGeometry.SchemeCat.OpenCover.fromGlued

@[simp, reassoc.1]
theorem ι_from_glued (x : 𝒰.J) : 𝒰.gluedCover.ι x ≫ 𝒰.fromGlued = 𝒰.map x :=
  multicoequalizer.π_desc _ _ _ _ _
#align
  algebraic_geometry.Scheme.open_cover.ι_from_glued AlgebraicGeometry.SchemeCat.OpenCover.ι_from_glued

theorem from_glued_injective : Function.Injective 𝒰.fromGlued.1.base :=
  by
  intro x y h
  obtain ⟨i, x, rfl⟩ := 𝒰.glued_cover.ι_jointly_surjective x
  obtain ⟨j, y, rfl⟩ := 𝒰.glued_cover.ι_jointly_surjective y
  simp_rw [← comp_apply, ← SheafedSpace.comp_base, ← LocallyRingedSpace.comp_val] at h
  erw [ι_from_glued, ι_from_glued] at h
  let e :=
    (TopCat.pullbackConeIsLimit _ _).conePointUniqueUpToIso
      (is_limit_of_has_pullback_of_preserves_limit Scheme.forget_to_Top (𝒰.map i) (𝒰.map j))
  rw [𝒰.glued_cover.ι_eq_iff]
  right
  use e.hom ⟨⟨x, y⟩, h⟩
  simp_rw [← comp_apply]
  constructor
  · erw [is_limit.cone_point_unique_up_to_iso_hom_comp _ _ walking_cospan.left]
    rfl
  · erw [pullback_symmetry_hom_comp_fst,
      is_limit.cone_point_unique_up_to_iso_hom_comp _ _ walking_cospan.right]
    rfl
#align
  algebraic_geometry.Scheme.open_cover.from_glued_injective AlgebraicGeometry.SchemeCat.OpenCover.from_glued_injective

instance from_glued_stalk_iso (x : 𝒰.gluedCover.glued.carrier) :
    IsIso (PresheafedSpaceCat.stalkMap 𝒰.fromGlued.val x) :=
  by
  obtain ⟨i, x, rfl⟩ := 𝒰.glued_cover.ι_jointly_surjective x
  have :=
    PresheafedSpace.stalk_map.congr_hom _ _
      (congr_arg LocallyRingedSpace.hom.val <| 𝒰.ι_from_glued i) x
  erw [PresheafedSpace.stalk_map.comp] at this
  rw [← is_iso.eq_comp_inv] at this
  rw [this]
  infer_instance
#align
  algebraic_geometry.Scheme.open_cover.from_glued_stalk_iso AlgebraicGeometry.SchemeCat.OpenCover.from_glued_stalk_iso

theorem from_glued_open_map : IsOpenMap 𝒰.fromGlued.1.base :=
  by
  intro U hU
  rw [is_open_iff_forall_mem_open]
  intro x hx
  rw [𝒰.glued_cover.is_open_iff] at hU
  use 𝒰.from_glued.val.base '' U ∩ Set.range (𝒰.map (𝒰.f x)).1.base
  use Set.inter_subset_left _ _
  constructor
  · rw [← Set.image_preimage_eq_inter_range]
    apply show is_open_immersion (𝒰.map (𝒰.f x)) by infer_instance.base_open.IsOpenMap
    convert hU (𝒰.f x) using 1
    rw [← ι_from_glued]
    erw [coe_comp]
    rw [Set.preimage_comp]
    congr 1
    refine' Set.preimage_image_eq _ 𝒰.from_glued_injective
  · exact ⟨hx, 𝒰.covers x⟩
#align
  algebraic_geometry.Scheme.open_cover.from_glued_open_map AlgebraicGeometry.SchemeCat.OpenCover.from_glued_open_map

theorem from_glued_open_embedding : OpenEmbedding 𝒰.fromGlued.1.base :=
  open_embedding_of_continuous_injective_open (by continuity) 𝒰.from_glued_injective
    𝒰.from_glued_open_map
#align
  algebraic_geometry.Scheme.open_cover.from_glued_open_embedding AlgebraicGeometry.SchemeCat.OpenCover.from_glued_open_embedding

instance : Epi 𝒰.fromGlued.val.base :=
  by
  rw [TopCat.epi_iff_surjective]
  intro x
  obtain ⟨y, h⟩ := 𝒰.covers x
  use (𝒰.glued_cover.ι (𝒰.f x)).1.base y
  rw [← comp_apply]
  rw [← 𝒰.ι_from_glued (𝒰.f x)] at h
  exact h

instance from_glued_open_immersion : IsOpenImmersion 𝒰.fromGlued :=
  SheafedSpaceCat.IsOpenImmersion.of_stalk_iso _ 𝒰.from_glued_open_embedding
#align
  algebraic_geometry.Scheme.open_cover.from_glued_open_immersion AlgebraicGeometry.SchemeCat.OpenCover.from_glued_open_immersion

instance : IsIso 𝒰.fromGlued :=
  by
  apply
    is_iso_of_reflects_iso _
      (Scheme.forget_to_LocallyRingedSpace ⋙
        LocallyRingedSpace.forget_to_SheafedSpace ⋙ SheafedSpace.forget_to_PresheafedSpace)
  change @is_iso (PresheafedSpace _) _ _ _ 𝒰.from_glued.val
  apply PresheafedSpace.is_open_immersion.to_iso

/-- Given an open cover of `X`, and a morphism `𝒰.obj x ⟶ Y` for each open subscheme in the cover,
such that these morphisms are compatible in the intersection (pullback), we may glue the morphisms
together into a morphism `X ⟶ Y`.

Note:
If `X` is exactly (defeq to) the gluing of `U i`, then using `multicoequalizer.desc` suffices.
-/
def glueMorphisms {Y : SchemeCat} (f : ∀ x, 𝒰.obj x ⟶ Y)
    (hf : ∀ x y, (pullback.fst : pullback (𝒰.map x) (𝒰.map y) ⟶ _) ≫ f x = pullback.snd ≫ f y) :
    X ⟶ Y := by
  refine' inv 𝒰.from_glued ≫ _
  fapply multicoequalizer.desc
  exact f
  rintro ⟨i, j⟩
  change pullback.fst ≫ f i = (_ ≫ _) ≫ f j
  erw [pullback_symmetry_hom_comp_fst]
  exact hf i j
#align
  algebraic_geometry.Scheme.open_cover.glue_morphisms AlgebraicGeometry.SchemeCat.OpenCover.glueMorphisms

@[simp, reassoc.1]
theorem ι_glue_morphisms {Y : SchemeCat} (f : ∀ x, 𝒰.obj x ⟶ Y)
    (hf : ∀ x y, (pullback.fst : pullback (𝒰.map x) (𝒰.map y) ⟶ _) ≫ f x = pullback.snd ≫ f y)
    (x : 𝒰.J) : 𝒰.map x ≫ 𝒰.glueMorphisms f hf = f x :=
  by
  rw [← ι_from_glued, category.assoc]
  erw [is_iso.hom_inv_id_assoc, multicoequalizer.π_desc]
#align
  algebraic_geometry.Scheme.open_cover.ι_glue_morphisms AlgebraicGeometry.SchemeCat.OpenCover.ι_glue_morphisms

theorem hom_ext {Y : SchemeCat} (f₁ f₂ : X ⟶ Y) (h : ∀ x, 𝒰.map x ≫ f₁ = 𝒰.map x ≫ f₂) : f₁ = f₂ :=
  by
  rw [← cancel_epi 𝒰.from_glued]
  apply multicoequalizer.hom_ext
  intro x
  erw [multicoequalizer.π_desc_assoc]
  erw [multicoequalizer.π_desc_assoc]
  exact h x
#align algebraic_geometry.Scheme.open_cover.hom_ext AlgebraicGeometry.SchemeCat.OpenCover.hom_ext

end OpenCover

end SchemeCat

end AlgebraicGeometry

