/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis

! This file was ported from Lean 3 source module analysis.normed_space.star.basic
! leanprover-community/mathlib commit 6d0adfa76594f304b4650d098273d4366edeb61b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Normed.Group.Hom
import Mathbin.Analysis.NormedSpace.Basic
import Mathbin.Analysis.NormedSpace.LinearIsometry
import Mathbin.Analysis.NormedSpace.OperatorNorm
import Mathbin.Algebra.Star.SelfAdjoint
import Mathbin.Algebra.Star.Unitary

/-!
# Normed star rings and algebras

A normed star group is a normed group with a compatible `star` which is isometric.

A C⋆-ring is a normed star group that is also a ring and that verifies the stronger
condition `‖x⋆ * x‖ = ‖x‖^2` for all `x`.  If a C⋆-ring is also a star algebra, then it is a
C⋆-algebra.

To get a C⋆-algebra `E` over field `𝕜`, use
`[normed_field 𝕜] [star_ring 𝕜] [normed_ring E] [star_ring E] [cstar_ring E]
 [normed_algebra 𝕜 E] [star_module 𝕜 E]`.

## TODO

- Show that `‖x⋆ * x‖ = ‖x‖^2` is equivalent to `‖x⋆ * x‖ = ‖x⋆‖ * ‖x‖`, which is used as the
  definition of C*-algebras in some sources (e.g. Wikipedia).

-/


open TopologicalSpace

-- mathport name: «expr ⋆»
local postfix:max "⋆" => star

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "A normed star group is a normed group with a compatible `star` which is isometric. -/")]
      []
      []
      []
      []
      [])
     (Command.structure
      (Command.classTk "class")
      (Command.declId `NormedStarGroup [])
      [(Term.explicitBinder "(" [`E] [":" (Term.type "Type" [(Level.hole "_")])] [] ")")
       (Term.instBinder "[" [] (Term.app `SeminormedAddCommGroup [`E]) "]")
       (Term.instBinder "[" [] (Term.app `StarAddMonoid [`E]) "]")]
      []
      [(Term.typeSpec ":" (Term.prop "Prop"))]
      ["where"
       []
       (Command.structFields
        [(Command.structSimpleBinder
          (Command.declModifiers [] [] [] [] [] [])
          `norm_star
          (Command.optDeclSig
           []
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [`x]
              [(Term.typeSpec ":" `E)]
              ","
              («term_=_»
               (Analysis.Normed.Group.Basic.«term‖_‖»
                "‖"
                (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
                "‖")
               "="
               (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))))])
          [])])]
      (Command.optDeriving [])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structSimpleBinder', expected 'Lean.Parser.Command.structExplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structSimpleBinder', expected 'Lean.Parser.Command.structImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structSimpleBinder', expected 'Lean.Parser.Command.structInstBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`x]
       [(Term.typeSpec ":" `E)]
       ","
       («term_=_»
        (Analysis.Normed.Group.Basic.«term‖_‖»
         "‖"
         (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
         "‖")
        "="
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Analysis.Normed.Group.Basic.«term‖_‖»
        "‖"
        (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
        "‖")
       "="
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.Normed.Group.Basic.«term‖_‖»
       "‖"
       (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
       "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.NormedSpace.Star.Basic.«term_⋆»', expected 'Analysis.NormedSpace.Star.Basic.term_⋆._@.Analysis.NormedSpace.Star.Basic._hyg.7'-/-- failed to format: format: uncaught backtrack exception
/-- A normed star group is a normed group with a compatible `star` which is isometric. -/
  class
    NormedStarGroup
    ( E : Type _ ) [ SeminormedAddCommGroup E ] [ StarAddMonoid E ]
    : Prop
    where norm_star : ∀ x : E , ‖ x ⋆ ‖ = ‖ x ‖
#align normed_star_group NormedStarGroup

export NormedStarGroup (norm_star)

attribute [simp] norm_star

variable {𝕜 E α : Type _}

section NormedStarGroup

variable [SeminormedAddCommGroup E] [StarAddMonoid E] [NormedStarGroup E]

@[simp]
theorem nnnorm_star (x : E) : ‖star x‖₊ = ‖x‖₊ :=
  Subtype.ext <| norm_star _
#align nnnorm_star nnnorm_star

/-- The `star` map in a normed star group is a normed group homomorphism. -/
def starNormedAddGroupHom : NormedAddGroupHom E E :=
  { starAddEquiv with bound' := ⟨1, fun v => le_trans (norm_star _).le (one_mul _).symm.le⟩ }
#align star_normed_add_group_hom starNormedAddGroupHom

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "The `star` map in a normed star group is an isometry -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `star_isometry [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app `Isometry [(Term.typeAscription "(" `star ":" [(Term.arrow `E "→" `E)] ")")])))
      (Command.declValSimple
       ":="
       (Term.show
        "show"
        (Term.app `Isometry [`starAddEquiv])
        (Term.fromTerm
         "from"
         (Term.app
          `AddMonoidHomClass.isometry_of_norm
          [`starAddEquiv
           (Term.show
            "show"
            (Term.forall
             "∀"
             [`x]
             []
             ","
             («term_=_»
              (Analysis.Normed.Group.Basic.«term‖_‖»
               "‖"
               (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
               "‖")
              "="
              (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))
            (Term.fromTerm "from" `norm_star))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       (Term.app `Isometry [`starAddEquiv])
       (Term.fromTerm
        "from"
        (Term.app
         `AddMonoidHomClass.isometry_of_norm
         [`starAddEquiv
          (Term.show
           "show"
           (Term.forall
            "∀"
            [`x]
            []
            ","
            («term_=_»
             (Analysis.Normed.Group.Basic.«term‖_‖»
              "‖"
              (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
              "‖")
             "="
             (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))
           (Term.fromTerm "from" `norm_star))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `AddMonoidHomClass.isometry_of_norm
       [`starAddEquiv
        (Term.show
         "show"
         (Term.forall
          "∀"
          [`x]
          []
          ","
          («term_=_»
           (Analysis.Normed.Group.Basic.«term‖_‖»
            "‖"
            (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
            "‖")
           "="
           (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))
         (Term.fromTerm "from" `norm_star))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       (Term.forall
        "∀"
        [`x]
        []
        ","
        («term_=_»
         (Analysis.Normed.Group.Basic.«term‖_‖»
          "‖"
          (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
          "‖")
         "="
         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))
       (Term.fromTerm "from" `norm_star))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_star
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.forall
       "∀"
       [`x]
       []
       ","
       («term_=_»
        (Analysis.Normed.Group.Basic.«term‖_‖»
         "‖"
         (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
         "‖")
        "="
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Analysis.Normed.Group.Basic.«term‖_‖»
        "‖"
        (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
        "‖")
       "="
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.Normed.Group.Basic.«term‖_‖»
       "‖"
       (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
       "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.NormedSpace.Star.Basic.«term_⋆»', expected 'Analysis.NormedSpace.Star.Basic.term_⋆._@.Analysis.NormedSpace.Star.Basic._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fromTerm', expected 'Lean.Parser.Term.byTactic''
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The `star` map in a normed star group is an isometry -/
  theorem
    star_isometry
    : Isometry ( star : E → E )
    :=
      show
        Isometry starAddEquiv
        from
          AddMonoidHomClass.isometry_of_norm starAddEquiv show ∀ x , ‖ x ⋆ ‖ = ‖ x ‖ from norm_star
#align star_isometry star_isometry

instance (priority := 100) NormedStarGroup.to_has_continuous_star : HasContinuousStar E :=
  ⟨star_isometry.Continuous⟩
#align normed_star_group.to_has_continuous_star NormedStarGroup.to_has_continuous_star

end NormedStarGroup

instance RingHomIsometric.star_ring_end [NormedCommRing E] [StarRing E] [NormedStarGroup E] :
    RingHomIsometric (starRingEnd E) :=
  ⟨norm_star⟩
#align ring_hom_isometric.star_ring_end RingHomIsometric.star_ring_end

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "A C*-ring is a normed star ring that satifies the stronger condition `‖x⋆ * x‖ = ‖x‖^2`\nfor every `x`. -/")]
      []
      []
      []
      []
      [])
     (Command.structure
      (Command.classTk "class")
      (Command.declId `CstarRing [])
      [(Term.explicitBinder "(" [`E] [":" (Term.type "Type" [(Level.hole "_")])] [] ")")
       (Term.instBinder "[" [] (Term.app `NonUnitalNormedRing [`E]) "]")
       (Term.instBinder "[" [] (Term.app `StarRing [`E]) "]")]
      []
      [(Term.typeSpec ":" (Term.prop "Prop"))]
      ["where"
       []
       (Command.structFields
        [(Command.structSimpleBinder
          (Command.declModifiers [] [] [] [] [] [])
          `norm_star_mul_self
          (Command.optDeclSig
           []
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.implicitBinder "{" [`x] [":" `E] "}")]
              []
              ","
              («term_=_»
               (Analysis.Normed.Group.Basic.«term‖_‖»
                "‖"
                («term_*_» (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆") "*" `x)
                "‖")
               "="
               («term_*_»
                (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
                "*"
                (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))))])
          [])])]
      (Command.optDeriving [])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structure', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structSimpleBinder', expected 'Lean.Parser.Command.structExplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structSimpleBinder', expected 'Lean.Parser.Command.structImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.structSimpleBinder', expected 'Lean.Parser.Command.structInstBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [(Term.implicitBinder "{" [`x] [":" `E] "}")]
       []
       ","
       («term_=_»
        (Analysis.Normed.Group.Basic.«term‖_‖»
         "‖"
         («term_*_» (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆") "*" `x)
         "‖")
        "="
        («term_*_»
         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
         "*"
         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Analysis.Normed.Group.Basic.«term‖_‖»
        "‖"
        («term_*_» (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆") "*" `x)
        "‖")
       "="
       («term_*_»
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
        "*"
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
       "*"
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.Normed.Group.Basic.«term‖_‖»
       "‖"
       («term_*_» (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆") "*" `x)
       "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆") "*" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.NormedSpace.Star.Basic.«term_⋆»', expected 'Analysis.NormedSpace.Star.Basic.term_⋆._@.Analysis.NormedSpace.Star.Basic._hyg.7'-/-- failed to format: format: uncaught backtrack exception
/--
    A C*-ring is a normed star ring that satifies the stronger condition `‖x⋆ * x‖ = ‖x‖^2`
    for every `x`. -/
  class
    CstarRing
    ( E : Type _ ) [ NonUnitalNormedRing E ] [ StarRing E ]
    : Prop
    where norm_star_mul_self : ∀ { x : E } , ‖ x ⋆ * x ‖ = ‖ x ‖ * ‖ x ‖
#align cstar_ring CstarRing

instance : CstarRing ℝ where norm_star_mul_self x := by simp only [star, id.def, norm_mul]

namespace CstarRing

section NonUnital

variable [NonUnitalNormedRing E] [StarRing E] [CstarRing E]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "In a C*-ring, star preserves the norm. -/")]
      []
      []
      []
      []
      [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      [(Command.namedPrio "(" "priority" ":=" (num "100") ")")]
      [(Command.declId `to_normed_star_group [])]
      (Command.declSig [] (Term.typeSpec ":" (Term.app `NormedStarGroup [`E])))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.intro "intro" [`x])
             []
             (Classical.«tacticBy_cases_:_» "by_cases" [`htriv ":"] («term_=_» `x "=" (num "0")))
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["[" [(Tactic.simpLemma [] [] `htriv) "," (Tactic.simpLemma [] [] `star_zero)] "]"]
                [])])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`hnt []]
                  [(Term.typeSpec
                    ":"
                    («term_<_» (num "0") "<" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))]
                  ":="
                  (Term.app `norm_pos_iff.mpr [`htriv]))))
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`hnt_star []]
                  [(Term.typeSpec
                    ":"
                    («term_<_»
                     (num "0")
                     "<"
                     (Analysis.Normed.Group.Basic.«term‖_‖»
                      "‖"
                      (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
                      "‖")))]
                  ":="
                  (Term.app
                   `norm_pos_iff.mpr
                   [(Term.app
                     (Term.proj (Term.app `AddEquiv.map_ne_zero_iff [`starAddEquiv]) "." `mpr)
                     [`htriv])]))))
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`h₁ []]
                  []
                  ":="
                  (calc
                   "calc"
                   (calcStep
                    («term_=_»
                     («term_*_»
                      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
                      "*"
                      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))
                     "="
                     (Analysis.Normed.Group.Basic.«term‖_‖»
                      "‖"
                      («term_*_» (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆") "*" `x)
                      "‖"))
                    ":="
                    `norm_star_mul_self.symm)
                   [(calcStep
                     («term_≤_»
                      (Term.hole "_")
                      "≤"
                      («term_*_»
                       (Analysis.Normed.Group.Basic.«term‖_‖»
                        "‖"
                        (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
                        "‖")
                       "*"
                       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))
                     ":="
                     (Term.app `norm_mul_le [(Term.hole "_") (Term.hole "_")]))]))))
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`h₂ []]
                  []
                  ":="
                  (calc
                   "calc"
                   (calcStep
                    («term_=_»
                     («term_*_»
                      (Analysis.Normed.Group.Basic.«term‖_‖»
                       "‖"
                       (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
                       "‖")
                      "*"
                      (Analysis.Normed.Group.Basic.«term‖_‖»
                       "‖"
                       (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
                       "‖"))
                     "="
                     (Analysis.Normed.Group.Basic.«term‖_‖»
                      "‖"
                      («term_*_» `x "*" (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆"))
                      "‖"))
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
                          [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `norm_star_mul_self)
                           ","
                           (Tactic.rwRule [] `star_star)]
                          "]")
                         [])]))))
                   [(calcStep
                     («term_≤_»
                      (Term.hole "_")
                      "≤"
                      («term_*_»
                       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
                       "*"
                       (Analysis.Normed.Group.Basic.«term‖_‖»
                        "‖"
                        (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
                        "‖")))
                     ":="
                     (Term.app `norm_mul_le [(Term.hole "_") (Term.hole "_")]))]))))
               []
               (Tactic.exact
                "exact"
                (Term.app
                 `le_antisymm
                 [(Term.app `le_of_mul_le_mul_right [`h₂ `hnt_star])
                  (Term.app `le_of_mul_le_mul_right [`h₁ `hnt])]))])])))]
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
       [(Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.intro "intro" [`x])
            []
            (Classical.«tacticBy_cases_:_» "by_cases" [`htriv ":"] («term_=_» `x "=" (num "0")))
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["[" [(Tactic.simpLemma [] [] `htriv) "," (Tactic.simpLemma [] [] `star_zero)] "]"]
               [])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`hnt []]
                 [(Term.typeSpec
                   ":"
                   («term_<_» (num "0") "<" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))]
                 ":="
                 (Term.app `norm_pos_iff.mpr [`htriv]))))
              []
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`hnt_star []]
                 [(Term.typeSpec
                   ":"
                   («term_<_»
                    (num "0")
                    "<"
                    (Analysis.Normed.Group.Basic.«term‖_‖»
                     "‖"
                     (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
                     "‖")))]
                 ":="
                 (Term.app
                  `norm_pos_iff.mpr
                  [(Term.app
                    (Term.proj (Term.app `AddEquiv.map_ne_zero_iff [`starAddEquiv]) "." `mpr)
                    [`htriv])]))))
              []
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`h₁ []]
                 []
                 ":="
                 (calc
                  "calc"
                  (calcStep
                   («term_=_»
                    («term_*_»
                     (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
                     "*"
                     (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))
                    "="
                    (Analysis.Normed.Group.Basic.«term‖_‖»
                     "‖"
                     («term_*_» (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆") "*" `x)
                     "‖"))
                   ":="
                   `norm_star_mul_self.symm)
                  [(calcStep
                    («term_≤_»
                     (Term.hole "_")
                     "≤"
                     («term_*_»
                      (Analysis.Normed.Group.Basic.«term‖_‖»
                       "‖"
                       (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
                       "‖")
                      "*"
                      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))
                    ":="
                    (Term.app `norm_mul_le [(Term.hole "_") (Term.hole "_")]))]))))
              []
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`h₂ []]
                 []
                 ":="
                 (calc
                  "calc"
                  (calcStep
                   («term_=_»
                    («term_*_»
                     (Analysis.Normed.Group.Basic.«term‖_‖»
                      "‖"
                      (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
                      "‖")
                     "*"
                     (Analysis.Normed.Group.Basic.«term‖_‖»
                      "‖"
                      (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
                      "‖"))
                    "="
                    (Analysis.Normed.Group.Basic.«term‖_‖»
                     "‖"
                     («term_*_» `x "*" (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆"))
                     "‖"))
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
                         [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `norm_star_mul_self)
                          ","
                          (Tactic.rwRule [] `star_star)]
                         "]")
                        [])]))))
                  [(calcStep
                    («term_≤_»
                     (Term.hole "_")
                     "≤"
                     («term_*_»
                      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
                      "*"
                      (Analysis.Normed.Group.Basic.«term‖_‖»
                       "‖"
                       (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
                       "‖")))
                    ":="
                    (Term.app `norm_mul_le [(Term.hole "_") (Term.hole "_")]))]))))
              []
              (Tactic.exact
               "exact"
               (Term.app
                `le_antisymm
                [(Term.app `le_of_mul_le_mul_right [`h₂ `hnt_star])
                 (Term.app `le_of_mul_le_mul_right [`h₁ `hnt])]))])])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intro "intro" [`x])
          []
          (Classical.«tacticBy_cases_:_» "by_cases" [`htriv ":"] («term_=_» `x "=" (num "0")))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["[" [(Tactic.simpLemma [] [] `htriv) "," (Tactic.simpLemma [] [] `star_zero)] "]"]
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`hnt []]
               [(Term.typeSpec
                 ":"
                 («term_<_» (num "0") "<" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))]
               ":="
               (Term.app `norm_pos_iff.mpr [`htriv]))))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`hnt_star []]
               [(Term.typeSpec
                 ":"
                 («term_<_»
                  (num "0")
                  "<"
                  (Analysis.Normed.Group.Basic.«term‖_‖»
                   "‖"
                   (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
                   "‖")))]
               ":="
               (Term.app
                `norm_pos_iff.mpr
                [(Term.app
                  (Term.proj (Term.app `AddEquiv.map_ne_zero_iff [`starAddEquiv]) "." `mpr)
                  [`htriv])]))))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`h₁ []]
               []
               ":="
               (calc
                "calc"
                (calcStep
                 («term_=_»
                  («term_*_»
                   (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
                   "*"
                   (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))
                  "="
                  (Analysis.Normed.Group.Basic.«term‖_‖»
                   "‖"
                   («term_*_» (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆") "*" `x)
                   "‖"))
                 ":="
                 `norm_star_mul_self.symm)
                [(calcStep
                  («term_≤_»
                   (Term.hole "_")
                   "≤"
                   («term_*_»
                    (Analysis.Normed.Group.Basic.«term‖_‖»
                     "‖"
                     (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
                     "‖")
                    "*"
                    (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))
                  ":="
                  (Term.app `norm_mul_le [(Term.hole "_") (Term.hole "_")]))]))))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`h₂ []]
               []
               ":="
               (calc
                "calc"
                (calcStep
                 («term_=_»
                  («term_*_»
                   (Analysis.Normed.Group.Basic.«term‖_‖»
                    "‖"
                    (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
                    "‖")
                   "*"
                   (Analysis.Normed.Group.Basic.«term‖_‖»
                    "‖"
                    (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
                    "‖"))
                  "="
                  (Analysis.Normed.Group.Basic.«term‖_‖»
                   "‖"
                   («term_*_» `x "*" (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆"))
                   "‖"))
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
                       [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `norm_star_mul_self)
                        ","
                        (Tactic.rwRule [] `star_star)]
                       "]")
                      [])]))))
                [(calcStep
                  («term_≤_»
                   (Term.hole "_")
                   "≤"
                   («term_*_»
                    (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
                    "*"
                    (Analysis.Normed.Group.Basic.«term‖_‖»
                     "‖"
                     (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
                     "‖")))
                  ":="
                  (Term.app `norm_mul_le [(Term.hole "_") (Term.hole "_")]))]))))
            []
            (Tactic.exact
             "exact"
             (Term.app
              `le_antisymm
              [(Term.app `le_of_mul_le_mul_right [`h₂ `hnt_star])
               (Term.app `le_of_mul_le_mul_right [`h₁ `hnt])]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hnt []]
           [(Term.typeSpec
             ":"
             («term_<_» (num "0") "<" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))]
           ":="
           (Term.app `norm_pos_iff.mpr [`htriv]))))
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hnt_star []]
           [(Term.typeSpec
             ":"
             («term_<_»
              (num "0")
              "<"
              (Analysis.Normed.Group.Basic.«term‖_‖»
               "‖"
               (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
               "‖")))]
           ":="
           (Term.app
            `norm_pos_iff.mpr
            [(Term.app
              (Term.proj (Term.app `AddEquiv.map_ne_zero_iff [`starAddEquiv]) "." `mpr)
              [`htriv])]))))
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`h₁ []]
           []
           ":="
           (calc
            "calc"
            (calcStep
             («term_=_»
              («term_*_»
               (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
               "*"
               (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))
              "="
              (Analysis.Normed.Group.Basic.«term‖_‖»
               "‖"
               («term_*_» (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆") "*" `x)
               "‖"))
             ":="
             `norm_star_mul_self.symm)
            [(calcStep
              («term_≤_»
               (Term.hole "_")
               "≤"
               («term_*_»
                (Analysis.Normed.Group.Basic.«term‖_‖»
                 "‖"
                 (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
                 "‖")
                "*"
                (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))
              ":="
              (Term.app `norm_mul_le [(Term.hole "_") (Term.hole "_")]))]))))
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`h₂ []]
           []
           ":="
           (calc
            "calc"
            (calcStep
             («term_=_»
              («term_*_»
               (Analysis.Normed.Group.Basic.«term‖_‖»
                "‖"
                (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
                "‖")
               "*"
               (Analysis.Normed.Group.Basic.«term‖_‖»
                "‖"
                (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
                "‖"))
              "="
              (Analysis.Normed.Group.Basic.«term‖_‖»
               "‖"
               («term_*_» `x "*" (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆"))
               "‖"))
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
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `norm_star_mul_self)
                    ","
                    (Tactic.rwRule [] `star_star)]
                   "]")
                  [])]))))
            [(calcStep
              («term_≤_»
               (Term.hole "_")
               "≤"
               («term_*_»
                (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
                "*"
                (Analysis.Normed.Group.Basic.«term‖_‖»
                 "‖"
                 (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
                 "‖")))
              ":="
              (Term.app `norm_mul_le [(Term.hole "_") (Term.hole "_")]))]))))
        []
        (Tactic.exact
         "exact"
         (Term.app
          `le_antisymm
          [(Term.app `le_of_mul_le_mul_right [`h₂ `hnt_star])
           (Term.app `le_of_mul_le_mul_right [`h₁ `hnt])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `le_antisymm
        [(Term.app `le_of_mul_le_mul_right [`h₂ `hnt_star])
         (Term.app `le_of_mul_le_mul_right [`h₁ `hnt])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le_antisymm
       [(Term.app `le_of_mul_le_mul_right [`h₂ `hnt_star])
        (Term.app `le_of_mul_le_mul_right [`h₁ `hnt])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `le_of_mul_le_mul_right [`h₁ `hnt])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hnt
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_mul_le_mul_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `le_of_mul_le_mul_right [`h₁ `hnt])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `le_of_mul_le_mul_right [`h₂ `hnt_star])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hnt_star
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_of_mul_le_mul_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `le_of_mul_le_mul_right [`h₂ `hnt_star])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_antisymm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`h₂ []]
         []
         ":="
         (calc
          "calc"
          (calcStep
           («term_=_»
            («term_*_»
             (Analysis.Normed.Group.Basic.«term‖_‖»
              "‖"
              (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
              "‖")
             "*"
             (Analysis.Normed.Group.Basic.«term‖_‖»
              "‖"
              (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
              "‖"))
            "="
            (Analysis.Normed.Group.Basic.«term‖_‖»
             "‖"
             («term_*_» `x "*" (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆"))
             "‖"))
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
                 [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `norm_star_mul_self)
                  ","
                  (Tactic.rwRule [] `star_star)]
                 "]")
                [])]))))
          [(calcStep
            («term_≤_»
             (Term.hole "_")
             "≤"
             («term_*_»
              (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
              "*"
              (Analysis.Normed.Group.Basic.«term‖_‖»
               "‖"
               (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
               "‖")))
            ":="
            (Term.app `norm_mul_le [(Term.hole "_") (Term.hole "_")]))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calc
       "calc"
       (calcStep
        («term_=_»
         («term_*_»
          (Analysis.Normed.Group.Basic.«term‖_‖»
           "‖"
           (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
           "‖")
          "*"
          (Analysis.Normed.Group.Basic.«term‖_‖»
           "‖"
           (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
           "‖"))
         "="
         (Analysis.Normed.Group.Basic.«term‖_‖»
          "‖"
          («term_*_» `x "*" (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆"))
          "‖"))
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
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `norm_star_mul_self)
               ","
               (Tactic.rwRule [] `star_star)]
              "]")
             [])]))))
       [(calcStep
         («term_≤_»
          (Term.hole "_")
          "≤"
          («term_*_»
           (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
           "*"
           (Analysis.Normed.Group.Basic.«term‖_‖»
            "‖"
            (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
            "‖")))
         ":="
         (Term.app `norm_mul_le [(Term.hole "_") (Term.hole "_")]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `norm_mul_le [(Term.hole "_") (Term.hole "_")])
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
      `norm_mul_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Term.hole "_")
       "≤"
       («term_*_»
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
        "*"
        (Analysis.Normed.Group.Basic.«term‖_‖»
         "‖"
         (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
         "‖")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
       "*"
       (Analysis.Normed.Group.Basic.«term‖_‖»
        "‖"
        (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
        "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖»
       "‖"
       (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
       "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.NormedSpace.Star.Basic.«term_⋆»', expected 'Analysis.NormedSpace.Star.Basic.term_⋆._@.Analysis.NormedSpace.Star.Basic._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- In a C*-ring, star preserves the norm. -/
  instance
    ( priority := 100 )
    to_normed_star_group
    : NormedStarGroup E
    :=
      ⟨
        by
          intro x
            by_cases htriv : x = 0
            · simp only [ htriv , star_zero ]
            ·
              have hnt : 0 < ‖ x ‖ := norm_pos_iff.mpr htriv
                have
                  hnt_star
                    : 0 < ‖ x ⋆ ‖
                    :=
                    norm_pos_iff.mpr AddEquiv.map_ne_zero_iff starAddEquiv . mpr htriv
                have
                  h₁
                    :=
                    calc
                      ‖ x ‖ * ‖ x ‖ = ‖ x ⋆ * x ‖ := norm_star_mul_self.symm
                      _ ≤ ‖ x ⋆ ‖ * ‖ x ‖ := norm_mul_le _ _
                have
                  h₂
                    :=
                    calc
                      ‖ x ⋆ ‖ * ‖ x ⋆ ‖ = ‖ x * x ⋆ ‖ := by rw [ ← norm_star_mul_self , star_star ]
                      _ ≤ ‖ x ‖ * ‖ x ⋆ ‖ := norm_mul_le _ _
                exact le_antisymm le_of_mul_le_mul_right h₂ hnt_star le_of_mul_le_mul_right h₁ hnt
        ⟩
#align cstar_ring.to_normed_star_group CstarRing.to_normed_star_group

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `norm_self_mul_star [])
      (Command.declSig
       [(Term.implicitBinder "{" [`x] [":" `E] "}")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Analysis.Normed.Group.Basic.«term‖_‖»
          "‖"
          («term_*_» `x "*" (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆"))
          "‖")
         "="
         («term_*_»
          (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
          "*"
          (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Mathlib.Tactic.nthRwSeq
            "nth_rw"
            []
            (num "1")
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `star_star [`x]))]
             "]")
            [])
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `norm_star_mul_self) "," (Tactic.simpLemma [] [] `norm_star)]
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
         [(Mathlib.Tactic.nthRwSeq
           "nth_rw"
           []
           (num "1")
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `star_star [`x]))]
            "]")
           [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `norm_star_mul_self) "," (Tactic.simpLemma [] [] `norm_star)]
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
        [(Tactic.simpLemma [] [] `norm_star_mul_self) "," (Tactic.simpLemma [] [] `norm_star)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_star
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_star_mul_self
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.nthRwSeq
       "nth_rw"
       []
       (num "1")
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `star_star [`x]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `star_star [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `star_star
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Analysis.Normed.Group.Basic.«term‖_‖»
        "‖"
        («term_*_» `x "*" (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆"))
        "‖")
       "="
       («term_*_»
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
        "*"
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
       "*"
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.Normed.Group.Basic.«term‖_‖»
       "‖"
       («term_*_» `x "*" (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆"))
       "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `x "*" (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.NormedSpace.Star.Basic.«term_⋆»', expected 'Analysis.NormedSpace.Star.Basic.term_⋆._@.Analysis.NormedSpace.Star.Basic._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  norm_self_mul_star
  { x : E } : ‖ x * x ⋆ ‖ = ‖ x ‖ * ‖ x ‖
  := by nth_rw 1 [ ← star_star x ] simp only [ norm_star_mul_self , norm_star ]
#align cstar_ring.norm_self_mul_star CstarRing.norm_self_mul_star

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `norm_star_mul_self' [])
      (Command.declSig
       [(Term.implicitBinder "{" [`x] [":" `E] "}")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Analysis.Normed.Group.Basic.«term‖_‖»
          "‖"
          («term_*_» (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆") "*" `x)
          "‖")
         "="
         («term_*_»
          (Analysis.Normed.Group.Basic.«term‖_‖»
           "‖"
           (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
           "‖")
          "*"
          (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))))
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
             [(Tactic.rwRule [] `norm_star_mul_self) "," (Tactic.rwRule [] `norm_star)]
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
            [(Tactic.rwRule [] `norm_star_mul_self) "," (Tactic.rwRule [] `norm_star)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `norm_star_mul_self) "," (Tactic.rwRule [] `norm_star)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_star
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_star_mul_self
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Analysis.Normed.Group.Basic.«term‖_‖»
        "‖"
        («term_*_» (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆") "*" `x)
        "‖")
       "="
       («term_*_»
        (Analysis.Normed.Group.Basic.«term‖_‖»
         "‖"
         (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
         "‖")
        "*"
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Analysis.Normed.Group.Basic.«term‖_‖»
        "‖"
        (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
        "‖")
       "*"
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Analysis.Normed.Group.Basic.«term‖_‖»
       "‖"
       (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
       "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.NormedSpace.Star.Basic.«term_⋆»', expected 'Analysis.NormedSpace.Star.Basic.term_⋆._@.Analysis.NormedSpace.Star.Basic._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  norm_star_mul_self'
  { x : E } : ‖ x ⋆ * x ‖ = ‖ x ⋆ ‖ * ‖ x ‖
  := by rw [ norm_star_mul_self , norm_star ]
#align cstar_ring.norm_star_mul_self' CstarRing.norm_star_mul_self'

theorem nnnorm_self_mul_star {x : E} : ‖x * star x‖₊ = ‖x‖₊ * ‖x‖₊ :=
  Subtype.ext norm_self_mul_star
#align cstar_ring.nnnorm_self_mul_star CstarRing.nnnorm_self_mul_star

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `nnnorm_star_mul_self [])
      (Command.declSig
       [(Term.implicitBinder "{" [`x] [":" `E] "}")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Analysis.Normed.Group.Basic.«term‖_‖₊»
          "‖"
          («term_*_» (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆") "*" `x)
          "‖₊")
         "="
         («term_*_»
          (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" `x "‖₊")
          "*"
          (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" `x "‖₊")))))
      (Command.declValSimple ":=" (Term.app `Subtype.ext [`norm_star_mul_self]) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Subtype.ext [`norm_star_mul_self])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_star_mul_self
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Subtype.ext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Analysis.Normed.Group.Basic.«term‖_‖₊»
        "‖"
        («term_*_» (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆") "*" `x)
        "‖₊")
       "="
       («term_*_»
        (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" `x "‖₊")
        "*"
        (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" `x "‖₊")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" `x "‖₊")
       "*"
       (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" `x "‖₊"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" `x "‖₊")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" `x "‖₊")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.Normed.Group.Basic.«term‖_‖₊»
       "‖"
       («term_*_» (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆") "*" `x)
       "‖₊")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆") "*" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Analysis.NormedSpace.Star.Basic.«term_⋆» `x "⋆")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.NormedSpace.Star.Basic.«term_⋆»', expected 'Analysis.NormedSpace.Star.Basic.term_⋆._@.Analysis.NormedSpace.Star.Basic._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  nnnorm_star_mul_self
  { x : E } : ‖ x ⋆ * x ‖₊ = ‖ x ‖₊ * ‖ x ‖₊
  := Subtype.ext norm_star_mul_self
#align cstar_ring.nnnorm_star_mul_self CstarRing.nnnorm_star_mul_self

@[simp]
theorem star_mul_self_eq_zero_iff (x : E) : star x * x = 0 ↔ x = 0 :=
  by
  rw [← norm_eq_zero, norm_star_mul_self]
  exact mul_self_eq_zero.trans norm_eq_zero
#align cstar_ring.star_mul_self_eq_zero_iff CstarRing.star_mul_self_eq_zero_iff

theorem star_mul_self_ne_zero_iff (x : E) : star x * x ≠ 0 ↔ x ≠ 0 := by
  simp only [Ne.def, star_mul_self_eq_zero_iff]
#align cstar_ring.star_mul_self_ne_zero_iff CstarRing.star_mul_self_ne_zero_iff

@[simp]
theorem mul_star_self_eq_zero_iff (x : E) : x * star x = 0 ↔ x = 0 := by
  simpa only [star_eq_zero, star_star] using @star_mul_self_eq_zero_iff _ _ _ _ (star x)
#align cstar_ring.mul_star_self_eq_zero_iff CstarRing.mul_star_self_eq_zero_iff

theorem mul_star_self_ne_zero_iff (x : E) : x * star x ≠ 0 ↔ x ≠ 0 := by
  simp only [Ne.def, mul_star_self_eq_zero_iff]
#align cstar_ring.mul_star_self_ne_zero_iff CstarRing.mul_star_self_ne_zero_iff

end NonUnital

section ProdPi

variable {ι R₁ R₂ : Type _} {R : ι → Type _}

variable [NonUnitalNormedRing R₁] [StarRing R₁] [CstarRing R₁]

variable [NonUnitalNormedRing R₂] [StarRing R₂] [CstarRing R₂]

variable [∀ i, NonUnitalNormedRing (R i)] [∀ i, StarRing (R i)]

/-- This instance exists to short circuit type class resolution because of problems with
inference involving Π-types. -/
instance Pi.starRing' : StarRing (∀ i, R i) :=
  inferInstance
#align pi.star_ring' Pi.starRing'

variable [Fintype ι] [∀ i, CstarRing (R i)]

instance Prod.cstar_ring : CstarRing (R₁ × R₂)
    where norm_star_mul_self x := by
    unfold norm
    simp only [Prod.fst_mul, Prod.fst_star, Prod.snd_mul, Prod.snd_star, norm_star_mul_self, ← sq]
    refine' le_antisymm _ _
    · refine' max_le _ _ <;> rw [sq_le_sq, abs_of_nonneg (norm_nonneg _)]
      exact (le_max_left _ _).trans (le_abs_self _)
      exact (le_max_right _ _).trans (le_abs_self _)
    · rw [le_sup_iff]
      rcases le_total ‖x.fst‖ ‖x.snd‖ with (h | h) <;> simp [h]
#align prod.cstar_ring Prod.cstar_ring

instance Pi.cstar_ring : CstarRing (∀ i, R i)
    where norm_star_mul_self x :=
    by
    simp only [norm, Pi.mul_apply, Pi.star_apply, nnnorm_star_mul_self, ← sq]
    norm_cast
    exact
      (Finset.comp_sup_eq_sup_comp_of_is_total (fun x : Nnreal => x ^ 2)
          (fun x y h => by simpa only [sq] using mul_le_mul' h h) (by simp)).symm
#align pi.cstar_ring Pi.cstar_ring

instance Pi.cstar_ring' : CstarRing (ι → R₁) :=
  Pi.cstar_ring
#align pi.cstar_ring' Pi.cstar_ring'

end ProdPi

section Unital

variable [NormedRing E] [StarRing E] [CstarRing E]

@[simp]
theorem norm_one [Nontrivial E] : ‖(1 : E)‖ = 1 :=
  by
  have : 0 < ‖(1 : E)‖ := norm_pos_iff.mpr one_ne_zero
  rw [← mul_left_inj' this.ne', ← norm_star_mul_self, mul_one, star_one, one_mul]
#align cstar_ring.norm_one CstarRing.norm_one

-- see Note [lower instance priority]
instance (priority := 100) [Nontrivial E] : NormOneClass E :=
  ⟨norm_one⟩

theorem norm_coe_unitary [Nontrivial E] (U : unitary E) : ‖(U : E)‖ = 1 := by
  rw [← sq_eq_sq (norm_nonneg _) zero_le_one, one_pow 2, sq, ← CstarRing.norm_star_mul_self,
    unitary.coe_star_mul_self, CstarRing.norm_one]
#align cstar_ring.norm_coe_unitary CstarRing.norm_coe_unitary

@[simp]
theorem norm_of_mem_unitary [Nontrivial E] {U : E} (hU : U ∈ unitary E) : ‖U‖ = 1 :=
  norm_coe_unitary ⟨U, hU⟩
#align cstar_ring.norm_of_mem_unitary CstarRing.norm_of_mem_unitary

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
      (Command.declId `norm_coe_unitary_mul [])
      (Command.declSig
       [(Term.explicitBinder "(" [`U] [":" (Term.app `unitary [`E])] [] ")")
        (Term.explicitBinder "(" [`A] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Analysis.Normed.Group.Basic.«term‖_‖»
          "‖"
          («term_*_» (Term.typeAscription "(" `U ":" [`E] ")") "*" `A)
          "‖")
         "="
         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `A "‖"))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Mathlib.Tactic.Nontriviality.nontriviality "nontriviality" [`E] [])
           []
           (Tactic.refine' "refine'" (Term.app `le_antisymm [(Term.hole "_") (Term.hole "_")]))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(calcTactic
              "calc"
              (calcStep
               («term_≤_»
                (Term.hole "_")
                "≤"
                («term_*_»
                 (Analysis.Normed.Group.Basic.«term‖_‖»
                  "‖"
                  (Term.typeAscription "(" `U ":" [`E] ")")
                  "‖")
                 "*"
                 (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `A "‖")))
               ":="
               (Term.app `norm_mul_le [(Term.hole "_") (Term.hole "_")]))
              [(calcStep
                («term_=_» (Term.hole "_") "=" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `A "‖"))
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
                      [(Tactic.rwRule [] `norm_coe_unitary) "," (Tactic.rwRule [] `one_mul)]
                      "]")
                     [])]))))])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(calcTactic
              "calc"
              (calcStep
               («term_=_»
                (Term.hole "_")
                "="
                (Analysis.Normed.Group.Basic.«term‖_‖»
                 "‖"
                 («term_*_»
                  («term_*_»
                   (Analysis.NormedSpace.Star.Basic.«term_⋆»
                    (Term.typeAscription "(" `U ":" [`E] ")")
                    "⋆")
                   "*"
                   `U)
                  "*"
                  `A)
                 "‖"))
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
                     [(Tactic.rwRule [] (Term.app `unitary.coe_star_mul_self [`U]))
                      ","
                      (Tactic.rwRule [] `one_mul)]
                     "]")
                    [])]))))
              [(calcStep
                («term_≤_»
                 (Term.hole "_")
                 "≤"
                 («term_*_»
                  (Analysis.Normed.Group.Basic.«term‖_‖»
                   "‖"
                   (Analysis.NormedSpace.Star.Basic.«term_⋆»
                    (Term.typeAscription "(" `U ":" [`E] ")")
                    "⋆")
                   "‖")
                  "*"
                  (Analysis.Normed.Group.Basic.«term‖_‖»
                   "‖"
                   («term_*_» (Term.typeAscription "(" `U ":" [`E] ")") "*" `A)
                   "‖")))
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_assoc)] "]")
                     [])
                    []
                    (Tactic.exact
                     "exact"
                     (Term.app `norm_mul_le [(Term.hole "_") (Term.hole "_")]))]))))
               (calcStep
                («term_=_»
                 (Term.hole "_")
                 "="
                 (Analysis.Normed.Group.Basic.«term‖_‖»
                  "‖"
                  («term_*_» (Term.typeAscription "(" `U ":" [`E] ")") "*" `A)
                  "‖"))
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
                      [(Tactic.rwRule [] `norm_star)
                       ","
                       (Tactic.rwRule [] `norm_coe_unitary)
                       ","
                       (Tactic.rwRule [] `one_mul)]
                      "]")
                     [])]))))])])])))
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
         [(Mathlib.Tactic.Nontriviality.nontriviality "nontriviality" [`E] [])
          []
          (Tactic.refine' "refine'" (Term.app `le_antisymm [(Term.hole "_") (Term.hole "_")]))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(calcTactic
             "calc"
             (calcStep
              («term_≤_»
               (Term.hole "_")
               "≤"
               («term_*_»
                (Analysis.Normed.Group.Basic.«term‖_‖»
                 "‖"
                 (Term.typeAscription "(" `U ":" [`E] ")")
                 "‖")
                "*"
                (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `A "‖")))
              ":="
              (Term.app `norm_mul_le [(Term.hole "_") (Term.hole "_")]))
             [(calcStep
               («term_=_» (Term.hole "_") "=" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `A "‖"))
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
                     [(Tactic.rwRule [] `norm_coe_unitary) "," (Tactic.rwRule [] `one_mul)]
                     "]")
                    [])]))))])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(calcTactic
             "calc"
             (calcStep
              («term_=_»
               (Term.hole "_")
               "="
               (Analysis.Normed.Group.Basic.«term‖_‖»
                "‖"
                («term_*_»
                 («term_*_»
                  (Analysis.NormedSpace.Star.Basic.«term_⋆»
                   (Term.typeAscription "(" `U ":" [`E] ")")
                   "⋆")
                  "*"
                  `U)
                 "*"
                 `A)
                "‖"))
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
                    [(Tactic.rwRule [] (Term.app `unitary.coe_star_mul_self [`U]))
                     ","
                     (Tactic.rwRule [] `one_mul)]
                    "]")
                   [])]))))
             [(calcStep
               («term_≤_»
                (Term.hole "_")
                "≤"
                («term_*_»
                 (Analysis.Normed.Group.Basic.«term‖_‖»
                  "‖"
                  (Analysis.NormedSpace.Star.Basic.«term_⋆»
                   (Term.typeAscription "(" `U ":" [`E] ")")
                   "⋆")
                  "‖")
                 "*"
                 (Analysis.Normed.Group.Basic.«term‖_‖»
                  "‖"
                  («term_*_» (Term.typeAscription "(" `U ":" [`E] ")") "*" `A)
                  "‖")))
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_assoc)] "]")
                    [])
                   []
                   (Tactic.exact
                    "exact"
                    (Term.app `norm_mul_le [(Term.hole "_") (Term.hole "_")]))]))))
              (calcStep
               («term_=_»
                (Term.hole "_")
                "="
                (Analysis.Normed.Group.Basic.«term‖_‖»
                 "‖"
                 («term_*_» (Term.typeAscription "(" `U ":" [`E] ")") "*" `A)
                 "‖"))
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
                     [(Tactic.rwRule [] `norm_star)
                      ","
                      (Tactic.rwRule [] `norm_coe_unitary)
                      ","
                      (Tactic.rwRule [] `one_mul)]
                     "]")
                    [])]))))])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(calcTactic
         "calc"
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Analysis.Normed.Group.Basic.«term‖_‖»
            "‖"
            («term_*_»
             («term_*_»
              (Analysis.NormedSpace.Star.Basic.«term_⋆»
               (Term.typeAscription "(" `U ":" [`E] ")")
               "⋆")
              "*"
              `U)
             "*"
             `A)
            "‖"))
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
                [(Tactic.rwRule [] (Term.app `unitary.coe_star_mul_self [`U]))
                 ","
                 (Tactic.rwRule [] `one_mul)]
                "]")
               [])]))))
         [(calcStep
           («term_≤_»
            (Term.hole "_")
            "≤"
            («term_*_»
             (Analysis.Normed.Group.Basic.«term‖_‖»
              "‖"
              (Analysis.NormedSpace.Star.Basic.«term_⋆»
               (Term.typeAscription "(" `U ":" [`E] ")")
               "⋆")
              "‖")
             "*"
             (Analysis.Normed.Group.Basic.«term‖_‖»
              "‖"
              («term_*_» (Term.typeAscription "(" `U ":" [`E] ")") "*" `A)
              "‖")))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_assoc)] "]") [])
               []
               (Tactic.exact "exact" (Term.app `norm_mul_le [(Term.hole "_") (Term.hole "_")]))]))))
          (calcStep
           («term_=_»
            (Term.hole "_")
            "="
            (Analysis.Normed.Group.Basic.«term‖_‖»
             "‖"
             («term_*_» (Term.typeAscription "(" `U ":" [`E] ")") "*" `A)
             "‖"))
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
                 [(Tactic.rwRule [] `norm_star)
                  ","
                  (Tactic.rwRule [] `norm_coe_unitary)
                  ","
                  (Tactic.rwRule [] `one_mul)]
                 "]")
                [])]))))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_=_»
         (Term.hole "_")
         "="
         (Analysis.Normed.Group.Basic.«term‖_‖»
          "‖"
          («term_*_»
           («term_*_»
            (Analysis.NormedSpace.Star.Basic.«term_⋆» (Term.typeAscription "(" `U ":" [`E] ")") "⋆")
            "*"
            `U)
           "*"
           `A)
          "‖"))
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
              [(Tactic.rwRule [] (Term.app `unitary.coe_star_mul_self [`U]))
               ","
               (Tactic.rwRule [] `one_mul)]
              "]")
             [])]))))
       [(calcStep
         («term_≤_»
          (Term.hole "_")
          "≤"
          («term_*_»
           (Analysis.Normed.Group.Basic.«term‖_‖»
            "‖"
            (Analysis.NormedSpace.Star.Basic.«term_⋆» (Term.typeAscription "(" `U ":" [`E] ")") "⋆")
            "‖")
           "*"
           (Analysis.Normed.Group.Basic.«term‖_‖»
            "‖"
            («term_*_» (Term.typeAscription "(" `U ":" [`E] ")") "*" `A)
            "‖")))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_assoc)] "]") [])
             []
             (Tactic.exact "exact" (Term.app `norm_mul_le [(Term.hole "_") (Term.hole "_")]))]))))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          (Analysis.Normed.Group.Basic.«term‖_‖»
           "‖"
           («term_*_» (Term.typeAscription "(" `U ":" [`E] ")") "*" `A)
           "‖"))
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
               [(Tactic.rwRule [] `norm_star)
                ","
                (Tactic.rwRule [] `norm_coe_unitary)
                ","
                (Tactic.rwRule [] `one_mul)]
               "]")
              [])]))))])
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
            [(Tactic.rwRule [] `norm_star)
             ","
             (Tactic.rwRule [] `norm_coe_unitary)
             ","
             (Tactic.rwRule [] `one_mul)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `norm_star)
         ","
         (Tactic.rwRule [] `norm_coe_unitary)
         ","
         (Tactic.rwRule [] `one_mul)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_coe_unitary
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_star
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       (Analysis.Normed.Group.Basic.«term‖_‖»
        "‖"
        («term_*_» (Term.typeAscription "(" `U ":" [`E] ")") "*" `A)
        "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖»
       "‖"
       («term_*_» (Term.typeAscription "(" `U ":" [`E] ")") "*" `A)
       "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (Term.typeAscription "(" `U ":" [`E] ")") "*" `A)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.typeAscription "(" `U ":" [`E] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `E
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_assoc)] "]") [])
          []
          (Tactic.exact "exact" (Term.app `norm_mul_le [(Term.hole "_") (Term.hole "_")]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `norm_mul_le [(Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `norm_mul_le [(Term.hole "_") (Term.hole "_")])
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
      `norm_mul_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_assoc)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Term.hole "_")
       "≤"
       («term_*_»
        (Analysis.Normed.Group.Basic.«term‖_‖»
         "‖"
         (Analysis.NormedSpace.Star.Basic.«term_⋆» (Term.typeAscription "(" `U ":" [`E] ")") "⋆")
         "‖")
        "*"
        (Analysis.Normed.Group.Basic.«term‖_‖»
         "‖"
         («term_*_» (Term.typeAscription "(" `U ":" [`E] ")") "*" `A)
         "‖")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Analysis.Normed.Group.Basic.«term‖_‖»
        "‖"
        (Analysis.NormedSpace.Star.Basic.«term_⋆» (Term.typeAscription "(" `U ":" [`E] ")") "⋆")
        "‖")
       "*"
       (Analysis.Normed.Group.Basic.«term‖_‖»
        "‖"
        («term_*_» (Term.typeAscription "(" `U ":" [`E] ")") "*" `A)
        "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖»
       "‖"
       («term_*_» (Term.typeAscription "(" `U ":" [`E] ")") "*" `A)
       "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (Term.typeAscription "(" `U ":" [`E] ")") "*" `A)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.typeAscription "(" `U ":" [`E] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `E
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Analysis.Normed.Group.Basic.«term‖_‖»
       "‖"
       (Analysis.NormedSpace.Star.Basic.«term_⋆» (Term.typeAscription "(" `U ":" [`E] ")") "⋆")
       "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.NormedSpace.Star.Basic.«term_⋆» (Term.typeAscription "(" `U ":" [`E] ")") "⋆")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.NormedSpace.Star.Basic.«term_⋆»', expected 'Analysis.NormedSpace.Star.Basic.term_⋆._@.Analysis.NormedSpace.Star.Basic._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    norm_coe_unitary_mul
    ( U : unitary E ) ( A : E ) : ‖ ( U : E ) * A ‖ = ‖ A ‖
    :=
      by
        nontriviality E
          refine' le_antisymm _ _
          ·
            calc
              _ ≤ ‖ ( U : E ) ‖ * ‖ A ‖ := norm_mul_le _ _
              _ = ‖ A ‖ := by rw [ norm_coe_unitary , one_mul ]
          ·
            calc
              _ = ‖ ( U : E ) ⋆ * U * A ‖ := by rw [ unitary.coe_star_mul_self U , one_mul ]
              _ ≤ ‖ ( U : E ) ⋆ ‖ * ‖ ( U : E ) * A ‖ := by rw [ mul_assoc ] exact norm_mul_le _ _
                _ = ‖ ( U : E ) * A ‖ := by rw [ norm_star , norm_coe_unitary , one_mul ]
#align cstar_ring.norm_coe_unitary_mul CstarRing.norm_coe_unitary_mul

@[simp]
theorem norm_unitary_smul (U : unitary E) (A : E) : ‖U • A‖ = ‖A‖ :=
  norm_coe_unitary_mul U A
#align cstar_ring.norm_unitary_smul CstarRing.norm_unitary_smul

theorem norm_mem_unitary_mul {U : E} (A : E) (hU : U ∈ unitary E) : ‖U * A‖ = ‖A‖ :=
  norm_coe_unitary_mul ⟨U, hU⟩ A
#align cstar_ring.norm_mem_unitary_mul CstarRing.norm_mem_unitary_mul

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
      (Command.declId `norm_mul_coe_unitary [])
      (Command.declSig
       [(Term.explicitBinder "(" [`A] [":" `E] [] ")")
        (Term.explicitBinder "(" [`U] [":" (Term.app `unitary [`E])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" («term_*_» `A "*" `U) "‖")
         "="
         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `A "‖"))))
      (Command.declValSimple
       ":="
       (calc
        "calc"
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          (Analysis.Normed.Group.Basic.«term‖_‖»
           "‖"
           (Analysis.NormedSpace.Star.Basic.«term_⋆»
            («term_*_»
             (Analysis.NormedSpace.Star.Basic.«term_⋆»
              (Term.typeAscription "(" `U ":" [`E] ")")
              "⋆")
             "*"
             (Analysis.NormedSpace.Star.Basic.«term_⋆» `A "⋆"))
            "⋆")
           "‖"))
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
              ["[" [(Tactic.simpLemma [] [] `star_star) "," (Tactic.simpLemma [] [] `star_mul)] "]"]
              [])]))))
        [(calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Analysis.Normed.Group.Basic.«term‖_‖»
            "‖"
            («term_*_»
             (Analysis.NormedSpace.Star.Basic.«term_⋆»
              (Term.typeAscription "(" `U ":" [`E] ")")
              "⋆")
             "*"
             (Analysis.NormedSpace.Star.Basic.«term_⋆» `A "⋆"))
            "‖"))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `norm_star)] "]")
               [])]))))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Analysis.Normed.Group.Basic.«term‖_‖»
            "‖"
            (Analysis.NormedSpace.Star.Basic.«term_⋆» `A "⋆")
            "‖"))
          ":="
          (Term.app
           `norm_mem_unitary_mul
           [(Term.app `star [`A]) (Term.app `unitary.star_mem [(Term.proj `U "." `Prop)])]))
         (calcStep
          («term_=_» (Term.hole "_") "=" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `A "‖"))
          ":="
          (Term.app `norm_star [(Term.hole "_")]))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calc
       "calc"
       (calcStep
        («term_=_»
         (Term.hole "_")
         "="
         (Analysis.Normed.Group.Basic.«term‖_‖»
          "‖"
          (Analysis.NormedSpace.Star.Basic.«term_⋆»
           («term_*_»
            (Analysis.NormedSpace.Star.Basic.«term_⋆» (Term.typeAscription "(" `U ":" [`E] ")") "⋆")
            "*"
            (Analysis.NormedSpace.Star.Basic.«term_⋆» `A "⋆"))
           "⋆")
          "‖"))
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
             ["[" [(Tactic.simpLemma [] [] `star_star) "," (Tactic.simpLemma [] [] `star_mul)] "]"]
             [])]))))
       [(calcStep
         («term_=_»
          (Term.hole "_")
          "="
          (Analysis.Normed.Group.Basic.«term‖_‖»
           "‖"
           («term_*_»
            (Analysis.NormedSpace.Star.Basic.«term_⋆» (Term.typeAscription "(" `U ":" [`E] ")") "⋆")
            "*"
            (Analysis.NormedSpace.Star.Basic.«term_⋆» `A "⋆"))
           "‖"))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `norm_star)] "]")
              [])]))))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          (Analysis.Normed.Group.Basic.«term‖_‖»
           "‖"
           (Analysis.NormedSpace.Star.Basic.«term_⋆» `A "⋆")
           "‖"))
         ":="
         (Term.app
          `norm_mem_unitary_mul
          [(Term.app `star [`A]) (Term.app `unitary.star_mem [(Term.proj `U "." `Prop)])]))
        (calcStep
         («term_=_» (Term.hole "_") "=" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `A "‖"))
         ":="
         (Term.app `norm_star [(Term.hole "_")]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `norm_star [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm_star
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.hole "_") "=" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `A "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `A "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.app
       `norm_mem_unitary_mul
       [(Term.app `star [`A]) (Term.app `unitary.star_mem [(Term.proj `U "." `Prop)])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `unitary.star_mem [(Term.proj `U "." `Prop)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `U "." `Prop)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `U
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `unitary.star_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `unitary.star_mem [(Term.proj `U "." `Prop)])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `star [`A])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `star
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `star [`A]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm_mem_unitary_mul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       (Analysis.Normed.Group.Basic.«term‖_‖»
        "‖"
        (Analysis.NormedSpace.Star.Basic.«term_⋆» `A "⋆")
        "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖»
       "‖"
       (Analysis.NormedSpace.Star.Basic.«term_⋆» `A "⋆")
       "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.NormedSpace.Star.Basic.«term_⋆» `A "⋆")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.NormedSpace.Star.Basic.«term_⋆»', expected 'Analysis.NormedSpace.Star.Basic.term_⋆._@.Analysis.NormedSpace.Star.Basic._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    norm_mul_coe_unitary
    ( A : E ) ( U : unitary E ) : ‖ A * U ‖ = ‖ A ‖
    :=
      calc
        _ = ‖ ( U : E ) ⋆ * A ⋆ ⋆ ‖ := by simp only [ star_star , star_mul ]
        _ = ‖ ( U : E ) ⋆ * A ⋆ ‖ := by rw [ norm_star ]
          _ = ‖ A ⋆ ‖ := norm_mem_unitary_mul star A unitary.star_mem U . Prop
          _ = ‖ A ‖ := norm_star _
#align cstar_ring.norm_mul_coe_unitary CstarRing.norm_mul_coe_unitary

theorem norm_mul_mem_unitary (A : E) {U : E} (hU : U ∈ unitary E) : ‖A * U‖ = ‖A‖ :=
  norm_mul_coe_unitary A ⟨U, hU⟩
#align cstar_ring.norm_mul_mem_unitary CstarRing.norm_mul_mem_unitary

end Unital

end CstarRing

theorem IsSelfAdjoint.nnnorm_pow_two_pow [NormedRing E] [StarRing E] [CstarRing E] {x : E}
    (hx : IsSelfAdjoint x) (n : ℕ) : ‖x ^ 2 ^ n‖₊ = ‖x‖₊ ^ 2 ^ n :=
  by
  induction' n with k hk
  · simp only [pow_zero, pow_one]
  · rw [pow_succ, pow_mul', sq]
    nth_rw 1 [← self_adjoint.mem_iff.mp hx]
    rw [← star_pow, CstarRing.nnnorm_star_mul_self, ← sq, hk, pow_mul']
#align is_self_adjoint.nnnorm_pow_two_pow IsSelfAdjoint.nnnorm_pow_two_pow

theorem selfAdjoint.nnnorm_pow_two_pow [NormedRing E] [StarRing E] [CstarRing E] (x : selfAdjoint E)
    (n : ℕ) : ‖x ^ 2 ^ n‖₊ = ‖x‖₊ ^ 2 ^ n :=
  x.Prop.nnnorm_pow_two_pow _
#align self_adjoint.nnnorm_pow_two_pow selfAdjoint.nnnorm_pow_two_pow

section starₗᵢ

variable [CommSemiring 𝕜] [StarRing 𝕜]

variable [SeminormedAddCommGroup E] [StarAddMonoid E] [NormedStarGroup E]

variable [Module 𝕜 E] [StarModule 𝕜 E]

variable (𝕜)

/-- `star` bundled as a linear isometric equivalence -/
def starₗᵢ : E ≃ₗᵢ⋆[𝕜] E :=
  { starAddEquiv with
    map_smul' := star_smul
    norm_map' := norm_star }
#align starₗᵢ starₗᵢ

variable {𝕜}

@[simp]
theorem coe_starₗᵢ : (starₗᵢ 𝕜 : E → E) = star :=
  rfl
#align coe_starₗᵢ coe_starₗᵢ

theorem starₗᵢ_apply {x : E} : starₗᵢ 𝕜 x = star x :=
  rfl
#align starₗᵢ_apply starₗᵢ_apply

end starₗᵢ

section Mul

open ContinuousLinearMap

variable (𝕜) [DenselyNormedField 𝕜] [NonUnitalNormedRing E] [StarRing E] [CstarRing E]

variable [NormedSpace 𝕜 E] [IsScalarTower 𝕜 E E] [SMulCommClass 𝕜 E E] (a : E)

/-- In a C⋆-algebra `E`, either unital or non-unital, multiplication on the left by `a : E` has
norm equal to the norm of `a`. -/
@[simp]
theorem op_nnnorm_mul : ‖mul 𝕜 E a‖₊ = ‖a‖₊ :=
  by
  rw [← Sup_closed_unit_ball_eq_nnnorm]
  refine' csupₛ_eq_of_forall_le_of_forall_lt_exists_gt _ _ fun r hr => _
  · exact (metric.nonempty_closed_ball.mpr zero_le_one).image _
  · rintro - ⟨x, hx, rfl⟩
    exact
      ((mul 𝕜 E a).unit_le_op_norm x <| mem_closed_ball_zero_iff.mp hx).trans
        (op_norm_mul_apply_le 𝕜 E a)
  · have ha : 0 < ‖a‖₊ := zero_le'.trans_lt hr
    rw [← inv_inv ‖a‖₊, Nnreal.lt_inv_iff_mul_lt (inv_ne_zero ha.ne')] at hr
    obtain ⟨k, hk₁, hk₂⟩ :=
      NormedField.exists_lt_nnnorm_lt 𝕜 (mul_lt_mul_of_pos_right hr <| Nnreal.inv_pos.2 ha)
    refine' ⟨_, ⟨k • star a, _, rfl⟩, _⟩
    ·
      simpa only [mem_closed_ball_zero_iff, norm_smul, one_mul, norm_star] using
        (Nnreal.le_inv_iff_mul_le ha.ne').1 (one_mul ‖a‖₊⁻¹ ▸ hk₂.le : ‖k‖₊ ≤ ‖a‖₊⁻¹)
    · simp only [map_smul, nnnorm_smul, mul_apply', mul_smul_comm, CstarRing.nnnorm_self_mul_star]
      rwa [← Nnreal.div_lt_iff (mul_pos ha ha).ne', div_eq_mul_inv, mul_inv, ← mul_assoc]
#align op_nnnorm_mul op_nnnorm_mul

/-- In a C⋆-algebra `E`, either unital or non-unital, multiplication on the right by `a : E` has
norm eqaul to the norm of `a`. -/
@[simp]
theorem op_nnnorm_mul_flip : ‖(mul 𝕜 E).flip a‖₊ = ‖a‖₊ :=
  by
  rw [← Sup_unit_ball_eq_nnnorm, ← nnnorm_star, ← @op_nnnorm_mul 𝕜 E, ← Sup_unit_ball_eq_nnnorm]
  congr 1
  simp only [mul_apply', flip_apply]
  refine' Set.Subset.antisymm _ _ <;> rintro - ⟨b, hb, rfl⟩ <;>
    refine' ⟨star b, by simpa only [norm_star, mem_ball_zero_iff] using hb, _⟩
  · simp only [← star_mul, nnnorm_star]
  · simpa using (nnnorm_star (star b * a)).symm
#align op_nnnorm_mul_flip op_nnnorm_mul_flip

variable (E)

/-- In a C⋆-algebra `E`, either unital or non-unital, the left regular representation is an
isometry. -/
theorem mul_isometry : Isometry (mul 𝕜 E) :=
  AddMonoidHomClass.isometry_of_norm _ fun a => congr_arg coe <| op_nnnorm_mul 𝕜 a
#align mul_isometry mul_isometry

/-- In a C⋆-algebra `E`, either unital or non-unital, the right regular anti-representation is an
isometry. -/
theorem mul_flip_isometry : Isometry (mul 𝕜 E).flip :=
  AddMonoidHomClass.isometry_of_norm _ fun a => congr_arg coe <| op_nnnorm_mul_flip 𝕜 a
#align mul_flip_isometry mul_flip_isometry

end Mul

