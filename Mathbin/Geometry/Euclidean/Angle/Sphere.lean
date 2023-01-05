/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers

! This file was ported from Lean 3 source module geometry.euclidean.angle.sphere
! leanprover-community/mathlib commit 5a3e819569b0f12cbec59d740a2613018e7b8eec
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Geometry.Euclidean.Angle.Oriented.RightAngle
import Mathbin.Geometry.Euclidean.Circumcenter

/-!
# Angles in circles and sphere.

This file proves results about angles in circles and spheres.

-/


noncomputable section

open FiniteDimensional Complex

open EuclideanGeometry Real RealInnerProductSpace ComplexConjugate

namespace Orientation

variable {V : Type _} [InnerProductSpace ℝ V]

variable [Fact (finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))

/-- Angle at center of a circle equals twice angle at circumference, oriented vector angle
form. -/
theorem oangle_eq_two_zsmul_oangle_sub_of_norm_eq {x y z : V} (hxyne : x ≠ y) (hxzne : x ≠ z)
    (hxy : ‖x‖ = ‖y‖) (hxz : ‖x‖ = ‖z‖) : o.oangle y z = (2 : ℤ) • o.oangle (y - x) (z - x) :=
  by
  have hy : y ≠ 0 := by
    rintro rfl
    rw [norm_zero, norm_eq_zero] at hxy
    exact hxyne hxy
  have hx : x ≠ 0 := norm_ne_zero_iff.1 (hxy.symm ▸ norm_ne_zero_iff.2 hy)
  have hz : z ≠ 0 := norm_ne_zero_iff.1 (hxz ▸ norm_ne_zero_iff.2 hx)
  calc
    o.oangle y z = o.oangle x z - o.oangle x y := (o.oangle_sub_left hx hy hz).symm
    _ = π - (2 : ℤ) • o.oangle (x - z) x - (π - (2 : ℤ) • o.oangle (x - y) x) := by
      rw [o.oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq hxzne.symm hxz.symm,
        o.oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq hxyne.symm hxy.symm]
    _ = (2 : ℤ) • (o.oangle (x - y) x - o.oangle (x - z) x) := by abel
    _ = (2 : ℤ) • o.oangle (x - y) (x - z) := by
      rw [o.oangle_sub_right (sub_ne_zero_of_ne hxyne) (sub_ne_zero_of_ne hxzne) hx]
    _ = (2 : ℤ) • o.oangle (y - x) (z - x) := by rw [← oangle_neg_neg, neg_sub, neg_sub]
    
#align
  orientation.oangle_eq_two_zsmul_oangle_sub_of_norm_eq Orientation.oangle_eq_two_zsmul_oangle_sub_of_norm_eq

/-- Angle at center of a circle equals twice angle at circumference, oriented vector angle
form with radius specified. -/
theorem oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real {x y z : V} (hxyne : x ≠ y) (hxzne : x ≠ z)
    {r : ℝ} (hx : ‖x‖ = r) (hy : ‖y‖ = r) (hz : ‖z‖ = r) :
    o.oangle y z = (2 : ℤ) • o.oangle (y - x) (z - x) :=
  o.oangle_eq_two_zsmul_oangle_sub_of_norm_eq hxyne hxzne (hy.symm ▸ hx) (hz.symm ▸ hx)
#align
  orientation.oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real Orientation.oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real

/-- Oriented vector angle version of "angles in same segment are equal" and "opposite angles of
a cyclic quadrilateral add to π", for oriented angles mod π (for which those are the same
result), represented here as equality of twice the angles. -/
theorem two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq {x₁ x₂ y z : V} (hx₁yne : x₁ ≠ y)
    (hx₁zne : x₁ ≠ z) (hx₂yne : x₂ ≠ y) (hx₂zne : x₂ ≠ z) {r : ℝ} (hx₁ : ‖x₁‖ = r) (hx₂ : ‖x₂‖ = r)
    (hy : ‖y‖ = r) (hz : ‖z‖ = r) :
    (2 : ℤ) • o.oangle (y - x₁) (z - x₁) = (2 : ℤ) • o.oangle (y - x₂) (z - x₂) :=
  o.oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real hx₁yne hx₁zne hx₁ hy hz ▸
    o.oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real hx₂yne hx₂zne hx₂ hy hz
#align
  orientation.two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq Orientation.two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq

end Orientation

namespace EuclideanGeometry

variable {V : Type _} {P : Type _} [InnerProductSpace ℝ V] [MetricSpace P]

variable [NormedAddTorsor V P] [hd2 : Fact (finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

include hd2

-- mathport name: expro
local notation "o" => Module.Oriented.positiveOrientation

namespace Sphere

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Angle at center of a circle equals twice angle at circumference, oriented angle version. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `oangle_center_eq_two_zsmul_oangle [])
      (Command.declSig
       [(Term.implicitBinder "{" [`s] [":" (Term.app `Sphere [`P])] "}")
        (Term.implicitBinder "{" [`p₁ `p₂ `p₃] [":" `P] "}")
        (Term.explicitBinder "(" [`hp₁] [":" («term_∈_» `p₁ "∈" `s)] [] ")")
        (Term.explicitBinder "(" [`hp₂] [":" («term_∈_» `p₂ "∈" `s)] [] ")")
        (Term.explicitBinder "(" [`hp₃] [":" («term_∈_» `p₃ "∈" `s)] [] ")")
        (Term.explicitBinder "(" [`hp₂p₁] [":" («term_≠_» `p₂ "≠" `p₁)] [] ")")
        (Term.explicitBinder "(" [`hp₂p₃] [":" («term_≠_» `p₂ "≠" `p₃)] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
          [`p₁ (Term.proj `s "." `center) `p₃])
         "="
         (Algebra.Group.Defs.«term_•_»
          (Term.typeAscription "(" (num "2") ":" [(termℤ "ℤ")] ")")
          " • "
          (Term.app
           (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
           [`p₁ `p₂ `p₃])))))
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
             [(Tactic.rwRule [] `mem_sphere)
              ","
              (Tactic.rwRule [] (Term.app (Term.explicit "@" `dist_eq_norm_vsub) [`V]))]
             "]")
            [(Tactic.location "at" (Tactic.locationHyp [`hp₁ `hp₂ `hp₃] []))])
           []
           (Tactic.«tactic_<;>_»
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
                []
                (Term.app
                 (Term.proj
                  (EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo "o")
                  "."
                  `oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real)
                 [(Term.hole "_") (Term.hole "_") `hp₂ `hp₁ `hp₃]))]
              "]")
             [])
            "<;>"
            (Tactic.simp
             "simp"
             []
             []
             []
             ["[" [(Tactic.simpLemma [] [] `hp₂p₁) "," (Tactic.simpLemma [] [] `hp₂p₃)] "]"]
             []))])))
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
            [(Tactic.rwRule [] `mem_sphere)
             ","
             (Tactic.rwRule [] (Term.app (Term.explicit "@" `dist_eq_norm_vsub) [`V]))]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`hp₁ `hp₂ `hp₃] []))])
          []
          (Tactic.«tactic_<;>_»
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
               []
               (Term.app
                (Term.proj
                 (EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo "o")
                 "."
                 `oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real)
                [(Term.hole "_") (Term.hole "_") `hp₂ `hp₁ `hp₃]))]
             "]")
            [])
           "<;>"
           (Tactic.simp
            "simp"
            []
            []
            []
            ["[" [(Tactic.simpLemma [] [] `hp₂p₁) "," (Tactic.simpLemma [] [] `hp₂p₃)] "]"]
            []))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
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
           []
           (Term.app
            (Term.proj
             (EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo "o")
             "."
             `oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real)
            [(Term.hole "_") (Term.hole "_") `hp₂ `hp₁ `hp₃]))]
         "]")
        [])
       "<;>"
       (Tactic.simp
        "simp"
        []
        []
        []
        ["[" [(Tactic.simpLemma [] [] `hp₂p₁) "," (Tactic.simpLemma [] [] `hp₂p₃)] "]"]
        []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["[" [(Tactic.simpLemma [] [] `hp₂p₁) "," (Tactic.simpLemma [] [] `hp₂p₃)] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp₂p₃
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp₂p₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
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
          []
          (Term.app
           (Term.proj
            (EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo "o")
            "."
            `oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real)
           [(Term.hole "_") (Term.hole "_") `hp₂ `hp₁ `hp₃]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo "o")
        "."
        `oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real)
       [(Term.hole "_") (Term.hole "_") `hp₂ `hp₁ `hp₃])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp₃
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hp₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hp₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo "o")
       "."
       `oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo._@.Geometry.Euclidean.Angle.Sphere._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Angle at center of a circle equals twice angle at circumference, oriented angle version. -/
  theorem
    oangle_center_eq_two_zsmul_oangle
    { s : Sphere P }
        { p₁ p₂ p₃ : P }
        ( hp₁ : p₁ ∈ s )
        ( hp₂ : p₂ ∈ s )
        ( hp₃ : p₃ ∈ s )
        ( hp₂p₁ : p₂ ≠ p₁ )
        ( hp₂p₃ : p₂ ≠ p₃ )
      : ∡ p₁ s . center p₃ = ( 2 : ℤ ) • ∡ p₁ p₂ p₃
    :=
      by
        rw [ mem_sphere , @ dist_eq_norm_vsub V ] at hp₁ hp₂ hp₃
          rw
              [
                oangle , oangle , o . oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real _ _ hp₂ hp₁ hp₃
                ]
            <;>
            simp [ hp₂p₁ , hp₂p₃ ]
#align
  euclidean_geometry.sphere.oangle_center_eq_two_zsmul_oangle EuclideanGeometry.Sphere.oangle_center_eq_two_zsmul_oangle

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Oriented angle version of \"angles in same segment are equal\" and \"opposite angles of a\ncyclic quadrilateral add to π\", for oriented angles mod π (for which those are the same result),\nrepresented here as equality of twice the angles. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `two_zsmul_oangle_eq [])
      (Command.declSig
       [(Term.implicitBinder "{" [`s] [":" (Term.app `Sphere [`P])] "}")
        (Term.implicitBinder "{" [`p₁ `p₂ `p₃ `p₄] [":" `P] "}")
        (Term.explicitBinder "(" [`hp₁] [":" («term_∈_» `p₁ "∈" `s)] [] ")")
        (Term.explicitBinder "(" [`hp₂] [":" («term_∈_» `p₂ "∈" `s)] [] ")")
        (Term.explicitBinder "(" [`hp₃] [":" («term_∈_» `p₃ "∈" `s)] [] ")")
        (Term.explicitBinder "(" [`hp₄] [":" («term_∈_» `p₄ "∈" `s)] [] ")")
        (Term.explicitBinder "(" [`hp₂p₁] [":" («term_≠_» `p₂ "≠" `p₁)] [] ")")
        (Term.explicitBinder "(" [`hp₂p₄] [":" («term_≠_» `p₂ "≠" `p₄)] [] ")")
        (Term.explicitBinder "(" [`hp₃p₁] [":" («term_≠_» `p₃ "≠" `p₁)] [] ")")
        (Term.explicitBinder "(" [`hp₃p₄] [":" («term_≠_» `p₃ "≠" `p₄)] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Algebra.Group.Defs.«term_•_»
          (Term.typeAscription "(" (num "2") ":" [(termℤ "ℤ")] ")")
          " • "
          (Term.app
           (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
           [`p₁ `p₂ `p₄]))
         "="
         (Algebra.Group.Defs.«term_•_»
          (Term.typeAscription "(" (num "2") ":" [(termℤ "ℤ")] ")")
          " • "
          (Term.app
           (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
           [`p₁ `p₃ `p₄])))))
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
             [(Tactic.rwRule [] `mem_sphere)
              ","
              (Tactic.rwRule [] (Term.app (Term.explicit "@" `dist_eq_norm_vsub) [`V]))]
             "]")
            [(Tactic.location "at" (Tactic.locationHyp [`hp₁ `hp₂ `hp₃ `hp₄] []))])
           []
           (Tactic.«tactic_<;>_»
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
                (Term.app `vsub_sub_vsub_cancel_right [`p₁ `p₂ `s.center]))
               ","
               (Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.app `vsub_sub_vsub_cancel_right [`p₄ `p₂ `s.center]))
               ","
               (Tactic.rwRule
                []
                (Term.app
                 (Term.proj
                  (EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo "o")
                  "."
                  `two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq)
                 [(Term.hole "_")
                  (Term.hole "_")
                  (Term.hole "_")
                  (Term.hole "_")
                  `hp₂
                  `hp₃
                  `hp₁
                  `hp₄]))]
              "]")
             [])
            "<;>"
            (Tactic.simp
             "simp"
             []
             []
             []
             ["["
              [(Tactic.simpLemma [] [] `hp₂p₁)
               ","
               (Tactic.simpLemma [] [] `hp₂p₄)
               ","
               (Tactic.simpLemma [] [] `hp₃p₁)
               ","
               (Tactic.simpLemma [] [] `hp₃p₄)]
              "]"]
             []))])))
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
            [(Tactic.rwRule [] `mem_sphere)
             ","
             (Tactic.rwRule [] (Term.app (Term.explicit "@" `dist_eq_norm_vsub) [`V]))]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`hp₁ `hp₂ `hp₃ `hp₄] []))])
          []
          (Tactic.«tactic_<;>_»
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
               (Term.app `vsub_sub_vsub_cancel_right [`p₁ `p₂ `s.center]))
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app `vsub_sub_vsub_cancel_right [`p₄ `p₂ `s.center]))
              ","
              (Tactic.rwRule
               []
               (Term.app
                (Term.proj
                 (EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo "o")
                 "."
                 `two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq)
                [(Term.hole "_")
                 (Term.hole "_")
                 (Term.hole "_")
                 (Term.hole "_")
                 `hp₂
                 `hp₃
                 `hp₁
                 `hp₄]))]
             "]")
            [])
           "<;>"
           (Tactic.simp
            "simp"
            []
            []
            []
            ["["
             [(Tactic.simpLemma [] [] `hp₂p₁)
              ","
              (Tactic.simpLemma [] [] `hp₂p₄)
              ","
              (Tactic.simpLemma [] [] `hp₃p₁)
              ","
              (Tactic.simpLemma [] [] `hp₃p₄)]
             "]"]
            []))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
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
           (Term.app `vsub_sub_vsub_cancel_right [`p₁ `p₂ `s.center]))
          ","
          (Tactic.rwRule
           [(patternIgnore (token.«← » "←"))]
           (Term.app `vsub_sub_vsub_cancel_right [`p₄ `p₂ `s.center]))
          ","
          (Tactic.rwRule
           []
           (Term.app
            (Term.proj
             (EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo "o")
             "."
             `two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq)
            [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") `hp₂ `hp₃ `hp₁ `hp₄]))]
         "]")
        [])
       "<;>"
       (Tactic.simp
        "simp"
        []
        []
        []
        ["["
         [(Tactic.simpLemma [] [] `hp₂p₁)
          ","
          (Tactic.simpLemma [] [] `hp₂p₄)
          ","
          (Tactic.simpLemma [] [] `hp₃p₁)
          ","
          (Tactic.simpLemma [] [] `hp₃p₄)]
         "]"]
        []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpLemma [] [] `hp₂p₁)
         ","
         (Tactic.simpLemma [] [] `hp₂p₄)
         ","
         (Tactic.simpLemma [] [] `hp₃p₁)
         ","
         (Tactic.simpLemma [] [] `hp₃p₄)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp₃p₄
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp₃p₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp₂p₄
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp₂p₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
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
          (Term.app `vsub_sub_vsub_cancel_right [`p₁ `p₂ `s.center]))
         ","
         (Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app `vsub_sub_vsub_cancel_right [`p₄ `p₂ `s.center]))
         ","
         (Tactic.rwRule
          []
          (Term.app
           (Term.proj
            (EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo "o")
            "."
            `two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq)
           [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") `hp₂ `hp₃ `hp₁ `hp₄]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo "o")
        "."
        `two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq)
       [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") `hp₂ `hp₃ `hp₁ `hp₄])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp₄
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hp₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hp₃
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hp₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo "o")
       "."
       `two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo._@.Geometry.Euclidean.Angle.Sphere._hyg.9'
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
    Oriented angle version of "angles in same segment are equal" and "opposite angles of a
    cyclic quadrilateral add to π", for oriented angles mod π (for which those are the same result),
    represented here as equality of twice the angles. -/
  theorem
    two_zsmul_oangle_eq
    { s : Sphere P }
        { p₁ p₂ p₃ p₄ : P }
        ( hp₁ : p₁ ∈ s )
        ( hp₂ : p₂ ∈ s )
        ( hp₃ : p₃ ∈ s )
        ( hp₄ : p₄ ∈ s )
        ( hp₂p₁ : p₂ ≠ p₁ )
        ( hp₂p₄ : p₂ ≠ p₄ )
        ( hp₃p₁ : p₃ ≠ p₁ )
        ( hp₃p₄ : p₃ ≠ p₄ )
      : ( 2 : ℤ ) • ∡ p₁ p₂ p₄ = ( 2 : ℤ ) • ∡ p₁ p₃ p₄
    :=
      by
        rw [ mem_sphere , @ dist_eq_norm_vsub V ] at hp₁ hp₂ hp₃ hp₄
          rw
              [
                oangle
                  ,
                  oangle
                  ,
                  ← vsub_sub_vsub_cancel_right p₁ p₂ s.center
                  ,
                  ← vsub_sub_vsub_cancel_right p₄ p₂ s.center
                  ,
                  o . two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq
                    _ _ _ _ hp₂ hp₃ hp₁ hp₄
                ]
            <;>
            simp [ hp₂p₁ , hp₂p₄ , hp₃p₁ , hp₃p₄ ]
#align euclidean_geometry.sphere.two_zsmul_oangle_eq EuclideanGeometry.Sphere.two_zsmul_oangle_eq

end Sphere

/-- Oriented angle version of "angles in same segment are equal" and "opposite angles of a
cyclic quadrilateral add to π", for oriented angles mod π (for which those are the same result),
represented here as equality of twice the angles. -/
theorem Cospherical.two_zsmul_oangle_eq {p₁ p₂ p₃ p₄ : P}
    (h : Cospherical ({p₁, p₂, p₃, p₄} : Set P)) (hp₂p₁ : p₂ ≠ p₁) (hp₂p₄ : p₂ ≠ p₄)
    (hp₃p₁ : p₃ ≠ p₁) (hp₃p₄ : p₃ ≠ p₄) : (2 : ℤ) • ∡ p₁ p₂ p₄ = (2 : ℤ) • ∡ p₁ p₃ p₄ :=
  by
  obtain ⟨s, hs⟩ := cospherical_iff_exists_sphere.1 h
  simp_rw [Set.insert_subset, Set.singleton_subset_iff, sphere.mem_coe] at hs
  exact sphere.two_zsmul_oangle_eq hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 hp₂p₁ hp₂p₄ hp₃p₁ hp₃p₄
#align
  euclidean_geometry.cospherical.two_zsmul_oangle_eq EuclideanGeometry.Cospherical.two_zsmul_oangle_eq

namespace Sphere

/-- The angle at the apex of an isosceles triangle is `π` minus twice a base angle, oriented
angle-at-point form where the apex is given as the center of a circle. -/
theorem oangle_eq_pi_sub_two_zsmul_oangle_center_left {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) (h : p₁ ≠ p₂) : ∡ p₁ s.center p₂ = π - (2 : ℤ) • ∡ s.center p₂ p₁ := by
  rw [oangle_eq_pi_sub_two_zsmul_oangle_of_dist_eq h.symm
      (dist_center_eq_dist_center_of_mem_sphere' hp₂ hp₁)]
#align
  euclidean_geometry.sphere.oangle_eq_pi_sub_two_zsmul_oangle_center_left EuclideanGeometry.Sphere.oangle_eq_pi_sub_two_zsmul_oangle_center_left

/-- The angle at the apex of an isosceles triangle is `π` minus twice a base angle, oriented
angle-at-point form where the apex is given as the center of a circle. -/
theorem oangle_eq_pi_sub_two_zsmul_oangle_center_right {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) (h : p₁ ≠ p₂) : ∡ p₁ s.center p₂ = π - (2 : ℤ) • ∡ p₂ p₁ s.center := by
  rw [oangle_eq_pi_sub_two_zsmul_oangle_center_left hp₁ hp₂ h,
    oangle_eq_oangle_of_dist_eq (dist_center_eq_dist_center_of_mem_sphere' hp₂ hp₁)]
#align
  euclidean_geometry.sphere.oangle_eq_pi_sub_two_zsmul_oangle_center_right EuclideanGeometry.Sphere.oangle_eq_pi_sub_two_zsmul_oangle_center_right

/-- Twice a base angle of an isosceles triangle with apex at the center of a circle, plus twice
the angle at the apex of a triangle with the same base but apex on the circle, equals `π`. -/
theorem two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi {s : Sphere P} {p₁ p₂ p₃ : P}
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) (hp₂p₁ : p₂ ≠ p₁) (hp₂p₃ : p₂ ≠ p₃)
    (hp₁p₃ : p₁ ≠ p₃) : (2 : ℤ) • ∡ p₃ p₁ s.center + (2 : ℤ) • ∡ p₁ p₂ p₃ = π := by
  rw [← oangle_center_eq_two_zsmul_oangle hp₁ hp₂ hp₃ hp₂p₁ hp₂p₃,
    oangle_eq_pi_sub_two_zsmul_oangle_center_right hp₁ hp₃ hp₁p₃, add_sub_cancel'_right]
#align
  euclidean_geometry.sphere.two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi EuclideanGeometry.Sphere.two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi

/-- A base angle of an isosceles triangle with apex at the center of a circle is acute. -/
theorem abs_oangle_center_left_to_real_lt_pi_div_two {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) : |(∡ s.center p₂ p₁).toReal| < π / 2 :=
  abs_oangle_right_to_real_lt_pi_div_two_of_dist_eq
    (dist_center_eq_dist_center_of_mem_sphere' hp₂ hp₁)
#align
  euclidean_geometry.sphere.abs_oangle_center_left_to_real_lt_pi_div_two EuclideanGeometry.Sphere.abs_oangle_center_left_to_real_lt_pi_div_two

/-- A base angle of an isosceles triangle with apex at the center of a circle is acute. -/
theorem abs_oangle_center_right_to_real_lt_pi_div_two {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) : |(∡ p₂ p₁ s.center).toReal| < π / 2 :=
  abs_oangle_left_to_real_lt_pi_div_two_of_dist_eq
    (dist_center_eq_dist_center_of_mem_sphere' hp₂ hp₁)
#align
  euclidean_geometry.sphere.abs_oangle_center_right_to_real_lt_pi_div_two EuclideanGeometry.Sphere.abs_oangle_center_right_to_real_lt_pi_div_two

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Given two points on a circle, the center of that circle may be expressed explicitly as a\nmultiple (by half the tangent of the angle between the chord and the radius at one of those\npoints) of a `π / 2` rotation of the vector between those points, plus the midpoint of those\npoints. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center [])
      (Command.declSig
       [(Term.implicitBinder "{" [`s] [":" (Term.app `Sphere [`P])] "}")
        (Term.implicitBinder "{" [`p₁ `p₂] [":" `P] "}")
        (Term.explicitBinder "(" [`hp₁] [":" («term_∈_» `p₁ "∈" `s)] [] ")")
        (Term.explicitBinder "(" [`hp₂] [":" («term_∈_» `p₂ "∈" `s)] [] ")")
        (Term.explicitBinder "(" [`h] [":" («term_≠_» `p₁ "≠" `p₂)] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Algebra.Group.Defs.«term_+ᵥ_»
          (Algebra.Group.Defs.«term_•_»
           («term_/_»
            (Term.app
             `Real.Angle.tan
             [(Term.app
               (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
               [`p₂ `p₁ (Term.proj `s "." `center)])])
            "/"
            (num "2"))
           " • "
           (Term.app
            (Term.proj (EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo "o") "." `rotation)
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
         (Term.proj `s "." `center))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.obtain
            "obtain"
            [(Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr)])
                  [])]
                "⟩")])]
            []
            [":="
             [(Term.app
               (Term.proj
                (Term.app `dist_eq_iff_eq_smul_rotation_pi_div_two_vadd_midpoint [`h])
                "."
                (fieldIdx "1"))
               [(Term.app `dist_center_eq_dist_center_of_mem_sphere [`hp₁ `hp₂])])]])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hr)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `oangle_midpoint_rev_left)
              ","
              (Tactic.rwRule [] `oangle)
              ","
              (Tactic.rwRule [] `vadd_vsub_assoc)]
             "]")
            [])
           []
           (Mathlib.Tactic.nthRwSeq
            "nth_rw"
            []
            (num "1")
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               []
               (Term.show
                "show"
                («term_=_»
                 (Algebra.Group.Defs.«term_-ᵥ_» `p₂ " -ᵥ " `p₁)
                 "="
                 (Algebra.Group.Defs.«term_•_»
                  (Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                  " • "
                  (Algebra.Group.Defs.«term_-ᵥ_»
                   (Term.app `midpoint [(Data.Real.Basic.termℝ "ℝ") `p₁ `p₂])
                   " -ᵥ "
                   `p₁)))
                (Term.byTactic'
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))))]
             "]")
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `map_smul)
              ","
              (Tactic.rwRule [] `smul_smul)
              ","
              (Tactic.rwRule [] `add_comm)
              ","
              (Tactic.rwRule
               []
               (Term.proj
                (EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo "o")
                "."
                `tan_oangle_add_right_smul_rotation_pi_div_two))
              ","
              (Tactic.rwRule
               []
               (Term.app
                `mul_div_cancel
                [(Term.hole "_") (Term.app `two_ne_zero' [(Data.Real.Basic.termℝ "ℝ")])]))]
             "]")
            [])
           []
           (Std.Tactic.Simpa.simpa
            "simpa"
            []
            []
            (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `h.symm]))])))
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
         [(Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr)])
                 [])]
               "⟩")])]
           []
           [":="
            [(Term.app
              (Term.proj
               (Term.app `dist_eq_iff_eq_smul_rotation_pi_div_two_vadd_midpoint [`h])
               "."
               (fieldIdx "1"))
              [(Term.app `dist_center_eq_dist_center_of_mem_sphere [`hp₁ `hp₂])])]])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hr)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `oangle_midpoint_rev_left)
             ","
             (Tactic.rwRule [] `oangle)
             ","
             (Tactic.rwRule [] `vadd_vsub_assoc)]
            "]")
           [])
          []
          (Mathlib.Tactic.nthRwSeq
           "nth_rw"
           []
           (num "1")
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.show
               "show"
               («term_=_»
                (Algebra.Group.Defs.«term_-ᵥ_» `p₂ " -ᵥ " `p₁)
                "="
                (Algebra.Group.Defs.«term_•_»
                 (Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                 " • "
                 (Algebra.Group.Defs.«term_-ᵥ_»
                  (Term.app `midpoint [(Data.Real.Basic.termℝ "ℝ") `p₁ `p₂])
                  " -ᵥ "
                  `p₁)))
               (Term.byTactic'
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))))]
            "]")
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `map_smul)
             ","
             (Tactic.rwRule [] `smul_smul)
             ","
             (Tactic.rwRule [] `add_comm)
             ","
             (Tactic.rwRule
              []
              (Term.proj
               (EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo "o")
               "."
               `tan_oangle_add_right_smul_rotation_pi_div_two))
             ","
             (Tactic.rwRule
              []
              (Term.app
               `mul_div_cancel
               [(Term.hole "_") (Term.app `two_ne_zero' [(Data.Real.Basic.termℝ "ℝ")])]))]
            "]")
           [])
          []
          (Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `h.symm]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `h.symm]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h.symm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `map_smul)
         ","
         (Tactic.rwRule [] `smul_smul)
         ","
         (Tactic.rwRule [] `add_comm)
         ","
         (Tactic.rwRule
          []
          (Term.proj
           (EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo "o")
           "."
           `tan_oangle_add_right_smul_rotation_pi_div_two))
         ","
         (Tactic.rwRule
          []
          (Term.app
           `mul_div_cancel
           [(Term.hole "_") (Term.app `two_ne_zero' [(Data.Real.Basic.termℝ "ℝ")])]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mul_div_cancel
       [(Term.hole "_") (Term.app `two_ne_zero' [(Data.Real.Basic.termℝ "ℝ")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `two_ne_zero' [(Data.Real.Basic.termℝ "ℝ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `two_ne_zero'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `two_ne_zero' [(Data.Real.Basic.termℝ "ℝ")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_div_cancel
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo "o")
       "."
       `tan_oangle_add_right_smul_rotation_pi_div_two)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo._@.Geometry.Euclidean.Angle.Sphere._hyg.9'
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
    Given two points on a circle, the center of that circle may be expressed explicitly as a
    multiple (by half the tangent of the angle between the chord and the radius at one of those
    points) of a `π / 2` rotation of the vector between those points, plus the midpoint of those
    points. -/
  theorem
    tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center
    { s : Sphere P } { p₁ p₂ : P } ( hp₁ : p₁ ∈ s ) ( hp₂ : p₂ ∈ s ) ( h : p₁ ≠ p₂ )
      :
        Real.Angle.tan ∡ p₂ p₁ s . center / 2 • o . rotation ( π / 2 : ℝ ) p₂ -ᵥ p₁
            +ᵥ
            midpoint ℝ p₁ p₂
          =
          s . center
    :=
      by
        obtain
            ⟨ r , hr ⟩
            :=
              dist_eq_iff_eq_smul_rotation_pi_div_two_vadd_midpoint h . 1
                dist_center_eq_dist_center_of_mem_sphere hp₁ hp₂
          rw [ ← hr , ← oangle_midpoint_rev_left , oangle , vadd_vsub_assoc ]
          nth_rw 1 [ show p₂ -ᵥ p₁ = ( 2 : ℝ ) • midpoint ℝ p₁ p₂ -ᵥ p₁ by simp ]
          rw
            [
              map_smul
                ,
                smul_smul
                ,
                add_comm
                ,
                o . tan_oangle_add_right_smul_rotation_pi_div_two
                ,
                mul_div_cancel _ two_ne_zero' ℝ
              ]
          simpa using h.symm
#align
  euclidean_geometry.sphere.tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center EuclideanGeometry.Sphere.tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Given three points on a circle, the center of that circle may be expressed explicitly as a\nmultiple (by half the inverse of the tangent of the angle at one of those points) of a `π / 2`\nrotation of the vector between the other two points, plus the midpoint of those points. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center [])
      (Command.declSig
       [(Term.implicitBinder "{" [`s] [":" (Term.app `Sphere [`P])] "}")
        (Term.implicitBinder "{" [`p₁ `p₂ `p₃] [":" `P] "}")
        (Term.explicitBinder "(" [`hp₁] [":" («term_∈_» `p₁ "∈" `s)] [] ")")
        (Term.explicitBinder "(" [`hp₂] [":" («term_∈_» `p₂ "∈" `s)] [] ")")
        (Term.explicitBinder "(" [`hp₃] [":" («term_∈_» `p₃ "∈" `s)] [] ")")
        (Term.explicitBinder "(" [`hp₁p₂] [":" («term_≠_» `p₁ "≠" `p₂)] [] ")")
        (Term.explicitBinder "(" [`hp₁p₃] [":" («term_≠_» `p₁ "≠" `p₃)] [] ")")
        (Term.explicitBinder "(" [`hp₂p₃] [":" («term_≠_» `p₂ "≠" `p₃)] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Algebra.Group.Defs.«term_+ᵥ_»
          (Algebra.Group.Defs.«term_•_»
           («term_/_»
            («term_⁻¹»
             (Term.app
              `Real.Angle.tan
              [(Term.app
                (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
                [`p₁ `p₂ `p₃])])
             "⁻¹")
            "/"
            (num "2"))
           " • "
           (Term.app
            (Term.proj (EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo "o") "." `rotation)
            [(Term.typeAscription
              "("
              («term_/_»
               (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π")
               "/"
               (num "2"))
              ":"
              [(Data.Real.Basic.termℝ "ℝ")]
              ")")
             (Algebra.Group.Defs.«term_-ᵥ_» `p₃ " -ᵥ " `p₁)]))
          " +ᵥ "
          (Term.app `midpoint [(Data.Real.Basic.termℝ "ℝ") `p₁ `p₃]))
         "="
         (Term.proj `s "." `center))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(convert
            "convert"
            []
            (Term.app
             `tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center
             [`hp₁ `hp₃ `hp₁p₃])
            [])
           []
           (convert
            "convert"
            []
            (Term.proj
             (Term.app `Real.Angle.tan_eq_inv_of_two_zsmul_add_two_zsmul_eq_pi [(Term.hole "_")])
             "."
             `symm)
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `add_comm)
              ","
              (Tactic.rwRule
               []
               (Term.app
                `two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi
                [`hp₁ `hp₂ `hp₃ `hp₁p₂.symm `hp₂p₃ `hp₁p₃]))]
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
         [(convert
           "convert"
           []
           (Term.app
            `tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center
            [`hp₁ `hp₃ `hp₁p₃])
           [])
          []
          (convert
           "convert"
           []
           (Term.proj
            (Term.app `Real.Angle.tan_eq_inv_of_two_zsmul_add_two_zsmul_eq_pi [(Term.hole "_")])
            "."
            `symm)
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `add_comm)
             ","
             (Tactic.rwRule
              []
              (Term.app
               `two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi
               [`hp₁ `hp₂ `hp₃ `hp₁p₂.symm `hp₂p₃ `hp₁p₃]))]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `add_comm)
         ","
         (Tactic.rwRule
          []
          (Term.app
           `two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi
           [`hp₁ `hp₂ `hp₃ `hp₁p₂.symm `hp₂p₃ `hp₁p₃]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi
       [`hp₁ `hp₂ `hp₃ `hp₁p₂.symm `hp₂p₃ `hp₁p₃])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp₁p₃
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hp₂p₃
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hp₁p₂.symm
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hp₃
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hp₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hp₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert
       "convert"
       []
       (Term.proj
        (Term.app `Real.Angle.tan_eq_inv_of_two_zsmul_add_two_zsmul_eq_pi [(Term.hole "_")])
        "."
        `symm)
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app `Real.Angle.tan_eq_inv_of_two_zsmul_add_two_zsmul_eq_pi [(Term.hole "_")])
       "."
       `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Real.Angle.tan_eq_inv_of_two_zsmul_add_two_zsmul_eq_pi [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Real.Angle.tan_eq_inv_of_two_zsmul_add_two_zsmul_eq_pi
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Real.Angle.tan_eq_inv_of_two_zsmul_add_two_zsmul_eq_pi [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert
       "convert"
       []
       (Term.app `tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center [`hp₁ `hp₃ `hp₁p₃])
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center [`hp₁ `hp₃ `hp₁p₃])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp₁p₃
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hp₃
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hp₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Algebra.Group.Defs.«term_+ᵥ_»
        (Algebra.Group.Defs.«term_•_»
         («term_/_»
          («term_⁻¹»
           (Term.app
            `Real.Angle.tan
            [(Term.app
              (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
              [`p₁ `p₂ `p₃])])
           "⁻¹")
          "/"
          (num "2"))
         " • "
         (Term.app
          (Term.proj (EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo "o") "." `rotation)
          [(Term.typeAscription
            "("
            («term_/_»
             (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π")
             "/"
             (num "2"))
            ":"
            [(Data.Real.Basic.termℝ "ℝ")]
            ")")
           (Algebra.Group.Defs.«term_-ᵥ_» `p₃ " -ᵥ " `p₁)]))
        " +ᵥ "
        (Term.app `midpoint [(Data.Real.Basic.termℝ "ℝ") `p₁ `p₃]))
       "="
       (Term.proj `s "." `center))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `s "." `center)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Algebra.Group.Defs.«term_+ᵥ_»
       (Algebra.Group.Defs.«term_•_»
        («term_/_»
         («term_⁻¹»
          (Term.app
           `Real.Angle.tan
           [(Term.app
             (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
             [`p₁ `p₂ `p₃])])
          "⁻¹")
         "/"
         (num "2"))
        " • "
        (Term.app
         (Term.proj (EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo "o") "." `rotation)
         [(Term.typeAscription
           "("
           («term_/_»
            (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π")
            "/"
            (num "2"))
           ":"
           [(Data.Real.Basic.termℝ "ℝ")]
           ")")
          (Algebra.Group.Defs.«term_-ᵥ_» `p₃ " -ᵥ " `p₁)]))
       " +ᵥ "
       (Term.app `midpoint [(Data.Real.Basic.termℝ "ℝ") `p₁ `p₃]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `midpoint [(Data.Real.Basic.termℝ "ℝ") `p₁ `p₃])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p₃
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `midpoint
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Algebra.Group.Defs.«term_•_»
       («term_/_»
        («term_⁻¹»
         (Term.app
          `Real.Angle.tan
          [(Term.app
            (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
            [`p₁ `p₂ `p₃])])
         "⁻¹")
        "/"
        (num "2"))
       " • "
       (Term.app
        (Term.proj (EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo "o") "." `rotation)
        [(Term.typeAscription
          "("
          («term_/_» (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π") "/" (num "2"))
          ":"
          [(Data.Real.Basic.termℝ "ℝ")]
          ")")
         (Algebra.Group.Defs.«term_-ᵥ_» `p₃ " -ᵥ " `p₁)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo "o") "." `rotation)
       [(Term.typeAscription
         "("
         («term_/_» (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π") "/" (num "2"))
         ":"
         [(Data.Real.Basic.termℝ "ℝ")]
         ")")
        (Algebra.Group.Defs.«term_-ᵥ_» `p₃ " -ᵥ " `p₁)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_-ᵥ_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_-ᵥ_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_-ᵥ_» `p₃ " -ᵥ " `p₁)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p₁
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `p₃
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Group.Defs.«term_-ᵥ_» `p₃ " -ᵥ " `p₁)
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription
       "("
       («term_/_» (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π") "/" (num "2"))
       ":"
       [(Data.Real.Basic.termℝ "ℝ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π") "/" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo "o") "." `rotation)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo._@.Geometry.Euclidean.Angle.Sphere._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    Given three points on a circle, the center of that circle may be expressed explicitly as a
    multiple (by half the inverse of the tangent of the angle at one of those points) of a `π / 2`
    rotation of the vector between the other two points, plus the midpoint of those points. -/
  theorem
    inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center
    { s : Sphere P }
        { p₁ p₂ p₃ : P }
        ( hp₁ : p₁ ∈ s )
        ( hp₂ : p₂ ∈ s )
        ( hp₃ : p₃ ∈ s )
        ( hp₁p₂ : p₁ ≠ p₂ )
        ( hp₁p₃ : p₁ ≠ p₃ )
        ( hp₂p₃ : p₂ ≠ p₃ )
      :
        Real.Angle.tan ∡ p₁ p₂ p₃ ⁻¹ / 2 • o . rotation ( π / 2 : ℝ ) p₃ -ᵥ p₁ +ᵥ midpoint ℝ p₁ p₃
          =
          s . center
    :=
      by
        convert tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center hp₁ hp₃ hp₁p₃
          convert Real.Angle.tan_eq_inv_of_two_zsmul_add_two_zsmul_eq_pi _ . symm
          rw
            [
              add_comm
                ,
                two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi
                  hp₁ hp₂ hp₃ hp₁p₂.symm hp₂p₃ hp₁p₃
              ]
#align
  euclidean_geometry.sphere.inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center EuclideanGeometry.Sphere.inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Given two points on a circle, the radius of that circle may be expressed explicitly as half\nthe distance between those two points divided by the cosine of the angle between the chord and\nthe radius at one of those points. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `dist_div_cos_oangle_center_div_two_eq_radius [])
      (Command.declSig
       [(Term.implicitBinder "{" [`s] [":" (Term.app `Sphere [`P])] "}")
        (Term.implicitBinder "{" [`p₁ `p₂] [":" `P] "}")
        (Term.explicitBinder "(" [`hp₁] [":" («term_∈_» `p₁ "∈" `s)] [] ")")
        (Term.explicitBinder "(" [`hp₂] [":" («term_∈_» `p₂ "∈" `s)] [] ")")
        (Term.explicitBinder "(" [`h] [":" («term_≠_» `p₁ "≠" `p₂)] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_/_»
          («term_/_»
           (Term.app `dist [`p₁ `p₂])
           "/"
           (Term.app
            `Real.Angle.cos
            [(Term.app
              (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
              [`p₂ `p₁ (Term.proj `s "." `center)])]))
          "/"
          (num "2"))
         "="
         (Term.proj `s "." `radius))))
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
             [(Tactic.rwRule [] `div_right_comm)
              ","
              (Tactic.rwRule
               []
               (Term.app
                `div_eq_mul_inv
                [(Term.hole "_")
                 (Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")]))
              ","
              (Tactic.rwRule [] `mul_comm)
              ","
              (Tactic.rwRule
               []
               (Term.show
                "show"
                («term_=_»
                 («term_*_»
                  («term_⁻¹»
                   (Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                   "⁻¹")
                  "*"
                  (Term.app `dist [`p₁ `p₂]))
                 "="
                 (Term.app `dist [`p₁ (Term.app `midpoint [(Data.Real.Basic.termℝ "ℝ") `p₁ `p₂])]))
                (Term.byTactic'
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))))
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app (Term.proj `mem_sphere "." (fieldIdx "1")) [`hp₁]))
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app
                `tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center
                [`hp₁ `hp₂ `h]))
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `oangle_midpoint_rev_left)
              ","
              (Tactic.rwRule [] `oangle)
              ","
              (Tactic.rwRule [] `vadd_vsub_assoc)
              ","
              (Tactic.rwRule
               []
               (Term.show
                "show"
                («term_=_»
                 (Algebra.Group.Defs.«term_-ᵥ_» `p₂ " -ᵥ " `p₁)
                 "="
                 (Algebra.Group.Defs.«term_•_»
                  (Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                  " • "
                  (Algebra.Group.Defs.«term_-ᵥ_»
                   (Term.app `midpoint [(Data.Real.Basic.termℝ "ℝ") `p₁ `p₂])
                   " -ᵥ "
                   `p₁)))
                (Term.byTactic'
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))))
              ","
              (Tactic.rwRule [] `map_smul)
              ","
              (Tactic.rwRule [] `smul_smul)
              ","
              (Tactic.rwRule
               []
               (Term.app
                `div_mul_cancel
                [(Term.hole "_") (Term.app `two_ne_zero' [(Data.Real.Basic.termℝ "ℝ")])]))
              ","
              (Tactic.rwRule [] (Term.app (Term.explicit "@" `dist_eq_norm_vsub') [`V]))
              ","
              (Tactic.rwRule [] (Term.app (Term.explicit "@" `dist_eq_norm_vsub') [`V]))
              ","
              (Tactic.rwRule [] `vadd_vsub_assoc)
              ","
              (Tactic.rwRule [] `add_comm)
              ","
              (Tactic.rwRule
               []
               (Term.proj
                (EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo "o")
                "."
                `oangle_add_right_smul_rotation_pi_div_two))
              ","
              (Tactic.rwRule [] `Real.Angle.cos_coe)
              ","
              (Tactic.rwRule [] `Real.cos_arctan)
              ","
              (Tactic.rwRule [] `one_div)
              ","
              (Tactic.rwRule [] `div_inv_eq_mul)
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app
                `mul_self_inj
                [(Term.app
                  `mul_nonneg
                  [(Term.app `norm_nonneg [(Term.hole "_")])
                   (Term.app `Real.sqrt_nonneg [(Term.hole "_")])])
                 (Term.app `norm_nonneg [(Term.hole "_")])]))
              ","
              (Tactic.rwRule
               []
               (Term.app
                `norm_add_sq_eq_norm_sq_add_norm_sq_real
                [(Term.app
                  (Term.proj
                   (EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo "o")
                   "."
                   `inner_smul_rotation_pi_div_two_right)
                  [(Term.hole "_") (Term.hole "_")])]))
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)
              ","
              (Tactic.rwRule [] `mul_comm)
              ","
              (Tactic.rwRule
               []
               (Term.app `mul_comm [(Term.hole "_") (Term.app `Real.sqrt [(Term.hole "_")])]))
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)
              ","
              (Tactic.rwRule
               []
               (Term.app
                `Real.mul_self_sqrt
                [(Term.app `add_nonneg [`zero_le_one (Term.app `sq_nonneg [(Term.hole "_")])])]))
              ","
              (Tactic.rwRule [] `norm_smul)
              ","
              (Tactic.rwRule [] `LinearIsometryEquiv.norm_map)]
             "]")
            [])
           []
           (Mathlib.Tactic.tacticSwap "swap")
           ";"
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `h.symm]))])
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
                 [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)
                  ","
                  (Tactic.rwRule
                   []
                   (Term.app
                    `mul_comm
                    [(Term.hole "_")
                     (Analysis.Normed.Group.Basic.«term‖_‖»
                      "‖"
                      (Term.app `Real.Angle.tan [(Term.hole "_")])
                      "‖")]))
                  ","
                  (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)
                  ","
                  (Tactic.rwRule [] `Real.norm_eq_abs)
                  ","
                  (Tactic.rwRule [] `abs_mul_abs_self)]
                 "]"))])))
           []
           (Mathlib.Tactic.RingNF.ring "ring")])))
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
            [(Tactic.rwRule [] `div_right_comm)
             ","
             (Tactic.rwRule
              []
              (Term.app
               `div_eq_mul_inv
               [(Term.hole "_")
                (Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")]))
             ","
             (Tactic.rwRule [] `mul_comm)
             ","
             (Tactic.rwRule
              []
              (Term.show
               "show"
               («term_=_»
                («term_*_»
                 («term_⁻¹»
                  (Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                  "⁻¹")
                 "*"
                 (Term.app `dist [`p₁ `p₂]))
                "="
                (Term.app `dist [`p₁ (Term.app `midpoint [(Data.Real.Basic.termℝ "ℝ") `p₁ `p₂])]))
               (Term.byTactic'
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))))
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app (Term.proj `mem_sphere "." (fieldIdx "1")) [`hp₁]))
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app
               `tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center
               [`hp₁ `hp₂ `h]))
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `oangle_midpoint_rev_left)
             ","
             (Tactic.rwRule [] `oangle)
             ","
             (Tactic.rwRule [] `vadd_vsub_assoc)
             ","
             (Tactic.rwRule
              []
              (Term.show
               "show"
               («term_=_»
                (Algebra.Group.Defs.«term_-ᵥ_» `p₂ " -ᵥ " `p₁)
                "="
                (Algebra.Group.Defs.«term_•_»
                 (Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                 " • "
                 (Algebra.Group.Defs.«term_-ᵥ_»
                  (Term.app `midpoint [(Data.Real.Basic.termℝ "ℝ") `p₁ `p₂])
                  " -ᵥ "
                  `p₁)))
               (Term.byTactic'
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))))
             ","
             (Tactic.rwRule [] `map_smul)
             ","
             (Tactic.rwRule [] `smul_smul)
             ","
             (Tactic.rwRule
              []
              (Term.app
               `div_mul_cancel
               [(Term.hole "_") (Term.app `two_ne_zero' [(Data.Real.Basic.termℝ "ℝ")])]))
             ","
             (Tactic.rwRule [] (Term.app (Term.explicit "@" `dist_eq_norm_vsub') [`V]))
             ","
             (Tactic.rwRule [] (Term.app (Term.explicit "@" `dist_eq_norm_vsub') [`V]))
             ","
             (Tactic.rwRule [] `vadd_vsub_assoc)
             ","
             (Tactic.rwRule [] `add_comm)
             ","
             (Tactic.rwRule
              []
              (Term.proj
               (EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo "o")
               "."
               `oangle_add_right_smul_rotation_pi_div_two))
             ","
             (Tactic.rwRule [] `Real.Angle.cos_coe)
             ","
             (Tactic.rwRule [] `Real.cos_arctan)
             ","
             (Tactic.rwRule [] `one_div)
             ","
             (Tactic.rwRule [] `div_inv_eq_mul)
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app
               `mul_self_inj
               [(Term.app
                 `mul_nonneg
                 [(Term.app `norm_nonneg [(Term.hole "_")])
                  (Term.app `Real.sqrt_nonneg [(Term.hole "_")])])
                (Term.app `norm_nonneg [(Term.hole "_")])]))
             ","
             (Tactic.rwRule
              []
              (Term.app
               `norm_add_sq_eq_norm_sq_add_norm_sq_real
               [(Term.app
                 (Term.proj
                  (EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo "o")
                  "."
                  `inner_smul_rotation_pi_div_two_right)
                 [(Term.hole "_") (Term.hole "_")])]))
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)
             ","
             (Tactic.rwRule [] `mul_comm)
             ","
             (Tactic.rwRule
              []
              (Term.app `mul_comm [(Term.hole "_") (Term.app `Real.sqrt [(Term.hole "_")])]))
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)
             ","
             (Tactic.rwRule
              []
              (Term.app
               `Real.mul_self_sqrt
               [(Term.app `add_nonneg [`zero_le_one (Term.app `sq_nonneg [(Term.hole "_")])])]))
             ","
             (Tactic.rwRule [] `norm_smul)
             ","
             (Tactic.rwRule [] `LinearIsometryEquiv.norm_map)]
            "]")
           [])
          []
          (Mathlib.Tactic.tacticSwap "swap")
          ";"
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.Simpa.simpa
             "simpa"
             []
             []
             (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `h.symm]))])
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
                [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)
                 ","
                 (Tactic.rwRule
                  []
                  (Term.app
                   `mul_comm
                   [(Term.hole "_")
                    (Analysis.Normed.Group.Basic.«term‖_‖»
                     "‖"
                     (Term.app `Real.Angle.tan [(Term.hole "_")])
                     "‖")]))
                 ","
                 (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)
                 ","
                 (Tactic.rwRule [] `Real.norm_eq_abs)
                 ","
                 (Tactic.rwRule [] `abs_mul_abs_self)]
                "]"))])))
          []
          (Mathlib.Tactic.RingNF.ring "ring")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.RingNF.ring "ring")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
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
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)
             ","
             (Tactic.rwRule
              []
              (Term.app
               `mul_comm
               [(Term.hole "_")
                (Analysis.Normed.Group.Basic.«term‖_‖»
                 "‖"
                 (Term.app `Real.Angle.tan [(Term.hole "_")])
                 "‖")]))
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)
             ","
             (Tactic.rwRule [] `Real.norm_eq_abs)
             ","
             (Tactic.rwRule [] `abs_mul_abs_self)]
            "]"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convSeq1Indented', expected 'Lean.Parser.Tactic.Conv.convSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `abs_mul_abs_self
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Real.norm_eq_abs
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mul_comm
       [(Term.hole "_")
        (Analysis.Normed.Group.Basic.«term‖_‖»
         "‖"
         (Term.app `Real.Angle.tan [(Term.hole "_")])
         "‖")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term‖_‖»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term‖_‖»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `Real.Angle.tan [(Term.hole "_")]) "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Real.Angle.tan [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Real.Angle.tan
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.Simpa.simpa
         "simpa"
         []
         []
         (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `h.symm]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `h.symm]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h.symm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSwap "swap")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `div_right_comm)
         ","
         (Tactic.rwRule
          []
          (Term.app
           `div_eq_mul_inv
           [(Term.hole "_")
            (Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")]))
         ","
         (Tactic.rwRule [] `mul_comm)
         ","
         (Tactic.rwRule
          []
          (Term.show
           "show"
           («term_=_»
            («term_*_»
             («term_⁻¹»
              (Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
              "⁻¹")
             "*"
             (Term.app `dist [`p₁ `p₂]))
            "="
            (Term.app `dist [`p₁ (Term.app `midpoint [(Data.Real.Basic.termℝ "ℝ") `p₁ `p₂])]))
           (Term.byTactic'
            "by"
            (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))))
         ","
         (Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app (Term.proj `mem_sphere "." (fieldIdx "1")) [`hp₁]))
         ","
         (Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app `tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center [`hp₁ `hp₂ `h]))
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `oangle_midpoint_rev_left)
         ","
         (Tactic.rwRule [] `oangle)
         ","
         (Tactic.rwRule [] `vadd_vsub_assoc)
         ","
         (Tactic.rwRule
          []
          (Term.show
           "show"
           («term_=_»
            (Algebra.Group.Defs.«term_-ᵥ_» `p₂ " -ᵥ " `p₁)
            "="
            (Algebra.Group.Defs.«term_•_»
             (Term.typeAscription "(" (num "2") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
             " • "
             (Algebra.Group.Defs.«term_-ᵥ_»
              (Term.app `midpoint [(Data.Real.Basic.termℝ "ℝ") `p₁ `p₂])
              " -ᵥ "
              `p₁)))
           (Term.byTactic'
            "by"
            (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))))
         ","
         (Tactic.rwRule [] `map_smul)
         ","
         (Tactic.rwRule [] `smul_smul)
         ","
         (Tactic.rwRule
          []
          (Term.app
           `div_mul_cancel
           [(Term.hole "_") (Term.app `two_ne_zero' [(Data.Real.Basic.termℝ "ℝ")])]))
         ","
         (Tactic.rwRule [] (Term.app (Term.explicit "@" `dist_eq_norm_vsub') [`V]))
         ","
         (Tactic.rwRule [] (Term.app (Term.explicit "@" `dist_eq_norm_vsub') [`V]))
         ","
         (Tactic.rwRule [] `vadd_vsub_assoc)
         ","
         (Tactic.rwRule [] `add_comm)
         ","
         (Tactic.rwRule
          []
          (Term.proj
           (EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo "o")
           "."
           `oangle_add_right_smul_rotation_pi_div_two))
         ","
         (Tactic.rwRule [] `Real.Angle.cos_coe)
         ","
         (Tactic.rwRule [] `Real.cos_arctan)
         ","
         (Tactic.rwRule [] `one_div)
         ","
         (Tactic.rwRule [] `div_inv_eq_mul)
         ","
         (Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app
           `mul_self_inj
           [(Term.app
             `mul_nonneg
             [(Term.app `norm_nonneg [(Term.hole "_")])
              (Term.app `Real.sqrt_nonneg [(Term.hole "_")])])
            (Term.app `norm_nonneg [(Term.hole "_")])]))
         ","
         (Tactic.rwRule
          []
          (Term.app
           `norm_add_sq_eq_norm_sq_add_norm_sq_real
           [(Term.app
             (Term.proj
              (EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo "o")
              "."
              `inner_smul_rotation_pi_div_two_right)
             [(Term.hole "_") (Term.hole "_")])]))
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)
         ","
         (Tactic.rwRule [] `mul_comm)
         ","
         (Tactic.rwRule
          []
          (Term.app `mul_comm [(Term.hole "_") (Term.app `Real.sqrt [(Term.hole "_")])]))
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)
         ","
         (Tactic.rwRule
          []
          (Term.app
           `Real.mul_self_sqrt
           [(Term.app `add_nonneg [`zero_le_one (Term.app `sq_nonneg [(Term.hole "_")])])]))
         ","
         (Tactic.rwRule [] `norm_smul)
         ","
         (Tactic.rwRule [] `LinearIsometryEquiv.norm_map)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearIsometryEquiv.norm_map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Real.mul_self_sqrt
       [(Term.app `add_nonneg [`zero_le_one (Term.app `sq_nonneg [(Term.hole "_")])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `add_nonneg [`zero_le_one (Term.app `sq_nonneg [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `sq_nonneg [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sq_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `sq_nonneg [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `zero_le_one
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `add_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `add_nonneg
      [`zero_le_one (Term.paren "(" (Term.app `sq_nonneg [(Term.hole "_")]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Real.mul_self_sqrt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_comm [(Term.hole "_") (Term.app `Real.sqrt [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Real.sqrt [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Real.sqrt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Real.sqrt [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `norm_add_sq_eq_norm_sq_add_norm_sq_real
       [(Term.app
         (Term.proj
          (EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo "o")
          "."
          `inner_smul_rotation_pi_div_two_right)
         [(Term.hole "_") (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo "o")
        "."
        `inner_smul_rotation_pi_div_two_right)
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
       (EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo "o")
       "."
       `inner_smul_rotation_pi_div_two_right)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo', expected 'EuclideanGeometry.Geometry.Euclidean.Angle.Sphere.termo._@.Geometry.Euclidean.Angle.Sphere._hyg.9'
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
    Given two points on a circle, the radius of that circle may be expressed explicitly as half
    the distance between those two points divided by the cosine of the angle between the chord and
    the radius at one of those points. -/
  theorem
    dist_div_cos_oangle_center_div_two_eq_radius
    { s : Sphere P } { p₁ p₂ : P } ( hp₁ : p₁ ∈ s ) ( hp₂ : p₂ ∈ s ) ( h : p₁ ≠ p₂ )
      : dist p₁ p₂ / Real.Angle.cos ∡ p₂ p₁ s . center / 2 = s . radius
    :=
      by
        rw
            [
              div_right_comm
                ,
                div_eq_mul_inv _ ( 2 : ℝ )
                ,
                mul_comm
                ,
                show ( 2 : ℝ ) ⁻¹ * dist p₁ p₂ = dist p₁ midpoint ℝ p₁ p₂ by simp
                ,
                ← mem_sphere . 1 hp₁
                ,
                ← tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center hp₁ hp₂ h
                ,
                ← oangle_midpoint_rev_left
                ,
                oangle
                ,
                vadd_vsub_assoc
                ,
                show p₂ -ᵥ p₁ = ( 2 : ℝ ) • midpoint ℝ p₁ p₂ -ᵥ p₁ by simp
                ,
                map_smul
                ,
                smul_smul
                ,
                div_mul_cancel _ two_ne_zero' ℝ
                ,
                @ dist_eq_norm_vsub' V
                ,
                @ dist_eq_norm_vsub' V
                ,
                vadd_vsub_assoc
                ,
                add_comm
                ,
                o . oangle_add_right_smul_rotation_pi_div_two
                ,
                Real.Angle.cos_coe
                ,
                Real.cos_arctan
                ,
                one_div
                ,
                div_inv_eq_mul
                ,
                ← mul_self_inj mul_nonneg norm_nonneg _ Real.sqrt_nonneg _ norm_nonneg _
                ,
                norm_add_sq_eq_norm_sq_add_norm_sq_real o . inner_smul_rotation_pi_div_two_right _ _
                ,
                ← mul_assoc
                ,
                mul_comm
                ,
                mul_comm _ Real.sqrt _
                ,
                ← mul_assoc
                ,
                ← mul_assoc
                ,
                Real.mul_self_sqrt add_nonneg zero_le_one sq_nonneg _
                ,
                norm_smul
                ,
                LinearIsometryEquiv.norm_map
              ]
          swap
          ;
          · simpa using h.symm
          conv_rhs
            =>
            rw
              [
                ← mul_assoc
                  ,
                  mul_comm _ ‖ Real.Angle.tan _ ‖
                  ,
                  ← mul_assoc
                  ,
                  Real.norm_eq_abs
                  ,
                  abs_mul_abs_self
                ]
          ring
#align
  euclidean_geometry.sphere.dist_div_cos_oangle_center_div_two_eq_radius EuclideanGeometry.Sphere.dist_div_cos_oangle_center_div_two_eq_radius

/-- Given two points on a circle, twice the radius of that circle may be expressed explicitly as
the distance between those two points divided by the cosine of the angle between the chord and
the radius at one of those points. -/
theorem dist_div_cos_oangle_center_eq_two_mul_radius {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) (h : p₁ ≠ p₂) : dist p₁ p₂ / Real.Angle.cos (∡ p₂ p₁ s.center) = 2 * s.radius :=
  by
  rw [← dist_div_cos_oangle_center_div_two_eq_radius hp₁ hp₂ h, mul_div_cancel' _ (two_ne_zero' ℝ)]
#align
  euclidean_geometry.sphere.dist_div_cos_oangle_center_eq_two_mul_radius EuclideanGeometry.Sphere.dist_div_cos_oangle_center_eq_two_mul_radius

/-- Given three points on a circle, the radius of that circle may be expressed explicitly as half
the distance between two of those points divided by the absolute value of the sine of the angle
at the third point (a version of the law of sines or sine rule). -/
theorem dist_div_sin_oangle_div_two_eq_radius {s : Sphere P} {p₁ p₂ p₃ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) (hp₁p₂ : p₁ ≠ p₂) (hp₁p₃ : p₁ ≠ p₃) (hp₂p₃ : p₂ ≠ p₃) :
    dist p₁ p₃ / |Real.Angle.sin (∡ p₁ p₂ p₃)| / 2 = s.radius :=
  by
  convert dist_div_cos_oangle_center_div_two_eq_radius hp₁ hp₃ hp₁p₃
  rw [←
    Real.Angle.abs_cos_eq_abs_sin_of_two_zsmul_add_two_zsmul_eq_pi
      (two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi hp₁ hp₂ hp₃ hp₁p₂.symm hp₂p₃ hp₁p₃),
    _root_.abs_of_nonneg (Real.Angle.cos_nonneg_iff_abs_to_real_le_pi_div_two.2 _)]
  exact (abs_oangle_center_right_to_real_lt_pi_div_two hp₁ hp₃).le
#align
  euclidean_geometry.sphere.dist_div_sin_oangle_div_two_eq_radius EuclideanGeometry.Sphere.dist_div_sin_oangle_div_two_eq_radius

/-- Given three points on a circle, twice the radius of that circle may be expressed explicitly as
the distance between two of those points divided by the absolute value of the sine of the angle
at the third point (a version of the law of sines or sine rule). -/
theorem dist_div_sin_oangle_eq_two_mul_radius {s : Sphere P} {p₁ p₂ p₃ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) (hp₁p₂ : p₁ ≠ p₂) (hp₁p₃ : p₁ ≠ p₃) (hp₂p₃ : p₂ ≠ p₃) :
    dist p₁ p₃ / |Real.Angle.sin (∡ p₁ p₂ p₃)| = 2 * s.radius := by
  rw [← dist_div_sin_oangle_div_two_eq_radius hp₁ hp₂ hp₃ hp₁p₂ hp₁p₃ hp₂p₃,
    mul_div_cancel' _ (two_ne_zero' ℝ)]
#align
  euclidean_geometry.sphere.dist_div_sin_oangle_eq_two_mul_radius EuclideanGeometry.Sphere.dist_div_sin_oangle_eq_two_mul_radius

end Sphere

end EuclideanGeometry

namespace Affine

namespace Triangle

open EuclideanGeometry

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
        "The circumcenter of a triangle may be expressed explicitly as a multiple (by half the inverse\nof the tangent of the angle at one of the vertices) of a `π / 2` rotation of the vector between\nthe other two vertices, plus the midpoint of those vertices. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_circumcenter [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`t]
         [":" (Term.app `Triangle [(Data.Real.Basic.termℝ "ℝ") `P])]
         []
         ")")
        (Term.implicitBinder "{" [`i₁ `i₂ `i₃] [":" (Term.app `Fin [(num "3")])] "}")
        (Term.explicitBinder "(" [`h₁₂] [":" («term_≠_» `i₁ "≠" `i₂)] [] ")")
        (Term.explicitBinder "(" [`h₁₃] [":" («term_≠_» `i₁ "≠" `i₃)] [] ")")
        (Term.explicitBinder "(" [`h₂₃] [":" («term_≠_» `i₂ "≠" `i₃)] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Algebra.Group.Defs.«term_+ᵥ_»
          (Algebra.Group.Defs.«term_•_»
           («term_/_»
            («term_⁻¹»
             (Term.app
              `Real.Angle.tan
              [(Term.app
                (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
                [(Term.app (Term.proj `t "." `points) [`i₁])
                 (Term.app (Term.proj `t "." `points) [`i₂])
                 (Term.app (Term.proj `t "." `points) [`i₃])])])
             "⁻¹")
            "/"
            (num "2"))
           " • "
           (Term.app
            (Term.proj (Affine.Triangle.Geometry.Euclidean.Angle.Sphere.termo "o") "." `rotation)
            [(Term.typeAscription
              "("
              («term_/_»
               (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π")
               "/"
               (num "2"))
              ":"
              [(Data.Real.Basic.termℝ "ℝ")]
              ")")
             (Algebra.Group.Defs.«term_-ᵥ_»
              (Term.app (Term.proj `t "." `points) [`i₃])
              " -ᵥ "
              (Term.app (Term.proj `t "." `points) [`i₁]))]))
          " +ᵥ "
          (Term.app
           `midpoint
           [(Data.Real.Basic.termℝ "ℝ")
            (Term.app (Term.proj `t "." `points) [`i₁])
            (Term.app (Term.proj `t "." `points) [`i₃])]))
         "="
         (Term.proj `t "." `circumcenter))))
      (Command.declValSimple
       ":="
       (Term.app
        `Sphere.inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center
        [(Term.app (Term.proj `t "." `mem_circumsphere) [(Term.hole "_")])
         (Term.app (Term.proj `t "." `mem_circumsphere) [(Term.hole "_")])
         (Term.app (Term.proj `t "." `mem_circumsphere) [(Term.hole "_")])
         (Term.app
          (Term.proj (Term.proj (Term.proj `t "." `Independent) "." `Injective) "." `Ne)
          [`h₁₂])
         (Term.app
          (Term.proj (Term.proj (Term.proj `t "." `Independent) "." `Injective) "." `Ne)
          [`h₁₃])
         (Term.app
          (Term.proj (Term.proj (Term.proj `t "." `Independent) "." `Injective) "." `Ne)
          [`h₂₃])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Sphere.inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center
       [(Term.app (Term.proj `t "." `mem_circumsphere) [(Term.hole "_")])
        (Term.app (Term.proj `t "." `mem_circumsphere) [(Term.hole "_")])
        (Term.app (Term.proj `t "." `mem_circumsphere) [(Term.hole "_")])
        (Term.app
         (Term.proj (Term.proj (Term.proj `t "." `Independent) "." `Injective) "." `Ne)
         [`h₁₂])
        (Term.app
         (Term.proj (Term.proj (Term.proj `t "." `Independent) "." `Injective) "." `Ne)
         [`h₁₃])
        (Term.app
         (Term.proj (Term.proj (Term.proj `t "." `Independent) "." `Injective) "." `Ne)
         [`h₂₃])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.proj (Term.proj `t "." `Independent) "." `Injective) "." `Ne)
       [`h₂₃])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂₃
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj (Term.proj `t "." `Independent) "." `Injective) "." `Ne)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.proj `t "." `Independent) "." `Injective)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `t "." `Independent)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `t
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
      (Term.proj (Term.proj (Term.proj `t "." `Independent) "." `Injective) "." `Ne)
      [`h₂₃])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj (Term.proj (Term.proj `t "." `Independent) "." `Injective) "." `Ne)
       [`h₁₃])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁₃
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj (Term.proj `t "." `Independent) "." `Injective) "." `Ne)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.proj `t "." `Independent) "." `Injective)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `t "." `Independent)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.proj (Term.proj `t "." `Independent) "." `Injective) "." `Ne)
      [`h₁₃])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj (Term.proj (Term.proj `t "." `Independent) "." `Injective) "." `Ne)
       [`h₁₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj (Term.proj `t "." `Independent) "." `Injective) "." `Ne)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.proj `t "." `Independent) "." `Injective)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `t "." `Independent)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.proj (Term.proj `t "." `Independent) "." `Injective) "." `Ne)
      [`h₁₂])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `t "." `mem_circumsphere) [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `t "." `mem_circumsphere)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `t "." `mem_circumsphere) [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `t "." `mem_circumsphere) [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `t "." `mem_circumsphere)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `t "." `mem_circumsphere) [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `t "." `mem_circumsphere) [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `t "." `mem_circumsphere)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `t "." `mem_circumsphere) [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Sphere.inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Algebra.Group.Defs.«term_+ᵥ_»
        (Algebra.Group.Defs.«term_•_»
         («term_/_»
          («term_⁻¹»
           (Term.app
            `Real.Angle.tan
            [(Term.app
              (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
              [(Term.app (Term.proj `t "." `points) [`i₁])
               (Term.app (Term.proj `t "." `points) [`i₂])
               (Term.app (Term.proj `t "." `points) [`i₃])])])
           "⁻¹")
          "/"
          (num "2"))
         " • "
         (Term.app
          (Term.proj (Affine.Triangle.Geometry.Euclidean.Angle.Sphere.termo "o") "." `rotation)
          [(Term.typeAscription
            "("
            («term_/_»
             (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π")
             "/"
             (num "2"))
            ":"
            [(Data.Real.Basic.termℝ "ℝ")]
            ")")
           (Algebra.Group.Defs.«term_-ᵥ_»
            (Term.app (Term.proj `t "." `points) [`i₃])
            " -ᵥ "
            (Term.app (Term.proj `t "." `points) [`i₁]))]))
        " +ᵥ "
        (Term.app
         `midpoint
         [(Data.Real.Basic.termℝ "ℝ")
          (Term.app (Term.proj `t "." `points) [`i₁])
          (Term.app (Term.proj `t "." `points) [`i₃])]))
       "="
       (Term.proj `t "." `circumcenter))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `t "." `circumcenter)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Algebra.Group.Defs.«term_+ᵥ_»
       (Algebra.Group.Defs.«term_•_»
        («term_/_»
         («term_⁻¹»
          (Term.app
           `Real.Angle.tan
           [(Term.app
             (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
             [(Term.app (Term.proj `t "." `points) [`i₁])
              (Term.app (Term.proj `t "." `points) [`i₂])
              (Term.app (Term.proj `t "." `points) [`i₃])])])
          "⁻¹")
         "/"
         (num "2"))
        " • "
        (Term.app
         (Term.proj (Affine.Triangle.Geometry.Euclidean.Angle.Sphere.termo "o") "." `rotation)
         [(Term.typeAscription
           "("
           («term_/_»
            (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π")
            "/"
            (num "2"))
           ":"
           [(Data.Real.Basic.termℝ "ℝ")]
           ")")
          (Algebra.Group.Defs.«term_-ᵥ_»
           (Term.app (Term.proj `t "." `points) [`i₃])
           " -ᵥ "
           (Term.app (Term.proj `t "." `points) [`i₁]))]))
       " +ᵥ "
       (Term.app
        `midpoint
        [(Data.Real.Basic.termℝ "ℝ")
         (Term.app (Term.proj `t "." `points) [`i₁])
         (Term.app (Term.proj `t "." `points) [`i₃])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `midpoint
       [(Data.Real.Basic.termℝ "ℝ")
        (Term.app (Term.proj `t "." `points) [`i₁])
        (Term.app (Term.proj `t "." `points) [`i₃])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `t "." `points) [`i₃])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i₃
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `t "." `points)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `t "." `points) [`i₃])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `t "." `points) [`i₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `t "." `points)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `t "." `points) [`i₁])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `midpoint
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Algebra.Group.Defs.«term_•_»
       («term_/_»
        («term_⁻¹»
         (Term.app
          `Real.Angle.tan
          [(Term.app
            (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
            [(Term.app (Term.proj `t "." `points) [`i₁])
             (Term.app (Term.proj `t "." `points) [`i₂])
             (Term.app (Term.proj `t "." `points) [`i₃])])])
         "⁻¹")
        "/"
        (num "2"))
       " • "
       (Term.app
        (Term.proj (Affine.Triangle.Geometry.Euclidean.Angle.Sphere.termo "o") "." `rotation)
        [(Term.typeAscription
          "("
          («term_/_» (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π") "/" (num "2"))
          ":"
          [(Data.Real.Basic.termℝ "ℝ")]
          ")")
         (Algebra.Group.Defs.«term_-ᵥ_»
          (Term.app (Term.proj `t "." `points) [`i₃])
          " -ᵥ "
          (Term.app (Term.proj `t "." `points) [`i₁]))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Affine.Triangle.Geometry.Euclidean.Angle.Sphere.termo "o") "." `rotation)
       [(Term.typeAscription
         "("
         («term_/_» (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π") "/" (num "2"))
         ":"
         [(Data.Real.Basic.termℝ "ℝ")]
         ")")
        (Algebra.Group.Defs.«term_-ᵥ_»
         (Term.app (Term.proj `t "." `points) [`i₃])
         " -ᵥ "
         (Term.app (Term.proj `t "." `points) [`i₁]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_-ᵥ_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_-ᵥ_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_-ᵥ_»
       (Term.app (Term.proj `t "." `points) [`i₃])
       " -ᵥ "
       (Term.app (Term.proj `t "." `points) [`i₁]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `t "." `points) [`i₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `t "." `points)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app (Term.proj `t "." `points) [`i₃])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i₃
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `t "." `points)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Group.Defs.«term_-ᵥ_»
      (Term.app (Term.proj `t "." `points) [`i₃])
      " -ᵥ "
      (Term.app (Term.proj `t "." `points) [`i₁]))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription
       "("
       («term_/_» (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π") "/" (num "2"))
       ":"
       [(Data.Real.Basic.termℝ "ℝ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π") "/" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Affine.Triangle.Geometry.Euclidean.Angle.Sphere.termo "o") "." `rotation)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Affine.Triangle.Geometry.Euclidean.Angle.Sphere.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Affine.Triangle.Geometry.Euclidean.Angle.Sphere.termo', expected 'Affine.Triangle.Geometry.Euclidean.Angle.Sphere.termo._@.Geometry.Euclidean.Angle.Sphere._hyg.358'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The circumcenter of a triangle may be expressed explicitly as a multiple (by half the inverse
    of the tangent of the angle at one of the vertices) of a `π / 2` rotation of the vector between
    the other two vertices, plus the midpoint of those vertices. -/
  theorem
    inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_circumcenter
    ( t : Triangle ℝ P ) { i₁ i₂ i₃ : Fin 3 } ( h₁₂ : i₁ ≠ i₂ ) ( h₁₃ : i₁ ≠ i₃ ) ( h₂₃ : i₂ ≠ i₃ )
      :
        Real.Angle.tan ∡ t . points i₁ t . points i₂ t . points i₃ ⁻¹ / 2
              •
              o . rotation ( π / 2 : ℝ ) t . points i₃ -ᵥ t . points i₁
            +ᵥ
            midpoint ℝ t . points i₁ t . points i₃
          =
          t . circumcenter
    :=
      Sphere.inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center
        t . mem_circumsphere _
          t . mem_circumsphere _
          t . mem_circumsphere _
          t . Independent . Injective . Ne h₁₂
          t . Independent . Injective . Ne h₁₃
          t . Independent . Injective . Ne h₂₃
#align
  affine.triangle.inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_circumcenter Affine.Triangle.inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_circumcenter

/-- The circumradius of a triangle may be expressed explicitly as half the length of a side
divided by the absolute value of the sine of the angle at the third point (a version of the law
of sines or sine rule). -/
theorem dist_div_sin_oangle_div_two_eq_circumradius (t : Triangle ℝ P) {i₁ i₂ i₃ : Fin 3}
    (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    dist (t.points i₁) (t.points i₃) /
          |Real.Angle.sin (∡ (t.points i₁) (t.points i₂) (t.points i₃))| /
        2 =
      t.circumradius :=
  Sphere.dist_div_sin_oangle_div_two_eq_radius (t.mem_circumsphere _) (t.mem_circumsphere _)
    (t.mem_circumsphere _) (t.Independent.Injective.Ne h₁₂) (t.Independent.Injective.Ne h₁₃)
    (t.Independent.Injective.Ne h₂₃)
#align
  affine.triangle.dist_div_sin_oangle_div_two_eq_circumradius Affine.Triangle.dist_div_sin_oangle_div_two_eq_circumradius

/-- Twice the circumradius of a triangle may be expressed explicitly as the length of a side
divided by the absolute value of the sine of the angle at the third point (a version of the law
of sines or sine rule). -/
theorem dist_div_sin_oangle_eq_two_mul_circumradius (t : Triangle ℝ P) {i₁ i₂ i₃ : Fin 3}
    (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    dist (t.points i₁) (t.points i₃) /
        |Real.Angle.sin (∡ (t.points i₁) (t.points i₂) (t.points i₃))| =
      2 * t.circumradius :=
  Sphere.dist_div_sin_oangle_eq_two_mul_radius (t.mem_circumsphere _) (t.mem_circumsphere _)
    (t.mem_circumsphere _) (t.Independent.Injective.Ne h₁₂) (t.Independent.Injective.Ne h₁₃)
    (t.Independent.Injective.Ne h₂₃)
#align
  affine.triangle.dist_div_sin_oangle_eq_two_mul_circumradius Affine.Triangle.dist_div_sin_oangle_eq_two_mul_circumradius

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The circumsphere of a triangle may be expressed explicitly in terms of two points and the\nangle at the third point. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `circumsphere_eq_of_dist_of_oangle [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`t]
         [":" (Term.app `Triangle [(Data.Real.Basic.termℝ "ℝ") `P])]
         []
         ")")
        (Term.implicitBinder "{" [`i₁ `i₂ `i₃] [":" (Term.app `Fin [(num "3")])] "}")
        (Term.explicitBinder "(" [`h₁₂] [":" («term_≠_» `i₁ "≠" `i₂)] [] ")")
        (Term.explicitBinder "(" [`h₁₃] [":" («term_≠_» `i₁ "≠" `i₃)] [] ")")
        (Term.explicitBinder "(" [`h₂₃] [":" («term_≠_» `i₂ "≠" `i₃)] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.proj `t "." `circumsphere)
         "="
         (Term.anonymousCtor
          "⟨"
          [(Algebra.Group.Defs.«term_+ᵥ_»
            (Algebra.Group.Defs.«term_•_»
             («term_/_»
              («term_⁻¹»
               (Term.app
                `Real.Angle.tan
                [(Term.app
                  (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
                  [(Term.app (Term.proj `t "." `points) [`i₁])
                   (Term.app (Term.proj `t "." `points) [`i₂])
                   (Term.app (Term.proj `t "." `points) [`i₃])])])
               "⁻¹")
              "/"
              (num "2"))
             " • "
             (Term.app
              (Term.proj (Affine.Triangle.Geometry.Euclidean.Angle.Sphere.termo "o") "." `rotation)
              [(Term.typeAscription
                "("
                («term_/_»
                 (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π")
                 "/"
                 (num "2"))
                ":"
                [(Data.Real.Basic.termℝ "ℝ")]
                ")")
               (Algebra.Group.Defs.«term_-ᵥ_»
                (Term.app (Term.proj `t "." `points) [`i₃])
                " -ᵥ "
                (Term.app (Term.proj `t "." `points) [`i₁]))]))
            " +ᵥ "
            (Term.app
             `midpoint
             [(Data.Real.Basic.termℝ "ℝ")
              (Term.app (Term.proj `t "." `points) [`i₁])
              (Term.app (Term.proj `t "." `points) [`i₃])]))
           ","
           («term_/_»
            («term_/_»
             (Term.app
              `dist
              [(Term.app (Term.proj `t "." `points) [`i₁])
               (Term.app (Term.proj `t "." `points) [`i₃])])
             "/"
             («term|___|»
              (group "|")
              (Term.app
               `Real.Angle.sin
               [(Term.app
                 (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
                 [(Term.app (Term.proj `t "." `points) [`i₁])
                  (Term.app (Term.proj `t "." `points) [`i₂])
                  (Term.app (Term.proj `t "." `points) [`i₃])])])
              (group)
              "|"))
            "/"
            (num "2"))]
          "⟩"))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj (Term.proj `t "." `circumsphere) "." `ext)
        [(Term.hole "_")
         (Term.proj
          (Term.app
           (Term.proj
            `t
            "."
            `inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_circumcenter)
           [`h₁₂ `h₁₃ `h₂₃])
          "."
          `symm)
         (Term.proj
          (Term.app
           (Term.proj `t "." `dist_div_sin_oangle_div_two_eq_circumradius)
           [`h₁₂ `h₁₃ `h₂₃])
          "."
          `symm)])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.proj `t "." `circumsphere) "." `ext)
       [(Term.hole "_")
        (Term.proj
         (Term.app
          (Term.proj `t "." `inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_circumcenter)
          [`h₁₂ `h₁₃ `h₂₃])
         "."
         `symm)
        (Term.proj
         (Term.app (Term.proj `t "." `dist_div_sin_oangle_div_two_eq_circumradius) [`h₁₂ `h₁₃ `h₂₃])
         "."
         `symm)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app (Term.proj `t "." `dist_div_sin_oangle_div_two_eq_circumradius) [`h₁₂ `h₁₃ `h₂₃])
       "."
       `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `t "." `dist_div_sin_oangle_div_two_eq_circumradius) [`h₁₂ `h₁₃ `h₂₃])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂₃
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₁₃
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₁₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `t "." `dist_div_sin_oangle_div_two_eq_circumradius)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `t "." `dist_div_sin_oangle_div_two_eq_circumradius) [`h₁₂ `h₁₃ `h₂₃])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.app
        (Term.proj `t "." `inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_circumcenter)
        [`h₁₂ `h₁₃ `h₂₃])
       "."
       `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj `t "." `inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_circumcenter)
       [`h₁₂ `h₁₃ `h₂₃])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂₃
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₁₃
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₁₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `t "." `inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_circumcenter)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj `t "." `inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_circumcenter)
      [`h₁₂ `h₁₃ `h₂₃])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj `t "." `circumsphere) "." `ext)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `t "." `circumsphere)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.proj `t "." `circumsphere)
       "="
       (Term.anonymousCtor
        "⟨"
        [(Algebra.Group.Defs.«term_+ᵥ_»
          (Algebra.Group.Defs.«term_•_»
           («term_/_»
            («term_⁻¹»
             (Term.app
              `Real.Angle.tan
              [(Term.app
                (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
                [(Term.app (Term.proj `t "." `points) [`i₁])
                 (Term.app (Term.proj `t "." `points) [`i₂])
                 (Term.app (Term.proj `t "." `points) [`i₃])])])
             "⁻¹")
            "/"
            (num "2"))
           " • "
           (Term.app
            (Term.proj (Affine.Triangle.Geometry.Euclidean.Angle.Sphere.termo "o") "." `rotation)
            [(Term.typeAscription
              "("
              («term_/_»
               (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π")
               "/"
               (num "2"))
              ":"
              [(Data.Real.Basic.termℝ "ℝ")]
              ")")
             (Algebra.Group.Defs.«term_-ᵥ_»
              (Term.app (Term.proj `t "." `points) [`i₃])
              " -ᵥ "
              (Term.app (Term.proj `t "." `points) [`i₁]))]))
          " +ᵥ "
          (Term.app
           `midpoint
           [(Data.Real.Basic.termℝ "ℝ")
            (Term.app (Term.proj `t "." `points) [`i₁])
            (Term.app (Term.proj `t "." `points) [`i₃])]))
         ","
         («term_/_»
          («term_/_»
           (Term.app
            `dist
            [(Term.app (Term.proj `t "." `points) [`i₁])
             (Term.app (Term.proj `t "." `points) [`i₃])])
           "/"
           («term|___|»
            (group "|")
            (Term.app
             `Real.Angle.sin
             [(Term.app
               (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
               [(Term.app (Term.proj `t "." `points) [`i₁])
                (Term.app (Term.proj `t "." `points) [`i₂])
                (Term.app (Term.proj `t "." `points) [`i₃])])])
            (group)
            "|"))
          "/"
          (num "2"))]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Algebra.Group.Defs.«term_+ᵥ_»
         (Algebra.Group.Defs.«term_•_»
          («term_/_»
           («term_⁻¹»
            (Term.app
             `Real.Angle.tan
             [(Term.app
               (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
               [(Term.app (Term.proj `t "." `points) [`i₁])
                (Term.app (Term.proj `t "." `points) [`i₂])
                (Term.app (Term.proj `t "." `points) [`i₃])])])
            "⁻¹")
           "/"
           (num "2"))
          " • "
          (Term.app
           (Term.proj (Affine.Triangle.Geometry.Euclidean.Angle.Sphere.termo "o") "." `rotation)
           [(Term.typeAscription
             "("
             («term_/_»
              (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π")
              "/"
              (num "2"))
             ":"
             [(Data.Real.Basic.termℝ "ℝ")]
             ")")
            (Algebra.Group.Defs.«term_-ᵥ_»
             (Term.app (Term.proj `t "." `points) [`i₃])
             " -ᵥ "
             (Term.app (Term.proj `t "." `points) [`i₁]))]))
         " +ᵥ "
         (Term.app
          `midpoint
          [(Data.Real.Basic.termℝ "ℝ")
           (Term.app (Term.proj `t "." `points) [`i₁])
           (Term.app (Term.proj `t "." `points) [`i₃])]))
        ","
        («term_/_»
         («term_/_»
          (Term.app
           `dist
           [(Term.app (Term.proj `t "." `points) [`i₁])
            (Term.app (Term.proj `t "." `points) [`i₃])])
          "/"
          («term|___|»
           (group "|")
           (Term.app
            `Real.Angle.sin
            [(Term.app
              (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
              [(Term.app (Term.proj `t "." `points) [`i₁])
               (Term.app (Term.proj `t "." `points) [`i₂])
               (Term.app (Term.proj `t "." `points) [`i₃])])])
           (group)
           "|"))
         "/"
         (num "2"))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_»
       («term_/_»
        (Term.app
         `dist
         [(Term.app (Term.proj `t "." `points) [`i₁]) (Term.app (Term.proj `t "." `points) [`i₃])])
        "/"
        («term|___|»
         (group "|")
         (Term.app
          `Real.Angle.sin
          [(Term.app
            (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
            [(Term.app (Term.proj `t "." `points) [`i₁])
             (Term.app (Term.proj `t "." `points) [`i₂])
             (Term.app (Term.proj `t "." `points) [`i₃])])])
         (group)
         "|"))
       "/"
       (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_/_»
       (Term.app
        `dist
        [(Term.app (Term.proj `t "." `points) [`i₁]) (Term.app (Term.proj `t "." `points) [`i₃])])
       "/"
       («term|___|»
        (group "|")
        (Term.app
         `Real.Angle.sin
         [(Term.app
           (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
           [(Term.app (Term.proj `t "." `points) [`i₁])
            (Term.app (Term.proj `t "." `points) [`i₂])
            (Term.app (Term.proj `t "." `points) [`i₃])])])
        (group)
        "|"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term|___|»
       (group "|")
       (Term.app
        `Real.Angle.sin
        [(Term.app
          (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
          [(Term.app (Term.proj `t "." `points) [`i₁])
           (Term.app (Term.proj `t "." `points) [`i₂])
           (Term.app (Term.proj `t "." `points) [`i₃])])])
       (group)
       "|")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Real.Angle.sin
       [(Term.app
         (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
         [(Term.app (Term.proj `t "." `points) [`i₁])
          (Term.app (Term.proj `t "." `points) [`i₂])
          (Term.app (Term.proj `t "." `points) [`i₃])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
       [(Term.app (Term.proj `t "." `points) [`i₁])
        (Term.app (Term.proj `t "." `points) [`i₂])
        (Term.app (Term.proj `t "." `points) [`i₃])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `t "." `points) [`i₃])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i₃
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `t "." `points)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `t "." `points) [`i₃])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `t "." `points) [`i₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `t "." `points)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `t "." `points) [`i₂])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `t "." `points) [`i₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `t "." `points)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `t "." `points) [`i₁])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
      [(Term.paren "(" (Term.app (Term.proj `t "." `points) [`i₁]) ")")
       (Term.paren "(" (Term.app (Term.proj `t "." `points) [`i₂]) ")")
       (Term.paren "(" (Term.app (Term.proj `t "." `points) [`i₃]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Real.Angle.sin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app
       `dist
       [(Term.app (Term.proj `t "." `points) [`i₁]) (Term.app (Term.proj `t "." `points) [`i₃])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `t "." `points) [`i₃])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i₃
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `t "." `points)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `t "." `points) [`i₃])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `t "." `points) [`i₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `t "." `points)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `t "." `points) [`i₁])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dist
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_+ᵥ_»
       (Algebra.Group.Defs.«term_•_»
        («term_/_»
         («term_⁻¹»
          (Term.app
           `Real.Angle.tan
           [(Term.app
             (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
             [(Term.app (Term.proj `t "." `points) [`i₁])
              (Term.app (Term.proj `t "." `points) [`i₂])
              (Term.app (Term.proj `t "." `points) [`i₃])])])
          "⁻¹")
         "/"
         (num "2"))
        " • "
        (Term.app
         (Term.proj (Affine.Triangle.Geometry.Euclidean.Angle.Sphere.termo "o") "." `rotation)
         [(Term.typeAscription
           "("
           («term_/_»
            (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π")
            "/"
            (num "2"))
           ":"
           [(Data.Real.Basic.termℝ "ℝ")]
           ")")
          (Algebra.Group.Defs.«term_-ᵥ_»
           (Term.app (Term.proj `t "." `points) [`i₃])
           " -ᵥ "
           (Term.app (Term.proj `t "." `points) [`i₁]))]))
       " +ᵥ "
       (Term.app
        `midpoint
        [(Data.Real.Basic.termℝ "ℝ")
         (Term.app (Term.proj `t "." `points) [`i₁])
         (Term.app (Term.proj `t "." `points) [`i₃])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `midpoint
       [(Data.Real.Basic.termℝ "ℝ")
        (Term.app (Term.proj `t "." `points) [`i₁])
        (Term.app (Term.proj `t "." `points) [`i₃])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `t "." `points) [`i₃])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i₃
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `t "." `points)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `t "." `points) [`i₃])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `t "." `points) [`i₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `t "." `points)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `t "." `points) [`i₁])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `midpoint
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Algebra.Group.Defs.«term_•_»
       («term_/_»
        («term_⁻¹»
         (Term.app
          `Real.Angle.tan
          [(Term.app
            (EuclideanGeometry.Geometry.Euclidean.Angle.Oriented.Affine.oangle "∡")
            [(Term.app (Term.proj `t "." `points) [`i₁])
             (Term.app (Term.proj `t "." `points) [`i₂])
             (Term.app (Term.proj `t "." `points) [`i₃])])])
         "⁻¹")
        "/"
        (num "2"))
       " • "
       (Term.app
        (Term.proj (Affine.Triangle.Geometry.Euclidean.Angle.Sphere.termo "o") "." `rotation)
        [(Term.typeAscription
          "("
          («term_/_» (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π") "/" (num "2"))
          ":"
          [(Data.Real.Basic.termℝ "ℝ")]
          ")")
         (Algebra.Group.Defs.«term_-ᵥ_»
          (Term.app (Term.proj `t "." `points) [`i₃])
          " -ᵥ "
          (Term.app (Term.proj `t "." `points) [`i₁]))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Affine.Triangle.Geometry.Euclidean.Angle.Sphere.termo "o") "." `rotation)
       [(Term.typeAscription
         "("
         («term_/_» (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π") "/" (num "2"))
         ":"
         [(Data.Real.Basic.termℝ "ℝ")]
         ")")
        (Algebra.Group.Defs.«term_-ᵥ_»
         (Term.app (Term.proj `t "." `points) [`i₃])
         " -ᵥ "
         (Term.app (Term.proj `t "." `points) [`i₁]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_-ᵥ_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_-ᵥ_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_-ᵥ_»
       (Term.app (Term.proj `t "." `points) [`i₃])
       " -ᵥ "
       (Term.app (Term.proj `t "." `points) [`i₁]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `t "." `points) [`i₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `t "." `points)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app (Term.proj `t "." `points) [`i₃])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i₃
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `t "." `points)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `t
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Group.Defs.«term_-ᵥ_»
      (Term.app (Term.proj `t "." `points) [`i₃])
      " -ᵥ "
      (Term.app (Term.proj `t "." `points) [`i₁]))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription
       "("
       («term_/_» (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π") "/" (num "2"))
       ":"
       [(Data.Real.Basic.termℝ "ℝ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π") "/" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Real.Analysis.SpecialFunctions.Trigonometric.Basic.real.pi "π")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Affine.Triangle.Geometry.Euclidean.Angle.Sphere.termo "o") "." `rotation)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Affine.Triangle.Geometry.Euclidean.Angle.Sphere.termo "o")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Affine.Triangle.Geometry.Euclidean.Angle.Sphere.termo', expected 'Affine.Triangle.Geometry.Euclidean.Angle.Sphere.termo._@.Geometry.Euclidean.Angle.Sphere._hyg.358'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The circumsphere of a triangle may be expressed explicitly in terms of two points and the
    angle at the third point. -/
  theorem
    circumsphere_eq_of_dist_of_oangle
    ( t : Triangle ℝ P ) { i₁ i₂ i₃ : Fin 3 } ( h₁₂ : i₁ ≠ i₂ ) ( h₁₃ : i₁ ≠ i₃ ) ( h₂₃ : i₂ ≠ i₃ )
      :
        t . circumsphere
          =
          ⟨
            Real.Angle.tan ∡ t . points i₁ t . points i₂ t . points i₃ ⁻¹ / 2
                  •
                  o . rotation ( π / 2 : ℝ ) t . points i₃ -ᵥ t . points i₁
                +ᵥ
                midpoint ℝ t . points i₁ t . points i₃
              ,
              dist t . points i₁ t . points i₃
                  /
                  | Real.Angle.sin ∡ t . points i₁ t . points i₂ t . points i₃ |
                /
                2
            ⟩
    :=
      t . circumsphere . ext
        _
          t . inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_circumcenter h₁₂ h₁₃ h₂₃
            .
            symm
          t . dist_div_sin_oangle_div_two_eq_circumradius h₁₂ h₁₃ h₂₃ . symm
#align
  affine.triangle.circumsphere_eq_of_dist_of_oangle Affine.Triangle.circumsphere_eq_of_dist_of_oangle

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr ⟨«expr +ᵥ »(«expr • »(«expr / »(«expr ⁻¹»((_ : exprℝ())), 2), _), _), «expr / »(«expr / »(_, _), 2)⟩]] -/
/-- If two triangles have two points the same, and twice the angle at the third point the same,
they have the same circumsphere. -/
theorem circumsphere_eq_circumsphere_of_eq_of_eq_of_two_zsmul_oangle_eq {t₁ t₂ : Triangle ℝ P}
    {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃)
    (h₁ : t₁.points i₁ = t₂.points i₁) (h₃ : t₁.points i₃ = t₂.points i₃)
    (h₂ :
      (2 : ℤ) • ∡ (t₁.points i₁) (t₁.points i₂) (t₁.points i₃) =
        (2 : ℤ) • ∡ (t₂.points i₁) (t₂.points i₂) (t₂.points i₃)) :
    t₁.circumsphere = t₂.circumsphere :=
  by
  rw [t₁.circumsphere_eq_of_dist_of_oangle h₁₂ h₁₃ h₂₃,
    t₂.circumsphere_eq_of_dist_of_oangle h₁₂ h₁₃ h₂₃]
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `congrm #[[expr ⟨«expr +ᵥ »(«expr • »(«expr / »(«expr ⁻¹»((_ : exprℝ())), 2), _), _), «expr / »(«expr / »(_, _), 2)⟩]]"
  · exact Real.Angle.tan_eq_of_two_zsmul_eq h₂
  · rw [h₁, h₃]
  · rw [h₁, h₃]
  · rw [h₁, h₃]
  · exact Real.Angle.abs_sin_eq_of_two_zsmul_eq h₂
#align
  affine.triangle.circumsphere_eq_circumsphere_of_eq_of_eq_of_two_zsmul_oangle_eq Affine.Triangle.circumsphere_eq_circumsphere_of_eq_of_eq_of_two_zsmul_oangle_eq

/-- Given a triangle, and a fourth point such that twice the angle between two points of the
triangle at that fourth point equals twice the third angle of the triangle, the fourth point
lies in the circumsphere of the triangle. -/
theorem mem_circumsphere_of_two_zsmul_oangle_eq {t : Triangle ℝ P} {p : P} {i₁ i₂ i₃ : Fin 3}
    (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃)
    (h :
      (2 : ℤ) • ∡ (t.points i₁) p (t.points i₃) =
        (2 : ℤ) • ∡ (t.points i₁) (t.points i₂) (t.points i₃)) :
    p ∈ t.circumsphere :=
  by
  let t'p : Fin 3 → P := Function.update t.points i₂ p
  have h₁ : t'p i₁ = t.points i₁ := by simp [t'p, h₁₂]
  have h₂ : t'p i₂ = p := by simp [t'p]
  have h₃ : t'p i₃ = t.points i₃ := by simp [t'p, h₂₃.symm]
  have ha : AffineIndependent ℝ t'p :=
    by
    rw [affine_independent_iff_not_collinear_of_ne h₁₂ h₁₃ h₂₃, h₁, h₂, h₃,
      collinear_iff_of_two_zsmul_oangle_eq h, ←
      affine_independent_iff_not_collinear_of_ne h₁₂ h₁₃ h₂₃]
    exact t.independent
  let t' : triangle ℝ P := ⟨t'p, ha⟩
  have h₁' : t'.points i₁ = t.points i₁ := h₁
  have h₂' : t'.points i₂ = p := h₂
  have h₃' : t'.points i₃ = t.points i₃ := h₃
  have h' :
    (2 : ℤ) • ∡ (t'.points i₁) (t'.points i₂) (t'.points i₃) =
      (2 : ℤ) • ∡ (t.points i₁) (t.points i₂) (t.points i₃) :=
    by rwa [h₁', h₂', h₃']
  rw [← circumsphere_eq_circumsphere_of_eq_of_eq_of_two_zsmul_oangle_eq h₁₂ h₁₃ h₂₃ h₁' h₃' h', ←
    h₂']
  exact simplex.mem_circumsphere _ _
#align
  affine.triangle.mem_circumsphere_of_two_zsmul_oangle_eq Affine.Triangle.mem_circumsphere_of_two_zsmul_oangle_eq

end Triangle

end Affine

namespace EuclideanGeometry

variable {V : Type _} {P : Type _} [InnerProductSpace ℝ V] [MetricSpace P]

variable [NormedAddTorsor V P] [hd2 : Fact (finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

include hd2

-- mathport name: expro
local notation "o" => Module.Oriented.positiveOrientation

/-- Converse of "angles in same segment are equal" and "opposite angles of a cyclic quadrilateral
add to π", for oriented angles mod π. -/
theorem cospherical_of_two_zsmul_oangle_eq_of_not_collinear {p₁ p₂ p₃ p₄ : P}
    (h : (2 : ℤ) • ∡ p₁ p₂ p₄ = (2 : ℤ) • ∡ p₁ p₃ p₄) (hn : ¬Collinear ℝ ({p₁, p₂, p₄} : Set P)) :
    Cospherical ({p₁, p₂, p₃, p₄} : Set P) :=
  by
  have hn' : ¬Collinear ℝ ({p₁, p₃, p₄} : Set P) := by
    rwa [← collinear_iff_of_two_zsmul_oangle_eq h]
  let t₁ : Affine.Triangle ℝ P := ⟨![p₁, p₂, p₄], affine_independent_iff_not_collinear_set.2 hn⟩
  let t₂ : Affine.Triangle ℝ P := ⟨![p₁, p₃, p₄], affine_independent_iff_not_collinear_set.2 hn'⟩
  rw [cospherical_iff_exists_sphere]
  refine' ⟨t₂.circumsphere, _⟩
  simp_rw [Set.insert_subset, Set.singleton_subset_iff]
  refine' ⟨t₂.mem_circumsphere 0, _, t₂.mem_circumsphere 1, t₂.mem_circumsphere 2⟩
  rw [Affine.Triangle.circumsphere_eq_circumsphere_of_eq_of_eq_of_two_zsmul_oangle_eq
      (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2) (by decide)
      (show t₂.points 0 = t₁.points 0 from rfl) rfl h.symm]
  exact t₁.mem_circumsphere 1
#align
  euclidean_geometry.cospherical_of_two_zsmul_oangle_eq_of_not_collinear EuclideanGeometry.cospherical_of_two_zsmul_oangle_eq_of_not_collinear

/-- Converse of "angles in same segment are equal" and "opposite angles of a cyclic quadrilateral
add to π", for oriented angles mod π, with a "concyclic" conclusion. -/
theorem concyclicOfTwoZsmulOangleEqOfNotCollinear {p₁ p₂ p₃ p₄ : P}
    (h : (2 : ℤ) • ∡ p₁ p₂ p₄ = (2 : ℤ) • ∡ p₁ p₃ p₄) (hn : ¬Collinear ℝ ({p₁, p₂, p₄} : Set P)) :
    Concyclic ({p₁, p₂, p₃, p₄} : Set P) :=
  ⟨cospherical_of_two_zsmul_oangle_eq_of_not_collinear h hn, coplanar_of_fact_finrank_eq_two _⟩
#align
  euclidean_geometry.concyclic_of_two_zsmul_oangle_eq_of_not_collinear EuclideanGeometry.concyclicOfTwoZsmulOangleEqOfNotCollinear

/-- Converse of "angles in same segment are equal" and "opposite angles of a cyclic quadrilateral
add to π", for oriented angles mod π, with a "cospherical or collinear" conclusion. -/
theorem cospherical_or_collinear_of_two_zsmul_oangle_eq {p₁ p₂ p₃ p₄ : P}
    (h : (2 : ℤ) • ∡ p₁ p₂ p₄ = (2 : ℤ) • ∡ p₁ p₃ p₄) :
    Cospherical ({p₁, p₂, p₃, p₄} : Set P) ∨ Collinear ℝ ({p₁, p₂, p₃, p₄} : Set P) :=
  by
  by_cases hc : Collinear ℝ ({p₁, p₂, p₄} : Set P)
  · by_cases he : p₁ = p₄
    · rw [he,
        Set.insert_eq_self.2
          (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))]
      by_cases hl : Collinear ℝ ({p₂, p₃, p₄} : Set P)
      · exact Or.inr hl
      rw [or_iff_left hl]
      let t : Affine.Triangle ℝ P := ⟨![p₂, p₃, p₄], affine_independent_iff_not_collinear_set.2 hl⟩
      rw [cospherical_iff_exists_sphere]
      refine' ⟨t.circumsphere, _⟩
      simp_rw [Set.insert_subset, Set.singleton_subset_iff]
      exact ⟨t.mem_circumsphere 0, t.mem_circumsphere 1, t.mem_circumsphere 2⟩
    have hc' : Collinear ℝ ({p₁, p₃, p₄} : Set P) := by
      rwa [← collinear_iff_of_two_zsmul_oangle_eq h]
    refine' Or.inr _
    rw [Set.insert_comm p₁ p₂] at hc
    rwa [Set.insert_comm p₁ p₂,
      hc'.collinear_insert_iff_of_ne (Set.mem_insert _ _)
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) he]
  · exact Or.inl (cospherical_of_two_zsmul_oangle_eq_of_not_collinear h hc)
#align
  euclidean_geometry.cospherical_or_collinear_of_two_zsmul_oangle_eq EuclideanGeometry.cospherical_or_collinear_of_two_zsmul_oangle_eq

/-- Converse of "angles in same segment are equal" and "opposite angles of a cyclic quadrilateral
add to π", for oriented angles mod π, with a "concyclic or collinear" conclusion. -/
theorem concyclic_or_collinear_of_two_zsmul_oangle_eq {p₁ p₂ p₃ p₄ : P}
    (h : (2 : ℤ) • ∡ p₁ p₂ p₄ = (2 : ℤ) • ∡ p₁ p₃ p₄) :
    Concyclic ({p₁, p₂, p₃, p₄} : Set P) ∨ Collinear ℝ ({p₁, p₂, p₃, p₄} : Set P) :=
  by
  rcases cospherical_or_collinear_of_two_zsmul_oangle_eq h with (hc | hc)
  · exact Or.inl ⟨hc, coplanar_of_fact_finrank_eq_two _⟩
  · exact Or.inr hc
#align
  euclidean_geometry.concyclic_or_collinear_of_two_zsmul_oangle_eq EuclideanGeometry.concyclic_or_collinear_of_two_zsmul_oangle_eq

end EuclideanGeometry

