/-
Copyright (c) 2021 Alex Kontorovich and Heather Macbeth and Marc Masdeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth, Marc Masdeu

! This file was ported from Lean 3 source module analysis.complex.upper_half_plane.basic
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Parity
import Mathbin.LinearAlgebra.SpecialLinearGroup
import Mathbin.Analysis.Complex.Basic
import Mathbin.GroupTheory.GroupAction.Defs
import Mathbin.LinearAlgebra.GeneralLinearGroup

/-!
# The upper half plane and its automorphisms

This file defines `upper_half_plane` to be the upper half plane in `ℂ`.

We furthermore equip it with the structure of an `GL_pos 2 ℝ` action by
fractional linear transformations.

We define the notation `ℍ` for the upper half plane available in the locale
`upper_half_plane` so as not to conflict with the quaternions.
-/


noncomputable section

open Matrix Matrix.SpecialLinearGroup

open Classical BigOperators MatrixGroups

attribute [local instance] Fintype.card_fin_even

/- Disable this instances as it is not the simp-normal form, and having them disabled ensures
we state lemmas in this file without spurious `coe_fn` terms. -/
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToFun

-- mathport name: «expr↑ₘ »
local prefix:1024 "↑ₘ" => @coe _ (Matrix (Fin 2) (Fin 2) _) _

-- mathport name: «exprGL( , )⁺»
local notation "GL(" n ", " R ")" "⁺" => Matrix.gLPos (Fin n) R

/- ./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler λ α,
has_coe[has_coe] α exprℂ() -/
/-- The open upper half plane -/
def UpperHalfPlane :=
  { point : ℂ // 0 < point.im }deriving
  «./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler λ α,
  has_coe[has_coe] α exprℂ()»
#align upper_half_plane UpperHalfPlane

-- mathport name: upper_half_plane
scoped[UpperHalfPlane] notation "ℍ" => UpperHalfPlane

namespace UpperHalfPlane

instance : Inhabited ℍ :=
  ⟨⟨Complex.i, by simp⟩⟩

instance canLift : CanLift ℂ ℍ coe fun z => 0 < z.im :=
  Subtype.canLift fun z => 0 < z.im
#align upper_half_plane.can_lift UpperHalfPlane.canLift

/-- Imaginary part -/
def im (z : ℍ) :=
  (z : ℂ).im
#align upper_half_plane.im UpperHalfPlane.im

/-- Real part -/
def re (z : ℍ) :=
  (z : ℂ).re
#align upper_half_plane.re UpperHalfPlane.re

/-- Constructor for `upper_half_plane`. It is useful if `⟨z, h⟩` makes Lean use a wrong
typeclass instance. -/
def mk (z : ℂ) (h : 0 < z.im) : ℍ :=
  ⟨z, h⟩
#align upper_half_plane.mk UpperHalfPlane.mk

@[simp]
theorem coe_im (z : ℍ) : (z : ℂ).im = z.im :=
  rfl
#align upper_half_plane.coe_im UpperHalfPlane.coe_im

@[simp]
theorem coe_re (z : ℍ) : (z : ℂ).re = z.re :=
  rfl
#align upper_half_plane.coe_re UpperHalfPlane.coe_re

@[simp]
theorem mk_re (z : ℂ) (h : 0 < z.im) : (mk z h).re = z.re :=
  rfl
#align upper_half_plane.mk_re UpperHalfPlane.mk_re

@[simp]
theorem mk_im (z : ℂ) (h : 0 < z.im) : (mk z h).im = z.im :=
  rfl
#align upper_half_plane.mk_im UpperHalfPlane.mk_im

@[simp]
theorem coe_mk (z : ℂ) (h : 0 < z.im) : (mk z h : ℂ) = z :=
  rfl
#align upper_half_plane.coe_mk UpperHalfPlane.coe_mk

@[simp]
theorem mk_coe (z : ℍ) (h : 0 < (z : ℂ).im := z.2) : mk z h = z :=
  Subtype.eta z h
#align upper_half_plane.mk_coe UpperHalfPlane.mk_coe

theorem re_add_im (z : ℍ) : (z.re + z.im * Complex.i : ℂ) = z :=
  Complex.re_add_im z
#align upper_half_plane.re_add_im UpperHalfPlane.re_add_im

theorem im_pos (z : ℍ) : 0 < z.im :=
  z.2
#align upper_half_plane.im_pos UpperHalfPlane.im_pos

theorem im_ne_zero (z : ℍ) : z.im ≠ 0 :=
  z.im_pos.ne'
#align upper_half_plane.im_ne_zero UpperHalfPlane.im_ne_zero

theorem ne_zero (z : ℍ) : (z : ℂ) ≠ 0 :=
  mt (congr_arg Complex.im) z.im_ne_zero
#align upper_half_plane.ne_zero UpperHalfPlane.ne_zero

theorem norm_sq_pos (z : ℍ) : 0 < Complex.normSq (z : ℂ) :=
  by
  rw [Complex.norm_sq_pos]
  exact z.ne_zero
#align upper_half_plane.norm_sq_pos UpperHalfPlane.norm_sq_pos

theorem norm_sq_ne_zero (z : ℍ) : Complex.normSq (z : ℂ) ≠ 0 :=
  (norm_sq_pos z).ne'
#align upper_half_plane.norm_sq_ne_zero UpperHalfPlane.norm_sq_ne_zero

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Numerator of the formula for a fractional linear transformation -/")]
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `num [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`g]
         [":"
          (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
           "GL("
           (num "2")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")"
           "⁺")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`z]
         [":" (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")]
         []
         ")")]
       [(Term.typeSpec ":" (Data.Complex.Basic.termℂ "ℂ"))])
      (Command.declValSimple
       ":="
       («term_+_»
        («term_*_»
         (Term.typeAscription
          "("
          (Term.app (Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g) [(num "0") (num "0")])
          ":"
          [(Data.Real.Basic.termℝ "ℝ")]
          ")")
         "*"
         `z)
        "+"
        (Term.typeAscription
         "("
         (Term.app (Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g) [(num "0") (num "1")])
         ":"
         [(Data.Real.Basic.termℝ "ℝ")]
         ")"))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       («term_*_»
        (Term.typeAscription
         "("
         (Term.app (Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g) [(num "0") (num "0")])
         ":"
         [(Data.Real.Basic.termℝ "ℝ")]
         ")")
        "*"
        `z)
       "+"
       (Term.typeAscription
        "("
        (Term.app (Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g) [(num "0") (num "1")])
        ":"
        [(Data.Real.Basic.termℝ "ℝ")]
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.app (Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g) [(num "0") (num "1")])
       ":"
       [(Data.Real.Basic.termℝ "ℝ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g) [(num "0") (num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_»', expected 'Analysis.Complex.UpperHalfPlane.Basic.term↑ₘ_._@.Analysis.Complex.UpperHalfPlane.Basic._hyg.8'
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
/-- Numerator of the formula for a fractional linear transformation -/ @[ simp ]
  def num ( g : GL( 2 , ℝ ) ⁺ ) ( z : ℍ ) : ℂ := ( ↑ₘ g 0 0 : ℝ ) * z + ( ↑ₘ g 0 1 : ℝ )
#align upper_half_plane.num UpperHalfPlane.num

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Denominator of the formula for a fractional linear transformation -/")]
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `denom [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`g]
         [":"
          (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
           "GL("
           (num "2")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")"
           "⁺")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`z]
         [":" (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")]
         []
         ")")]
       [(Term.typeSpec ":" (Data.Complex.Basic.termℂ "ℂ"))])
      (Command.declValSimple
       ":="
       («term_+_»
        («term_*_»
         (Term.typeAscription
          "("
          (Term.app (Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g) [(num "1") (num "0")])
          ":"
          [(Data.Real.Basic.termℝ "ℝ")]
          ")")
         "*"
         `z)
        "+"
        (Term.typeAscription
         "("
         (Term.app (Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g) [(num "1") (num "1")])
         ":"
         [(Data.Real.Basic.termℝ "ℝ")]
         ")"))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       («term_*_»
        (Term.typeAscription
         "("
         (Term.app (Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g) [(num "1") (num "0")])
         ":"
         [(Data.Real.Basic.termℝ "ℝ")]
         ")")
        "*"
        `z)
       "+"
       (Term.typeAscription
        "("
        (Term.app (Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g) [(num "1") (num "1")])
        ":"
        [(Data.Real.Basic.termℝ "ℝ")]
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.app (Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g) [(num "1") (num "1")])
       ":"
       [(Data.Real.Basic.termℝ "ℝ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g) [(num "1") (num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_»', expected 'Analysis.Complex.UpperHalfPlane.Basic.term↑ₘ_._@.Analysis.Complex.UpperHalfPlane.Basic._hyg.8'
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
/-- Denominator of the formula for a fractional linear transformation -/ @[ simp ]
  def denom ( g : GL( 2 , ℝ ) ⁺ ) ( z : ℍ ) : ℂ := ( ↑ₘ g 1 0 : ℝ ) * z + ( ↑ₘ g 1 1 : ℝ )
#align upper_half_plane.denom UpperHalfPlane.denom

theorem linear_ne_zero (cd : Fin 2 → ℝ) (z : ℍ) (h : cd ≠ 0) : (cd 0 : ℂ) * z + cd 1 ≠ 0 :=
  by
  contrapose! h
  have : cd 0 = 0 :=
    by
    -- we will need this twice
    apply_fun Complex.im  at h
    simpa only [z.im_ne_zero, Complex.add_im, add_zero, coe_im, zero_mul, or_false_iff,
      Complex.of_real_im, Complex.zero_im, Complex.mul_im, mul_eq_zero] using h
  simp only [this, zero_mul, Complex.of_real_zero, zero_add, Complex.of_real_eq_zero] at h
  ext i
  fin_cases i <;> assumption
#align upper_half_plane.linear_ne_zero UpperHalfPlane.linear_ne_zero

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `denom_ne_zero [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`g]
         [":"
          (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
           "GL("
           (num "2")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")"
           "⁺")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`z]
         [":" (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")]
         []
         ")")]
       (Term.typeSpec ":" («term_≠_» (Term.app `denom [`g `z]) "≠" (num "0"))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.intro "intro" [`H])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`DET []]
              []
              ":="
              (Term.app
               (Term.proj (Term.app `mem_GL_pos [(Term.hole "_")]) "." (fieldIdx "1"))
               [`g.prop]))))
           []
           (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [`hz []] [] ":=" `z.prop)))
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["[" [(Tactic.simpLemma [] [] `general_linear_group.coe_det_apply)] "]"]
            [(Tactic.location "at" (Tactic.locationHyp [`DET] []))])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`H1 []]
              [(Term.typeSpec
                ":"
                («term_∨_»
                 («term_=_»
                  (Term.typeAscription
                   "("
                   (Term.app
                    (Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g)
                    [(num "1") (num "0")])
                   ":"
                   [(Data.Real.Basic.termℝ "ℝ")]
                   ")")
                  "="
                  (num "0"))
                 "∨"
                 («term_=_» `z.im "=" (num "0"))))]
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
                    []
                    []
                    ["using" (Term.app `congr_arg [`Complex.im `H])]))]))))))
           []
           (Tactic.cases "cases" [(Tactic.casesTarget [] `H1)] [] [])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `H1)
                ","
                (Tactic.simpLemma [] [] `Complex.of_real_zero)
                ","
                (Tactic.simpLemma [] [] `denom)
                ","
                (Tactic.simpLemma [] [] `coe_fn_eq_coe)
                ","
                (Tactic.simpLemma [] [] `zero_mul)
                ","
                (Tactic.simpLemma [] [] `zero_add)
                ","
                (Tactic.simpLemma [] [] `Complex.of_real_eq_zero)]
               "]"]
              [(Tactic.location "at" (Tactic.locationHyp [`H] []))])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `coe_coe)
                ","
                (Tactic.rwRule
                 []
                 (Term.app
                  `Matrix.det_fin_two
                  [(Term.typeAscription
                    "("
                    (coeNotation "↑" `g)
                    ":"
                    [(Term.app
                      `Matrix
                      [(Term.app `Fin [(num "2")])
                       (Term.app `Fin [(num "2")])
                       (Data.Real.Basic.termℝ "ℝ")])]
                    ")")]))]
               "]")
              [(Tactic.location "at" (Tactic.locationHyp [`DET] []))])
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `coe_coe)
                ","
                (Tactic.simpLemma [] [] `H)
                ","
                (Tactic.simpLemma [] [] `H1)
                ","
                (Tactic.simpLemma [] [] `mul_zero)
                ","
                (Tactic.simpLemma [] [] `sub_zero)
                ","
                (Tactic.simpLemma [] [] `lt_self_iff_false)]
               "]"]
              [(Tactic.location "at" (Tactic.locationHyp [`DET] []))])
             []
             (Tactic.exact "exact" `DET)])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.change
              "change"
              («term_>_» `z.im ">" (num "0"))
              [(Tactic.location "at" (Tactic.locationHyp [`hz] []))])
             []
             (linarith "linarith" [] (linarithArgsRest [] [] []))])])))
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
         [(Tactic.intro "intro" [`H])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`DET []]
             []
             ":="
             (Term.app
              (Term.proj (Term.app `mem_GL_pos [(Term.hole "_")]) "." (fieldIdx "1"))
              [`g.prop]))))
          []
          (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [`hz []] [] ":=" `z.prop)))
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["[" [(Tactic.simpLemma [] [] `general_linear_group.coe_det_apply)] "]"]
           [(Tactic.location "at" (Tactic.locationHyp [`DET] []))])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`H1 []]
             [(Term.typeSpec
               ":"
               («term_∨_»
                («term_=_»
                 (Term.typeAscription
                  "("
                  (Term.app
                   (Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g)
                   [(num "1") (num "0")])
                  ":"
                  [(Data.Real.Basic.termℝ "ℝ")]
                  ")")
                 "="
                 (num "0"))
                "∨"
                («term_=_» `z.im "=" (num "0"))))]
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
                   []
                   []
                   ["using" (Term.app `congr_arg [`Complex.im `H])]))]))))))
          []
          (Tactic.cases "cases" [(Tactic.casesTarget [] `H1)] [] [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `H1)
               ","
               (Tactic.simpLemma [] [] `Complex.of_real_zero)
               ","
               (Tactic.simpLemma [] [] `denom)
               ","
               (Tactic.simpLemma [] [] `coe_fn_eq_coe)
               ","
               (Tactic.simpLemma [] [] `zero_mul)
               ","
               (Tactic.simpLemma [] [] `zero_add)
               ","
               (Tactic.simpLemma [] [] `Complex.of_real_eq_zero)]
              "]"]
             [(Tactic.location "at" (Tactic.locationHyp [`H] []))])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `coe_coe)
               ","
               (Tactic.rwRule
                []
                (Term.app
                 `Matrix.det_fin_two
                 [(Term.typeAscription
                   "("
                   (coeNotation "↑" `g)
                   ":"
                   [(Term.app
                     `Matrix
                     [(Term.app `Fin [(num "2")])
                      (Term.app `Fin [(num "2")])
                      (Data.Real.Basic.termℝ "ℝ")])]
                   ")")]))]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`DET] []))])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `coe_coe)
               ","
               (Tactic.simpLemma [] [] `H)
               ","
               (Tactic.simpLemma [] [] `H1)
               ","
               (Tactic.simpLemma [] [] `mul_zero)
               ","
               (Tactic.simpLemma [] [] `sub_zero)
               ","
               (Tactic.simpLemma [] [] `lt_self_iff_false)]
              "]"]
             [(Tactic.location "at" (Tactic.locationHyp [`DET] []))])
            []
            (Tactic.exact "exact" `DET)])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.change
             "change"
             («term_>_» `z.im ">" (num "0"))
             [(Tactic.location "at" (Tactic.locationHyp [`hz] []))])
            []
            (linarith "linarith" [] (linarithArgsRest [] [] []))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.change
         "change"
         («term_>_» `z.im ">" (num "0"))
         [(Tactic.location "at" (Tactic.locationHyp [`hz] []))])
        []
        (linarith "linarith" [] (linarithArgsRest [] [] []))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (linarith "linarith" [] (linarithArgsRest [] [] []))
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       («term_>_» `z.im ">" (num "0"))
       [(Tactic.location "at" (Tactic.locationHyp [`hz] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hz
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_>_» `z.im ">" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `z.im
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `H1)
           ","
           (Tactic.simpLemma [] [] `Complex.of_real_zero)
           ","
           (Tactic.simpLemma [] [] `denom)
           ","
           (Tactic.simpLemma [] [] `coe_fn_eq_coe)
           ","
           (Tactic.simpLemma [] [] `zero_mul)
           ","
           (Tactic.simpLemma [] [] `zero_add)
           ","
           (Tactic.simpLemma [] [] `Complex.of_real_eq_zero)]
          "]"]
         [(Tactic.location "at" (Tactic.locationHyp [`H] []))])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `coe_coe)
           ","
           (Tactic.rwRule
            []
            (Term.app
             `Matrix.det_fin_two
             [(Term.typeAscription
               "("
               (coeNotation "↑" `g)
               ":"
               [(Term.app
                 `Matrix
                 [(Term.app `Fin [(num "2")])
                  (Term.app `Fin [(num "2")])
                  (Data.Real.Basic.termℝ "ℝ")])]
               ")")]))]
          "]")
         [(Tactic.location "at" (Tactic.locationHyp [`DET] []))])
        []
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `coe_coe)
           ","
           (Tactic.simpLemma [] [] `H)
           ","
           (Tactic.simpLemma [] [] `H1)
           ","
           (Tactic.simpLemma [] [] `mul_zero)
           ","
           (Tactic.simpLemma [] [] `sub_zero)
           ","
           (Tactic.simpLemma [] [] `lt_self_iff_false)]
          "]"]
         [(Tactic.location "at" (Tactic.locationHyp [`DET] []))])
        []
        (Tactic.exact "exact" `DET)])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `DET)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `DET
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `coe_coe)
         ","
         (Tactic.simpLemma [] [] `H)
         ","
         (Tactic.simpLemma [] [] `H1)
         ","
         (Tactic.simpLemma [] [] `mul_zero)
         ","
         (Tactic.simpLemma [] [] `sub_zero)
         ","
         (Tactic.simpLemma [] [] `lt_self_iff_false)]
        "]"]
       [(Tactic.location "at" (Tactic.locationHyp [`DET] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `DET
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lt_self_iff_false
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `coe_coe)
         ","
         (Tactic.rwRule
          []
          (Term.app
           `Matrix.det_fin_two
           [(Term.typeAscription
             "("
             (coeNotation "↑" `g)
             ":"
             [(Term.app
               `Matrix
               [(Term.app `Fin [(num "2")])
                (Term.app `Fin [(num "2")])
                (Data.Real.Basic.termℝ "ℝ")])]
             ")")]))]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`DET] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `DET
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Matrix.det_fin_two
       [(Term.typeAscription
         "("
         (coeNotation "↑" `g)
         ":"
         [(Term.app
           `Matrix
           [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (coeNotation "↑" `g)
       ":"
       [(Term.app
         `Matrix
         [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Matrix
       [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `Fin [(num "2")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Fin [(num "2")]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Fin [(num "2")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Fin [(num "2")]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Matrix
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (coeNotation "↑" `g)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Matrix.det_fin_two
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `H1)
         ","
         (Tactic.simpLemma [] [] `Complex.of_real_zero)
         ","
         (Tactic.simpLemma [] [] `denom)
         ","
         (Tactic.simpLemma [] [] `coe_fn_eq_coe)
         ","
         (Tactic.simpLemma [] [] `zero_mul)
         ","
         (Tactic.simpLemma [] [] `zero_add)
         ","
         (Tactic.simpLemma [] [] `Complex.of_real_eq_zero)]
        "]"]
       [(Tactic.location "at" (Tactic.locationHyp [`H] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Complex.of_real_eq_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_fn_eq_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `denom
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Complex.of_real_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases "cases" [(Tactic.casesTarget [] `H1)] [] [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`H1 []]
         [(Term.typeSpec
           ":"
           («term_∨_»
            («term_=_»
             (Term.typeAscription
              "("
              (Term.app
               (Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g)
               [(num "1") (num "0")])
              ":"
              [(Data.Real.Basic.termℝ "ℝ")]
              ")")
             "="
             (num "0"))
            "∨"
            («term_=_» `z.im "=" (num "0"))))]
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
               []
               []
               ["using" (Term.app `congr_arg [`Complex.im `H])]))]))))))
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
            []
            []
            ["using" (Term.app `congr_arg [`Complex.im `H])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        []
        []
        ["using" (Term.app `congr_arg [`Complex.im `H])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `congr_arg [`Complex.im `H])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Complex.im
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `congr_arg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∨_»
       («term_=_»
        (Term.typeAscription
         "("
         (Term.app (Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g) [(num "1") (num "0")])
         ":"
         [(Data.Real.Basic.termℝ "ℝ")]
         ")")
        "="
        (num "0"))
       "∨"
       («term_=_» `z.im "=" (num "0")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `z.im "=" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `z.im
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 30 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 30, term))
      («term_=_»
       (Term.typeAscription
        "("
        (Term.app (Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g) [(num "1") (num "0")])
        ":"
        [(Data.Real.Basic.termℝ "ℝ")]
        ")")
       "="
       (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription
       "("
       (Term.app (Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g) [(num "1") (num "0")])
       ":"
       [(Data.Real.Basic.termℝ "ℝ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g) [(num "1") (num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_»', expected 'Analysis.Complex.UpperHalfPlane.Basic.term↑ₘ_._@.Analysis.Complex.UpperHalfPlane.Basic._hyg.8'
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
  denom_ne_zero
  ( g : GL( 2 , ℝ ) ⁺ ) ( z : ℍ ) : denom g z ≠ 0
  :=
    by
      intro H
        have DET := mem_GL_pos _ . 1 g.prop
        have hz := z.prop
        simp only [ general_linear_group.coe_det_apply ] at DET
        have H1 : ( ↑ₘ g 1 0 : ℝ ) = 0 ∨ z.im = 0 := by simpa using congr_arg Complex.im H
        cases H1
        ·
          simp
              only
              [
                H1
                  ,
                  Complex.of_real_zero
                  ,
                  denom
                  ,
                  coe_fn_eq_coe
                  ,
                  zero_mul
                  ,
                  zero_add
                  ,
                  Complex.of_real_eq_zero
                ]
              at H
            rw [ ← coe_coe , Matrix.det_fin_two ( ↑ g : Matrix Fin 2 Fin 2 ℝ ) ] at DET
            simp only [ coe_coe , H , H1 , mul_zero , sub_zero , lt_self_iff_false ] at DET
            exact DET
        · change z.im > 0 at hz linarith
#align upper_half_plane.denom_ne_zero UpperHalfPlane.denom_ne_zero

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `norm_sq_denom_pos [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`g]
         [":"
          (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
           "GL("
           (num "2")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")"
           "⁺")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`z]
         [":" (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_<_» (num "0") "<" (Term.app `Complex.normSq [(Term.app `denom [`g `z])]))))
      (Command.declValSimple
       ":="
       (Term.app (Term.proj `Complex.norm_sq_pos "." `mpr) [(Term.app `denom_ne_zero [`g `z])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `Complex.norm_sq_pos "." `mpr) [(Term.app `denom_ne_zero [`g `z])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `denom_ne_zero [`g `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `denom_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `denom_ne_zero [`g `z]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `Complex.norm_sq_pos "." `mpr)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Complex.norm_sq_pos
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_<_» (num "0") "<" (Term.app `Complex.normSq [(Term.app `denom [`g `z])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Complex.normSq [(Term.app `denom [`g `z])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `denom [`g `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `denom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `denom [`g `z]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Complex.normSq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
       "GL("
       (num "2")
       ", "
       (Data.Real.Basic.termℝ "ℝ")
       ")"
       "⁺")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»', expected 'Analysis.Complex.UpperHalfPlane.Basic.termGL(_,_)⁺._@.Analysis.Complex.UpperHalfPlane.Basic._hyg.63'
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
  norm_sq_denom_pos
  ( g : GL( 2 , ℝ ) ⁺ ) ( z : ℍ ) : 0 < Complex.normSq denom g z
  := Complex.norm_sq_pos . mpr denom_ne_zero g z
#align upper_half_plane.norm_sq_denom_pos UpperHalfPlane.norm_sq_denom_pos

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `norm_sq_denom_ne_zero [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`g]
         [":"
          (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
           "GL("
           (num "2")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")"
           "⁺")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`z]
         [":" (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_≠_» (Term.app `Complex.normSq [(Term.app `denom [`g `z])]) "≠" (num "0"))))
      (Command.declValSimple ":=" (Term.app `ne_of_gt [(Term.app `norm_sq_denom_pos [`g `z])]) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ne_of_gt [(Term.app `norm_sq_denom_pos [`g `z])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `norm_sq_denom_pos [`g `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm_sq_denom_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `norm_sq_denom_pos [`g `z])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ne_of_gt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≠_» (Term.app `Complex.normSq [(Term.app `denom [`g `z])]) "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `Complex.normSq [(Term.app `denom [`g `z])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `denom [`g `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `denom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `denom [`g `z]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Complex.normSq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
       "GL("
       (num "2")
       ", "
       (Data.Real.Basic.termℝ "ℝ")
       ")"
       "⁺")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»', expected 'Analysis.Complex.UpperHalfPlane.Basic.termGL(_,_)⁺._@.Analysis.Complex.UpperHalfPlane.Basic._hyg.63'
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
  norm_sq_denom_ne_zero
  ( g : GL( 2 , ℝ ) ⁺ ) ( z : ℍ ) : Complex.normSq denom g z ≠ 0
  := ne_of_gt norm_sq_denom_pos g z
#align upper_half_plane.norm_sq_denom_ne_zero UpperHalfPlane.norm_sq_denom_ne_zero

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Fractional linear transformation, also known as the Moebius transformation -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `smulAux' [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`g]
         [":"
          (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
           "GL("
           (num "2")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")"
           "⁺")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`z]
         [":" (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")]
         []
         ")")]
       [(Term.typeSpec ":" (Data.Complex.Basic.termℂ "ℂ"))])
      (Command.declValSimple
       ":="
       («term_/_» (Term.app `num [`g `z]) "/" (Term.app `denom [`g `z]))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» (Term.app `num [`g `z]) "/" (Term.app `denom [`g `z]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `denom [`g `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `denom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `num [`g `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `num
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
       "GL("
       (num "2")
       ", "
       (Data.Real.Basic.termℝ "ℝ")
       ")"
       "⁺")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»', expected 'Analysis.Complex.UpperHalfPlane.Basic.termGL(_,_)⁺._@.Analysis.Complex.UpperHalfPlane.Basic._hyg.63'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Fractional linear transformation, also known as the Moebius transformation -/
  def smulAux' ( g : GL( 2 , ℝ ) ⁺ ) ( z : ℍ ) : ℂ := num g z / denom g z
#align upper_half_plane.smul_aux' UpperHalfPlane.smulAux'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `smul_aux'_im [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`g]
         [":"
          (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
           "GL("
           (num "2")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")"
           "⁺")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`z]
         [":" (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.proj (Term.app `smulAux' [`g `z]) "." `im)
         "="
         («term_/_»
          («term_*_»
           (Term.app `det [(Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g)])
           "*"
           (Term.proj `z "." `im))
          "/"
          (Term.proj (Term.app `denom [`g `z]) "." `normSq)))))
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
             [(Tactic.rwRule [] `smul_aux') "," (Tactic.rwRule [] `Complex.div_im)]
             "]")
            [])
           []
           (Mathlib.Tactic.set
            "set"
            []
            (Mathlib.Tactic.setArgsRest
             `NsqBot
             []
             ":="
             (Term.proj (Term.app `denom [`g `z]) "." `normSq)
             []))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec ":" («term_≠_» `NsqBot "≠" (num "0")))]
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
                    [(Tactic.simpLemma [] [] (Term.app `denom_ne_zero [`g `z]))
                     ","
                     (Tactic.simpLemma [] [] `map_eq_zero)
                     ","
                     (Tactic.simpLemma [] [] `Ne.def)
                     ","
                     (Tactic.simpLemma [] [] `not_false_iff)]
                    "]"]
                   [])]))))))
           []
           (Tactic.fieldSimp
            "field_simp"
            []
            []
            []
            [(Tactic.simpArgs
              "["
              [(Tactic.simpLemma [] [] `smul_aux') "," (Tactic.simpErase "-" `coe_coe)]
              "]")]
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               []
               (Term.app
                `Matrix.det_fin_two
                [(Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g)]))]
             "]")
            [])
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
            [(Tactic.rwRule [] `smul_aux') "," (Tactic.rwRule [] `Complex.div_im)]
            "]")
           [])
          []
          (Mathlib.Tactic.set
           "set"
           []
           (Mathlib.Tactic.setArgsRest
            `NsqBot
            []
            ":="
            (Term.proj (Term.app `denom [`g `z]) "." `normSq)
            []))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec ":" («term_≠_» `NsqBot "≠" (num "0")))]
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
                   [(Tactic.simpLemma [] [] (Term.app `denom_ne_zero [`g `z]))
                    ","
                    (Tactic.simpLemma [] [] `map_eq_zero)
                    ","
                    (Tactic.simpLemma [] [] `Ne.def)
                    ","
                    (Tactic.simpLemma [] [] `not_false_iff)]
                   "]"]
                  [])]))))))
          []
          (Tactic.fieldSimp
           "field_simp"
           []
           []
           []
           [(Tactic.simpArgs
             "["
             [(Tactic.simpLemma [] [] `smul_aux') "," (Tactic.simpErase "-" `coe_coe)]
             "]")]
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.app
               `Matrix.det_fin_two
               [(Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g)]))]
            "]")
           [])
          []
          (Mathlib.Tactic.RingNF.ring "ring")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.RingNF.ring "ring")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          []
          (Term.app
           `Matrix.det_fin_two
           [(Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g)]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Matrix.det_fin_two [(Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_»', expected 'Analysis.Complex.UpperHalfPlane.Basic.term↑ₘ_._@.Analysis.Complex.UpperHalfPlane.Basic._hyg.8'
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
  smul_aux'_im
  ( g : GL( 2 , ℝ ) ⁺ ) ( z : ℍ ) : smulAux' g z . im = det ↑ₘ g * z . im / denom g z . normSq
  :=
    by
      rw [ smul_aux' , Complex.div_im ]
        set NsqBot := denom g z . normSq
        have
          : NsqBot ≠ 0 := by simp only [ denom_ne_zero g z , map_eq_zero , Ne.def , not_false_iff ]
        field_simp [ smul_aux' , - coe_coe ]
        rw [ Matrix.det_fin_two ↑ₘ g ]
        ring
#align upper_half_plane.smul_aux'_im UpperHalfPlane.smul_aux'_im

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Fractional linear transformation, also known as the Moebius transformation -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `smulAux [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`g]
         [":"
          (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
           "GL("
           (num "2")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")"
           "⁺")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`z]
         [":" (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")]
         []
         ")")]
       [(Term.typeSpec
         ":"
         (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ"))])
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.app `smulAux' [`g `z])
         ","
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `smul_aux'_im)] "]") [])
             []
             (convert
              "convert"
              []
              (Term.app
               `mul_pos
               [(Term.app
                 (Term.proj (Term.app `mem_GL_pos [(Term.hole "_")]) "." (fieldIdx "1"))
                 [`g.prop])
                (Term.app
                 `div_pos
                 [`z.im_pos
                  (Term.app `complex.norm_sq_pos.mpr [(Term.app `denom_ne_zero [`g `z])])])])
              [])
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `general_linear_group.coe_det_apply)
                ","
                (Tactic.simpLemma [] [] `coe_coe)]
               "]"]
              [])
             []
             (Mathlib.Tactic.RingNF.ring "ring")])))]
        "⟩")
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app `smulAux' [`g `z])
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `smul_aux'_im)] "]") [])
            []
            (convert
             "convert"
             []
             (Term.app
              `mul_pos
              [(Term.app
                (Term.proj (Term.app `mem_GL_pos [(Term.hole "_")]) "." (fieldIdx "1"))
                [`g.prop])
               (Term.app
                `div_pos
                [`z.im_pos
                 (Term.app `complex.norm_sq_pos.mpr [(Term.app `denom_ne_zero [`g `z])])])])
             [])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `general_linear_group.coe_det_apply)
               ","
               (Tactic.simpLemma [] [] `coe_coe)]
              "]"]
             [])
            []
            (Mathlib.Tactic.RingNF.ring "ring")])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `smul_aux'_im)] "]") [])
          []
          (convert
           "convert"
           []
           (Term.app
            `mul_pos
            [(Term.app
              (Term.proj (Term.app `mem_GL_pos [(Term.hole "_")]) "." (fieldIdx "1"))
              [`g.prop])
             (Term.app
              `div_pos
              [`z.im_pos (Term.app `complex.norm_sq_pos.mpr [(Term.app `denom_ne_zero [`g `z])])])])
           [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `general_linear_group.coe_det_apply)
             ","
             (Tactic.simpLemma [] [] `coe_coe)]
            "]"]
           [])
          []
          (Mathlib.Tactic.RingNF.ring "ring")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.RingNF.ring "ring")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `general_linear_group.coe_det_apply)
         ","
         (Tactic.simpLemma [] [] `coe_coe)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `general_linear_group.coe_det_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert
       "convert"
       []
       (Term.app
        `mul_pos
        [(Term.app
          (Term.proj (Term.app `mem_GL_pos [(Term.hole "_")]) "." (fieldIdx "1"))
          [`g.prop])
         (Term.app
          `div_pos
          [`z.im_pos (Term.app `complex.norm_sq_pos.mpr [(Term.app `denom_ne_zero [`g `z])])])])
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mul_pos
       [(Term.app (Term.proj (Term.app `mem_GL_pos [(Term.hole "_")]) "." (fieldIdx "1")) [`g.prop])
        (Term.app
         `div_pos
         [`z.im_pos (Term.app `complex.norm_sq_pos.mpr [(Term.app `denom_ne_zero [`g `z])])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `div_pos
       [`z.im_pos (Term.app `complex.norm_sq_pos.mpr [(Term.app `denom_ne_zero [`g `z])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `complex.norm_sq_pos.mpr [(Term.app `denom_ne_zero [`g `z])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `denom_ne_zero [`g `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `denom_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `denom_ne_zero [`g `z]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `complex.norm_sq_pos.mpr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `complex.norm_sq_pos.mpr [(Term.paren "(" (Term.app `denom_ne_zero [`g `z]) ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `z.im_pos
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `div_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `div_pos
      [`z.im_pos
       (Term.paren
        "("
        (Term.app `complex.norm_sq_pos.mpr [(Term.paren "(" (Term.app `denom_ne_zero [`g `z]) ")")])
        ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj (Term.app `mem_GL_pos [(Term.hole "_")]) "." (fieldIdx "1")) [`g.prop])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g.prop
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `mem_GL_pos [(Term.hole "_")]) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `mem_GL_pos [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mem_GL_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `mem_GL_pos [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.paren "(" (Term.app `mem_GL_pos [(Term.hole "_")]) ")") "." (fieldIdx "1"))
      [`g.prop])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `smul_aux'_im)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `smul_aux'_im
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `smulAux' [`g `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `smulAux'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
       "GL("
       (num "2")
       ", "
       (Data.Real.Basic.termℝ "ℝ")
       ")"
       "⁺")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»', expected 'Analysis.Complex.UpperHalfPlane.Basic.termGL(_,_)⁺._@.Analysis.Complex.UpperHalfPlane.Basic._hyg.63'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Fractional linear transformation, also known as the Moebius transformation -/
  def
    smulAux
    ( g : GL( 2 , ℝ ) ⁺ ) ( z : ℍ ) : ℍ
    :=
      ⟨
        smulAux' g z
          ,
          by
            rw [ smul_aux'_im ]
              convert
                mul_pos
                  mem_GL_pos _ . 1 g.prop div_pos z.im_pos complex.norm_sq_pos.mpr denom_ne_zero g z
              simp only [ general_linear_group.coe_det_apply , coe_coe ]
              ring
        ⟩
#align upper_half_plane.smul_aux UpperHalfPlane.smulAux

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `denom_cocycle [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`x `y]
         [":"
          (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
           "GL("
           (num "2")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")"
           "⁺")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`z]
         [":" (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `denom [(«term_*_» `x "*" `y) `z])
         "="
         («term_*_»
          (Term.app `denom [`x (Term.app `smulAux [`y `z])])
          "*"
          (Term.app `denom [`y `z])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.change
            "change"
            («term_=_»
             (Term.hole "_")
             "="
             («term_*_»
              («term_+_»
               («term_*_» (Term.hole "_") "*" («term_/_» (Term.hole "_") "/" (Term.hole "_")))
               "+"
               (Term.hole "_"))
              "*"
              (Term.hole "_")))
            [])
           []
           (Tactic.fieldSimp
            "field_simp"
            []
            []
            []
            [(Tactic.simpArgs
              "["
              [(Tactic.simpLemma [] [] `denom_ne_zero)
               ","
               (Tactic.simpErase "-" `denom)
               ","
               (Tactic.simpErase "-" `Num)]
              "]")]
            [])
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `Matrix.mul)
              ","
              (Tactic.simpLemma [] [] `dot_product)
              ","
              (Tactic.simpLemma [] [] `Fin.sum_univ_succ)
              ","
              (Tactic.simpLemma [] [] `denom)
              ","
              (Tactic.simpLemma [] [] `Num)
              ","
              (Tactic.simpLemma [] [] `coe_coe)
              ","
              (Tactic.simpLemma [] [] `Subgroup.coe_mul)
              ","
              (Tactic.simpLemma [] [] `general_linear_group.coe_mul)
              ","
              (Tactic.simpLemma [] [] `Fintype.univ_of_subsingleton)
              ","
              (Tactic.simpLemma [] [] `Fin.mk_zero)
              ","
              (Tactic.simpLemma [] [] `Finset.sum_singleton)
              ","
              (Tactic.simpLemma [] [] `Fin.succ_zero_eq_one)
              ","
              (Tactic.simpLemma [] [] `Complex.of_real_add)
              ","
              (Tactic.simpLemma [] [] `Complex.of_real_mul)]
             "]"]
            [])
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
         [(Tactic.change
           "change"
           («term_=_»
            (Term.hole "_")
            "="
            («term_*_»
             («term_+_»
              («term_*_» (Term.hole "_") "*" («term_/_» (Term.hole "_") "/" (Term.hole "_")))
              "+"
              (Term.hole "_"))
             "*"
             (Term.hole "_")))
           [])
          []
          (Tactic.fieldSimp
           "field_simp"
           []
           []
           []
           [(Tactic.simpArgs
             "["
             [(Tactic.simpLemma [] [] `denom_ne_zero)
              ","
              (Tactic.simpErase "-" `denom)
              ","
              (Tactic.simpErase "-" `Num)]
             "]")]
           [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `Matrix.mul)
             ","
             (Tactic.simpLemma [] [] `dot_product)
             ","
             (Tactic.simpLemma [] [] `Fin.sum_univ_succ)
             ","
             (Tactic.simpLemma [] [] `denom)
             ","
             (Tactic.simpLemma [] [] `Num)
             ","
             (Tactic.simpLemma [] [] `coe_coe)
             ","
             (Tactic.simpLemma [] [] `Subgroup.coe_mul)
             ","
             (Tactic.simpLemma [] [] `general_linear_group.coe_mul)
             ","
             (Tactic.simpLemma [] [] `Fintype.univ_of_subsingleton)
             ","
             (Tactic.simpLemma [] [] `Fin.mk_zero)
             ","
             (Tactic.simpLemma [] [] `Finset.sum_singleton)
             ","
             (Tactic.simpLemma [] [] `Fin.succ_zero_eq_one)
             ","
             (Tactic.simpLemma [] [] `Complex.of_real_add)
             ","
             (Tactic.simpLemma [] [] `Complex.of_real_mul)]
            "]"]
           [])
          []
          (Mathlib.Tactic.RingNF.ring "ring")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.RingNF.ring "ring")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `Matrix.mul)
         ","
         (Tactic.simpLemma [] [] `dot_product)
         ","
         (Tactic.simpLemma [] [] `Fin.sum_univ_succ)
         ","
         (Tactic.simpLemma [] [] `denom)
         ","
         (Tactic.simpLemma [] [] `Num)
         ","
         (Tactic.simpLemma [] [] `coe_coe)
         ","
         (Tactic.simpLemma [] [] `Subgroup.coe_mul)
         ","
         (Tactic.simpLemma [] [] `general_linear_group.coe_mul)
         ","
         (Tactic.simpLemma [] [] `Fintype.univ_of_subsingleton)
         ","
         (Tactic.simpLemma [] [] `Fin.mk_zero)
         ","
         (Tactic.simpLemma [] [] `Finset.sum_singleton)
         ","
         (Tactic.simpLemma [] [] `Fin.succ_zero_eq_one)
         ","
         (Tactic.simpLemma [] [] `Complex.of_real_add)
         ","
         (Tactic.simpLemma [] [] `Complex.of_real_mul)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Complex.of_real_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Complex.of_real_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fin.succ_zero_eq_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Finset.sum_singleton
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fin.mk_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fintype.univ_of_subsingleton
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `general_linear_group.coe_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subgroup.coe_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Num
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `denom
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fin.sum_univ_succ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `dot_product
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Matrix.mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.fieldSimp
       "field_simp"
       []
       []
       []
       [(Tactic.simpArgs
         "["
         [(Tactic.simpLemma [] [] `denom_ne_zero)
          ","
          (Tactic.simpErase "-" `denom)
          ","
          (Tactic.simpErase "-" `Num)]
         "]")]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpErase', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Num
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpErase', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `denom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `denom_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       («term_=_»
        (Term.hole "_")
        "="
        («term_*_»
         («term_+_»
          («term_*_» (Term.hole "_") "*" («term_/_» (Term.hole "_") "/" (Term.hole "_")))
          "+"
          (Term.hole "_"))
         "*"
         (Term.hole "_")))
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       («term_*_»
        («term_+_»
         («term_*_» (Term.hole "_") "*" («term_/_» (Term.hole "_") "/" (Term.hole "_")))
         "+"
         (Term.hole "_"))
        "*"
        (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_+_»
        («term_*_» (Term.hole "_") "*" («term_/_» (Term.hole "_") "/" (Term.hole "_")))
        "+"
        (Term.hole "_"))
       "*"
       (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_+_»
       («term_*_» (Term.hole "_") "*" («term_/_» (Term.hole "_") "/" (Term.hole "_")))
       "+"
       (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_*_» (Term.hole "_") "*" («term_/_» (Term.hole "_") "/" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» (Term.hole "_") "/" (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_/_» (Term.hole "_") "/" (Term.hole "_"))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 70, (some 71, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 65, (some 66, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_+_»
      («term_*_»
       (Term.hole "_")
       "*"
       (Term.paren "(" («term_/_» (Term.hole "_") "/" (Term.hole "_")) ")"))
      "+"
      (Term.hole "_"))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app `denom [(«term_*_» `x "*" `y) `z])
       "="
       («term_*_» (Term.app `denom [`x (Term.app `smulAux [`y `z])]) "*" (Term.app `denom [`y `z])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (Term.app `denom [`x (Term.app `smulAux [`y `z])]) "*" (Term.app `denom [`y `z]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `denom [`y `z])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `denom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `denom [`x (Term.app `smulAux [`y `z])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `smulAux [`y `z])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `smulAux
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `smulAux [`y `z]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `denom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `denom [(«term_*_» `x "*" `y) `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_*_» `x "*" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 70, (some 71, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_*_» `x "*" `y) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `denom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
       "GL("
       (num "2")
       ", "
       (Data.Real.Basic.termℝ "ℝ")
       ")"
       "⁺")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»', expected 'Analysis.Complex.UpperHalfPlane.Basic.termGL(_,_)⁺._@.Analysis.Complex.UpperHalfPlane.Basic._hyg.63'
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
  denom_cocycle
  ( x y : GL( 2 , ℝ ) ⁺ ) ( z : ℍ ) : denom x * y z = denom x smulAux y z * denom y z
  :=
    by
      change _ = _ * _ / _ + _ * _
        field_simp [ denom_ne_zero , - denom , - Num ]
        simp
          only
          [
            Matrix.mul
              ,
              dot_product
              ,
              Fin.sum_univ_succ
              ,
              denom
              ,
              Num
              ,
              coe_coe
              ,
              Subgroup.coe_mul
              ,
              general_linear_group.coe_mul
              ,
              Fintype.univ_of_subsingleton
              ,
              Fin.mk_zero
              ,
              Finset.sum_singleton
              ,
              Fin.succ_zero_eq_one
              ,
              Complex.of_real_add
              ,
              Complex.of_real_mul
            ]
        ring
#align upper_half_plane.denom_cocycle UpperHalfPlane.denom_cocycle

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mul_smul' [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`x `y]
         [":"
          (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
           "GL("
           (num "2")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")"
           "⁺")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`z]
         [":" (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `smulAux [(«term_*_» `x "*" `y) `z])
         "="
         (Term.app `smulAux [`x (Term.app `smulAux [`y `z])]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.Ext.tacticExt1___ "ext1" [])
           []
           (Tactic.change
            "change"
            («term_=_»
             («term_/_» (Term.hole "_") "/" (Term.hole "_"))
             "="
             («term_*_»
              («term_+_»
               («term_*_» (Term.hole "_") "*" («term_/_» (Term.hole "_") "/" (Term.hole "_")))
               "+"
               (Term.hole "_"))
              "*"
              (Term.hole "_")))
            [])
           []
           (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `denom_cocycle)] "]") [])
           []
           (Tactic.fieldSimp
            "field_simp"
            []
            []
            []
            [(Tactic.simpArgs
              "["
              [(Tactic.simpLemma [] [] `denom_ne_zero)
               ","
               (Tactic.simpErase "-" `denom)
               ","
               (Tactic.simpErase "-" `Num)]
              "]")]
            [])
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `Matrix.mul)
              ","
              (Tactic.simpLemma [] [] `dot_product)
              ","
              (Tactic.simpLemma [] [] `Fin.sum_univ_succ)
              ","
              (Tactic.simpLemma [] [] `Num)
              ","
              (Tactic.simpLemma [] [] `denom)
              ","
              (Tactic.simpLemma [] [] `coe_coe)
              ","
              (Tactic.simpLemma [] [] `Subgroup.coe_mul)
              ","
              (Tactic.simpLemma [] [] `general_linear_group.coe_mul)
              ","
              (Tactic.simpLemma [] [] `Fintype.univ_of_subsingleton)
              ","
              (Tactic.simpLemma [] [] `Fin.mk_zero)
              ","
              (Tactic.simpLemma [] [] `Finset.sum_singleton)
              ","
              (Tactic.simpLemma [] [] `Fin.succ_zero_eq_one)
              ","
              (Tactic.simpLemma [] [] `Complex.of_real_add)
              ","
              (Tactic.simpLemma [] [] `Complex.of_real_mul)]
             "]"]
            [])
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
         [(Std.Tactic.Ext.tacticExt1___ "ext1" [])
          []
          (Tactic.change
           "change"
           («term_=_»
            («term_/_» (Term.hole "_") "/" (Term.hole "_"))
            "="
            («term_*_»
             («term_+_»
              («term_*_» (Term.hole "_") "*" («term_/_» (Term.hole "_") "/" (Term.hole "_")))
              "+"
              (Term.hole "_"))
             "*"
             (Term.hole "_")))
           [])
          []
          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `denom_cocycle)] "]") [])
          []
          (Tactic.fieldSimp
           "field_simp"
           []
           []
           []
           [(Tactic.simpArgs
             "["
             [(Tactic.simpLemma [] [] `denom_ne_zero)
              ","
              (Tactic.simpErase "-" `denom)
              ","
              (Tactic.simpErase "-" `Num)]
             "]")]
           [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `Matrix.mul)
             ","
             (Tactic.simpLemma [] [] `dot_product)
             ","
             (Tactic.simpLemma [] [] `Fin.sum_univ_succ)
             ","
             (Tactic.simpLemma [] [] `Num)
             ","
             (Tactic.simpLemma [] [] `denom)
             ","
             (Tactic.simpLemma [] [] `coe_coe)
             ","
             (Tactic.simpLemma [] [] `Subgroup.coe_mul)
             ","
             (Tactic.simpLemma [] [] `general_linear_group.coe_mul)
             ","
             (Tactic.simpLemma [] [] `Fintype.univ_of_subsingleton)
             ","
             (Tactic.simpLemma [] [] `Fin.mk_zero)
             ","
             (Tactic.simpLemma [] [] `Finset.sum_singleton)
             ","
             (Tactic.simpLemma [] [] `Fin.succ_zero_eq_one)
             ","
             (Tactic.simpLemma [] [] `Complex.of_real_add)
             ","
             (Tactic.simpLemma [] [] `Complex.of_real_mul)]
            "]"]
           [])
          []
          (Mathlib.Tactic.RingNF.ring "ring")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.RingNF.ring "ring")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `Matrix.mul)
         ","
         (Tactic.simpLemma [] [] `dot_product)
         ","
         (Tactic.simpLemma [] [] `Fin.sum_univ_succ)
         ","
         (Tactic.simpLemma [] [] `Num)
         ","
         (Tactic.simpLemma [] [] `denom)
         ","
         (Tactic.simpLemma [] [] `coe_coe)
         ","
         (Tactic.simpLemma [] [] `Subgroup.coe_mul)
         ","
         (Tactic.simpLemma [] [] `general_linear_group.coe_mul)
         ","
         (Tactic.simpLemma [] [] `Fintype.univ_of_subsingleton)
         ","
         (Tactic.simpLemma [] [] `Fin.mk_zero)
         ","
         (Tactic.simpLemma [] [] `Finset.sum_singleton)
         ","
         (Tactic.simpLemma [] [] `Fin.succ_zero_eq_one)
         ","
         (Tactic.simpLemma [] [] `Complex.of_real_add)
         ","
         (Tactic.simpLemma [] [] `Complex.of_real_mul)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Complex.of_real_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Complex.of_real_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fin.succ_zero_eq_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Finset.sum_singleton
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fin.mk_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fintype.univ_of_subsingleton
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `general_linear_group.coe_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subgroup.coe_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `denom
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Num
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Fin.sum_univ_succ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `dot_product
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Matrix.mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.fieldSimp
       "field_simp"
       []
       []
       []
       [(Tactic.simpArgs
         "["
         [(Tactic.simpLemma [] [] `denom_ne_zero)
          ","
          (Tactic.simpErase "-" `denom)
          ","
          (Tactic.simpErase "-" `Num)]
         "]")]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpErase', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Num
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpErase', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `denom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `denom_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `denom_cocycle)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `denom_cocycle
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       («term_=_»
        («term_/_» (Term.hole "_") "/" (Term.hole "_"))
        "="
        («term_*_»
         («term_+_»
          («term_*_» (Term.hole "_") "*" («term_/_» (Term.hole "_") "/" (Term.hole "_")))
          "+"
          (Term.hole "_"))
         "*"
         (Term.hole "_")))
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       («term_/_» (Term.hole "_") "/" (Term.hole "_"))
       "="
       («term_*_»
        («term_+_»
         («term_*_» (Term.hole "_") "*" («term_/_» (Term.hole "_") "/" (Term.hole "_")))
         "+"
         (Term.hole "_"))
        "*"
        (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_+_»
        («term_*_» (Term.hole "_") "*" («term_/_» (Term.hole "_") "/" (Term.hole "_")))
        "+"
        (Term.hole "_"))
       "*"
       (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_+_»
       («term_*_» (Term.hole "_") "*" («term_/_» (Term.hole "_") "/" (Term.hole "_")))
       "+"
       (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_*_» (Term.hole "_") "*" («term_/_» (Term.hole "_") "/" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» (Term.hole "_") "/" (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_/_» (Term.hole "_") "/" (Term.hole "_"))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 70, (some 71, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 65, (some 66, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_+_»
      («term_*_»
       (Term.hole "_")
       "*"
       (Term.paren "(" («term_/_» (Term.hole "_") "/" (Term.hole "_")) ")"))
      "+"
      (Term.hole "_"))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_/_» (Term.hole "_") "/" (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.tacticExt1___ "ext1" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app `smulAux [(«term_*_» `x "*" `y) `z])
       "="
       (Term.app `smulAux [`x (Term.app `smulAux [`y `z])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `smulAux [`x (Term.app `smulAux [`y `z])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `smulAux [`y `z])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `smulAux
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `smulAux [`y `z]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `smulAux
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `smulAux [(«term_*_» `x "*" `y) `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_*_» `x "*" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 70, (some 71, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_*_» `x "*" `y) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `smulAux
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
       "GL("
       (num "2")
       ", "
       (Data.Real.Basic.termℝ "ℝ")
       ")"
       "⁺")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»', expected 'Analysis.Complex.UpperHalfPlane.Basic.termGL(_,_)⁺._@.Analysis.Complex.UpperHalfPlane.Basic._hyg.63'
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
  mul_smul'
  ( x y : GL( 2 , ℝ ) ⁺ ) ( z : ℍ ) : smulAux x * y z = smulAux x smulAux y z
  :=
    by
      ext1
        change _ / _ = _ * _ / _ + _ * _
        rw [ denom_cocycle ]
        field_simp [ denom_ne_zero , - denom , - Num ]
        simp
          only
          [
            Matrix.mul
              ,
              dot_product
              ,
              Fin.sum_univ_succ
              ,
              Num
              ,
              denom
              ,
              coe_coe
              ,
              Subgroup.coe_mul
              ,
              general_linear_group.coe_mul
              ,
              Fintype.univ_of_subsingleton
              ,
              Fin.mk_zero
              ,
              Finset.sum_singleton
              ,
              Fin.succ_zero_eq_one
              ,
              Complex.of_real_add
              ,
              Complex.of_real_mul
            ]
        ring
#align upper_half_plane.mul_smul' UpperHalfPlane.mul_smul'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The action of ` GL_pos 2 ℝ` on the upper half-plane by fractional linear transformations. -/")]
      []
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
       []
       (Term.typeSpec
        ":"
        (Term.app
         `MulAction
         [(Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
           "GL("
           (num "2")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")"
           "⁺")
          (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")])))
      (Command.whereStructInst
       "where"
       [(Command.whereStructField (Term.letDecl (Term.letIdDecl `smul [] [] ":=" `smulAux)))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `one_smul
           [`z]
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.Ext.tacticExt1___ "ext1" [])
               []
               (Tactic.change
                "change"
                («term_=_» («term_/_» (Term.hole "_") "/" (Term.hole "_")) "=" (Term.hole "_"))
                [])
               []
               (Tactic.simp
                "simp"
                []
                []
                []
                ["[" [(Tactic.simpLemma [] [] `coe_fn_coe_base')] "]"]
                [])]))))))
        []
        (Command.whereStructField (Term.letDecl (Term.letIdDecl `mul_smul [] [] ":=" `mul_smul')))]
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
      `mul_smul'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Ext.tacticExt1___ "ext1" [])
          []
          (Tactic.change
           "change"
           («term_=_» («term_/_» (Term.hole "_") "/" (Term.hole "_")) "=" (Term.hole "_"))
           [])
          []
          (Tactic.simp
           "simp"
           []
           []
           []
           ["[" [(Tactic.simpLemma [] [] `coe_fn_coe_base')] "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `coe_fn_coe_base')] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_fn_coe_base'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       («term_=_» («term_/_» (Term.hole "_") "/" (Term.hole "_")) "=" (Term.hole "_"))
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» («term_/_» (Term.hole "_") "/" (Term.hole "_")) "=" (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_/_» (Term.hole "_") "/" (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.tacticExt1___ "ext1" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `smulAux
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `MulAction
       [(Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
         "GL("
         (num "2")
         ", "
         (Data.Real.Basic.termℝ "ℝ")
         ")"
         "⁺")
        (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
       "GL("
       (num "2")
       ", "
       (Data.Real.Basic.termℝ "ℝ")
       ")"
       "⁺")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»', expected 'Analysis.Complex.UpperHalfPlane.Basic.termGL(_,_)⁺._@.Analysis.Complex.UpperHalfPlane.Basic._hyg.63'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The action of ` GL_pos 2 ℝ` on the upper half-plane by fractional linear transformations. -/
  instance
    : MulAction GL( 2 , ℝ ) ⁺ ℍ
    where
      smul := smulAux
        one_smul z := by ext1 change _ / _ = _ simp [ coe_fn_coe_base' ]
        mul_smul := mul_smul'

section ModularScalarTowers

variable (Γ : Subgroup (SpecialLinearGroup (Fin 2) ℤ))

instance sLAction {R : Type _} [CommRing R] [Algebra R ℝ] : MulAction SL(2, R) ℍ :=
  MulAction.compHom ℍ <| SpecialLinearGroup.toGLPos.comp <| map (algebraMap R ℝ)
#align upper_half_plane.SL_action UpperHalfPlane.sLAction

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
         `Coe
         [(MatrixGroups.LinearAlgebra.SpecialLinearGroup.special_linear_group.fin
           "SL("
           (num "2")
           ", "
           (termℤ "ℤ")
           ")")
          (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
           "GL("
           (num "2")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")"
           "⁺")])))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.fun
          "fun"
          (Term.basicFun
           [`g]
           []
           "=>"
           (Term.typeAscription
            "("
            (Term.typeAscription
             "("
             `g
             ":"
             [(MatrixGroups.LinearAlgebra.SpecialLinearGroup.special_linear_group.fin
               "SL("
               (num "2")
               ", "
               (Data.Real.Basic.termℝ "ℝ")
               ")")]
             ")")
            ":"
            [(Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
              "GL("
              (num "2")
              ", "
              (Data.Real.Basic.termℝ "ℝ")
              ")"
              "⁺")]
            ")")))]
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
          [`g]
          []
          "=>"
          (Term.typeAscription
           "("
           (Term.typeAscription
            "("
            `g
            ":"
            [(MatrixGroups.LinearAlgebra.SpecialLinearGroup.special_linear_group.fin
              "SL("
              (num "2")
              ", "
              (Data.Real.Basic.termℝ "ℝ")
              ")")]
            ")")
           ":"
           [(Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
             "GL("
             (num "2")
             ", "
             (Data.Real.Basic.termℝ "ℝ")
             ")"
             "⁺")]
           ")")))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`g]
        []
        "=>"
        (Term.typeAscription
         "("
         (Term.typeAscription
          "("
          `g
          ":"
          [(MatrixGroups.LinearAlgebra.SpecialLinearGroup.special_linear_group.fin
            "SL("
            (num "2")
            ", "
            (Data.Real.Basic.termℝ "ℝ")
            ")")]
          ")")
         ":"
         [(Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
           "GL("
           (num "2")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")"
           "⁺")]
         ")")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.typeAscription
        "("
        `g
        ":"
        [(MatrixGroups.LinearAlgebra.SpecialLinearGroup.special_linear_group.fin
          "SL("
          (num "2")
          ", "
          (Data.Real.Basic.termℝ "ℝ")
          ")")]
        ")")
       ":"
       [(Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
         "GL("
         (num "2")
         ", "
         (Data.Real.Basic.termℝ "ℝ")
         ")"
         "⁺")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
       "GL("
       (num "2")
       ", "
       (Data.Real.Basic.termℝ "ℝ")
       ")"
       "⁺")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»', expected 'Analysis.Complex.UpperHalfPlane.Basic.termGL(_,_)⁺._@.Analysis.Complex.UpperHalfPlane.Basic._hyg.63'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance : Coe SL( 2 , ℤ ) GL( 2 , ℝ ) ⁺ := ⟨ fun g => ( ( g : SL( 2 , ℝ ) ) : GL( 2 , ℝ ) ⁺ ) ⟩

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `sLOnGLPos [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `HasSmul
         [(MatrixGroups.LinearAlgebra.SpecialLinearGroup.special_linear_group.fin
           "SL("
           (num "2")
           ", "
           (termℤ "ℤ")
           ")")
          (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
           "GL("
           (num "2")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")"
           "⁺")])))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.fun "fun" (Term.basicFun [`s `g] [] "=>" («term_*_» `s "*" `g)))]
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
       [(Term.fun "fun" (Term.basicFun [`s `g] [] "=>" («term_*_» `s "*" `g)))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`s `g] [] "=>" («term_*_» `s "*" `g)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `s "*" `g)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
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
      `s
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `HasSmul
       [(MatrixGroups.LinearAlgebra.SpecialLinearGroup.special_linear_group.fin
         "SL("
         (num "2")
         ", "
         (termℤ "ℤ")
         ")")
        (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
         "GL("
         (num "2")
         ", "
         (Data.Real.Basic.termℝ "ℝ")
         ")"
         "⁺")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
       "GL("
       (num "2")
       ", "
       (Data.Real.Basic.termℝ "ℝ")
       ")"
       "⁺")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»', expected 'Analysis.Complex.UpperHalfPlane.Basic.termGL(_,_)⁺._@.Analysis.Complex.UpperHalfPlane.Basic._hyg.63'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance sLOnGLPos : HasSmul SL( 2 , ℤ ) GL( 2 , ℝ ) ⁺ := ⟨ fun s g => s * g ⟩
#align upper_half_plane.SL_on_GL_pos UpperHalfPlane.sLOnGLPos

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `SL_on_GL_pos_smul_apply [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`s]
         [":"
          (MatrixGroups.LinearAlgebra.SpecialLinearGroup.special_linear_group.fin
           "SL("
           (num "2")
           ", "
           (termℤ "ℤ")
           ")")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`g]
         [":"
          (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
           "GL("
           (num "2")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")"
           "⁺")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`z]
         [":" (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Algebra.Group.Defs.«term_•_» (Algebra.Group.Defs.«term_•_» `s " • " `g) " • " `z)
         "="
         (Algebra.Group.Defs.«term_•_»
          («term_*_»
           (Term.typeAscription
            "("
            `s
            ":"
            [(Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
              "GL("
              (num "2")
              ", "
              (Data.Real.Basic.termℝ "ℝ")
              ")"
              "⁺")]
            ")")
           "*"
           `g)
          " • "
          `z))))
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
       (Algebra.Group.Defs.«term_•_» (Algebra.Group.Defs.«term_•_» `s " • " `g) " • " `z)
       "="
       (Algebra.Group.Defs.«term_•_»
        («term_*_»
         (Term.typeAscription
          "("
          `s
          ":"
          [(Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
            "GL("
            (num "2")
            ", "
            (Data.Real.Basic.termℝ "ℝ")
            ")"
            "⁺")]
          ")")
         "*"
         `g)
        " • "
        `z))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_»
       («term_*_»
        (Term.typeAscription
         "("
         `s
         ":"
         [(Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
           "GL("
           (num "2")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")"
           "⁺")]
         ")")
        "*"
        `g)
       " • "
       `z)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      («term_*_»
       (Term.typeAscription
        "("
        `s
        ":"
        [(Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
          "GL("
          (num "2")
          ", "
          (Data.Real.Basic.termℝ "ℝ")
          ")"
          "⁺")]
        ")")
       "*"
       `g)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.typeAscription
       "("
       `s
       ":"
       [(Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
         "GL("
         (num "2")
         ", "
         (Data.Real.Basic.termℝ "ℝ")
         ")"
         "⁺")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
       "GL("
       (num "2")
       ", "
       (Data.Real.Basic.termℝ "ℝ")
       ")"
       "⁺")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»', expected 'Analysis.Complex.UpperHalfPlane.Basic.termGL(_,_)⁺._@.Analysis.Complex.UpperHalfPlane.Basic._hyg.63'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  SL_on_GL_pos_smul_apply
  ( s : SL( 2 , ℤ ) ) ( g : GL( 2 , ℝ ) ⁺ ) ( z : ℍ ) : s • g • z = ( s : GL( 2 , ℝ ) ⁺ ) * g • z
  := rfl
#align upper_half_plane.SL_on_GL_pos_smul_apply UpperHalfPlane.SL_on_GL_pos_smul_apply

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `SL_to_GL_tower [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `IsScalarTower
         [(MatrixGroups.LinearAlgebra.SpecialLinearGroup.special_linear_group.fin
           "SL("
           (num "2")
           ", "
           (termℤ "ℤ")
           ")")
          (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
           "GL("
           (num "2")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")"
           "⁺")
          (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")])))
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `smul_assoc
           []
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.intro "intro" [`s `g `z])
               []
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `SL_on_GL_pos_smul_apply)
                  ","
                  (Tactic.simpLemma [] [] `coe_coe)]
                 "]"]
                [])
               []
               (Tactic.apply "apply" `mul_smul')]))))))]
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
         [(Tactic.intro "intro" [`s `g `z])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `SL_on_GL_pos_smul_apply)
             ","
             (Tactic.simpLemma [] [] `coe_coe)]
            "]"]
           [])
          []
          (Tactic.apply "apply" `mul_smul')])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `mul_smul')
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_smul'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `SL_on_GL_pos_smul_apply) "," (Tactic.simpLemma [] [] `coe_coe)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `SL_on_GL_pos_smul_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`s `g `z])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `IsScalarTower
       [(MatrixGroups.LinearAlgebra.SpecialLinearGroup.special_linear_group.fin
         "SL("
         (num "2")
         ", "
         (termℤ "ℤ")
         ")")
        (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
         "GL("
         (num "2")
         ", "
         (Data.Real.Basic.termℝ "ℝ")
         ")"
         "⁺")
        (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
       "GL("
       (num "2")
       ", "
       (Data.Real.Basic.termℝ "ℝ")
       ")"
       "⁺")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»', expected 'Analysis.Complex.UpperHalfPlane.Basic.termGL(_,_)⁺._@.Analysis.Complex.UpperHalfPlane.Basic._hyg.63'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  SL_to_GL_tower
  : IsScalarTower SL( 2 , ℤ ) GL( 2 , ℝ ) ⁺ ℍ
  where smul_assoc := by intro s g z simp only [ SL_on_GL_pos_smul_apply , coe_coe ] apply mul_smul'
#align upper_half_plane.SL_to_GL_tower UpperHalfPlane.SL_to_GL_tower

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `subgroupGLPos [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `HasSmul
         [`Γ
          (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
           "GL("
           (num "2")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")"
           "⁺")])))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.fun "fun" (Term.basicFun [`s `g] [] "=>" («term_*_» `s "*" `g)))]
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
       [(Term.fun "fun" (Term.basicFun [`s `g] [] "=>" («term_*_» `s "*" `g)))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`s `g] [] "=>" («term_*_» `s "*" `g)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `s "*" `g)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
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
      `s
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `HasSmul
       [`Γ
        (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
         "GL("
         (num "2")
         ", "
         (Data.Real.Basic.termℝ "ℝ")
         ")"
         "⁺")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
       "GL("
       (num "2")
       ", "
       (Data.Real.Basic.termℝ "ℝ")
       ")"
       "⁺")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»', expected 'Analysis.Complex.UpperHalfPlane.Basic.termGL(_,_)⁺._@.Analysis.Complex.UpperHalfPlane.Basic._hyg.63'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance subgroupGLPos : HasSmul Γ GL( 2 , ℝ ) ⁺ := ⟨ fun s g => s * g ⟩
#align upper_half_plane.subgroup_GL_pos UpperHalfPlane.subgroupGLPos

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `subgroup_on_GL_pos_smul_apply [])
      (Command.declSig
       [(Term.explicitBinder "(" [`s] [":" `Γ] [] ")")
        (Term.explicitBinder
         "("
         [`g]
         [":"
          (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
           "GL("
           (num "2")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")"
           "⁺")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`z]
         [":" (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Algebra.Group.Defs.«term_•_» (Algebra.Group.Defs.«term_•_» `s " • " `g) " • " `z)
         "="
         (Algebra.Group.Defs.«term_•_»
          («term_*_»
           (Term.typeAscription
            "("
            `s
            ":"
            [(Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
              "GL("
              (num "2")
              ", "
              (Data.Real.Basic.termℝ "ℝ")
              ")"
              "⁺")]
            ")")
           "*"
           `g)
          " • "
          `z))))
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
       (Algebra.Group.Defs.«term_•_» (Algebra.Group.Defs.«term_•_» `s " • " `g) " • " `z)
       "="
       (Algebra.Group.Defs.«term_•_»
        («term_*_»
         (Term.typeAscription
          "("
          `s
          ":"
          [(Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
            "GL("
            (num "2")
            ", "
            (Data.Real.Basic.termℝ "ℝ")
            ")"
            "⁺")]
          ")")
         "*"
         `g)
        " • "
        `z))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_»
       («term_*_»
        (Term.typeAscription
         "("
         `s
         ":"
         [(Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
           "GL("
           (num "2")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")"
           "⁺")]
         ")")
        "*"
        `g)
       " • "
       `z)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      («term_*_»
       (Term.typeAscription
        "("
        `s
        ":"
        [(Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
          "GL("
          (num "2")
          ", "
          (Data.Real.Basic.termℝ "ℝ")
          ")"
          "⁺")]
        ")")
       "*"
       `g)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.typeAscription
       "("
       `s
       ":"
       [(Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
         "GL("
         (num "2")
         ", "
         (Data.Real.Basic.termℝ "ℝ")
         ")"
         "⁺")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
       "GL("
       (num "2")
       ", "
       (Data.Real.Basic.termℝ "ℝ")
       ")"
       "⁺")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»', expected 'Analysis.Complex.UpperHalfPlane.Basic.termGL(_,_)⁺._@.Analysis.Complex.UpperHalfPlane.Basic._hyg.63'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  subgroup_on_GL_pos_smul_apply
  ( s : Γ ) ( g : GL( 2 , ℝ ) ⁺ ) ( z : ℍ ) : s • g • z = ( s : GL( 2 , ℝ ) ⁺ ) * g • z
  := rfl
#align upper_half_plane.subgroup_on_GL_pos_smul_apply UpperHalfPlane.subgroup_on_GL_pos_smul_apply

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `subgroup_on_GL_pos [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `IsScalarTower
         [`Γ
          (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
           "GL("
           (num "2")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")"
           "⁺")
          (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")])))
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `smul_assoc
           []
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.intro "intro" [`s `g `z])
               []
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `subgroup_on_GL_pos_smul_apply)
                  ","
                  (Tactic.simpLemma [] [] `coe_coe)]
                 "]"]
                [])
               []
               (Tactic.apply "apply" `mul_smul')]))))))]
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
         [(Tactic.intro "intro" [`s `g `z])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `subgroup_on_GL_pos_smul_apply)
             ","
             (Tactic.simpLemma [] [] `coe_coe)]
            "]"]
           [])
          []
          (Tactic.apply "apply" `mul_smul')])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `mul_smul')
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_smul'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `subgroup_on_GL_pos_smul_apply)
         ","
         (Tactic.simpLemma [] [] `coe_coe)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `subgroup_on_GL_pos_smul_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`s `g `z])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `IsScalarTower
       [`Γ
        (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
         "GL("
         (num "2")
         ", "
         (Data.Real.Basic.termℝ "ℝ")
         ")"
         "⁺")
        (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
       "GL("
       (num "2")
       ", "
       (Data.Real.Basic.termℝ "ℝ")
       ")"
       "⁺")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»', expected 'Analysis.Complex.UpperHalfPlane.Basic.termGL(_,_)⁺._@.Analysis.Complex.UpperHalfPlane.Basic._hyg.63'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  subgroup_on_GL_pos
  : IsScalarTower Γ GL( 2 , ℝ ) ⁺ ℍ
  where
    smul_assoc
      :=
      by intro s g z simp only [ subgroup_on_GL_pos_smul_apply , coe_coe ] apply mul_smul'
#align upper_half_plane.subgroup_on_GL_pos UpperHalfPlane.subgroup_on_GL_pos

instance subgroupSL : HasSmul Γ SL(2, ℤ) :=
  ⟨fun s g => s * g⟩
#align upper_half_plane.subgroup_SL UpperHalfPlane.subgroupSL

theorem subgroup_on_SL_apply (s : Γ) (g : SL(2, ℤ)) (z : ℍ) :
    (s • g) • z = ((s : SL(2, ℤ)) * g) • z :=
  rfl
#align upper_half_plane.subgroup_on_SL_apply UpperHalfPlane.subgroup_on_SL_apply

instance subgroup_to_SL_tower : IsScalarTower Γ SL(2, ℤ) ℍ
    where smul_assoc s g z := by
    rw [subgroup_on_SL_apply]
    apply MulAction.mul_smul
#align upper_half_plane.subgroup_to_SL_tower UpperHalfPlane.subgroup_to_SL_tower

end ModularScalarTowers

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
      (Command.declId `coe_smul [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`g]
         [":"
          (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
           "GL("
           (num "2")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")"
           "⁺")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`z]
         [":" (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (coeNotation "↑" (Algebra.Group.Defs.«term_•_» `g " • " `z))
         "="
         («term_/_» (Term.app `num [`g `z]) "/" (Term.app `denom [`g `z])))))
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
       (coeNotation "↑" (Algebra.Group.Defs.«term_•_» `g " • " `z))
       "="
       («term_/_» (Term.app `num [`g `z]) "/" (Term.app `denom [`g `z])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» (Term.app `num [`g `z]) "/" (Term.app `denom [`g `z]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `denom [`g `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `denom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `num [`g `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `num
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (coeNotation "↑" (Algebra.Group.Defs.«term_•_» `g " • " `z))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_» `g " • " `z)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Group.Defs.«term_•_» `g " • " `z)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (some 1024, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
       "GL("
       (num "2")
       ", "
       (Data.Real.Basic.termℝ "ℝ")
       ")"
       "⁺")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»', expected 'Analysis.Complex.UpperHalfPlane.Basic.termGL(_,_)⁺._@.Analysis.Complex.UpperHalfPlane.Basic._hyg.63'
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
@[ simp ] theorem coe_smul ( g : GL( 2 , ℝ ) ⁺ ) ( z : ℍ ) : ↑ g • z = num g z / denom g z := rfl
#align upper_half_plane.coe_smul UpperHalfPlane.coe_smul

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
      (Command.declId `re_smul [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`g]
         [":"
          (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
           "GL("
           (num "2")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")"
           "⁺")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`z]
         [":" (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)
         "="
         (Term.proj («term_/_» (Term.app `num [`g `z]) "/" (Term.app `denom [`g `z])) "." `re))))
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
       (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)
       "="
       (Term.proj («term_/_» (Term.app `num [`g `z]) "/" (Term.app `denom [`g `z])) "." `re))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj («term_/_» (Term.app `num [`g `z]) "/" (Term.app `denom [`g `z])) "." `re)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_/_» (Term.app `num [`g `z]) "/" (Term.app `denom [`g `z]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `denom [`g `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `denom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `num [`g `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `num
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_/_» (Term.app `num [`g `z]) "/" (Term.app `denom [`g `z]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `re)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Algebra.Group.Defs.«term_•_» `g " • " `z)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 73, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Group.Defs.«term_•_» `g " • " `z)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
       "GL("
       (num "2")
       ", "
       (Data.Real.Basic.termℝ "ℝ")
       ")"
       "⁺")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»', expected 'Analysis.Complex.UpperHalfPlane.Basic.termGL(_,_)⁺._@.Analysis.Complex.UpperHalfPlane.Basic._hyg.63'
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
@[ simp ]
  theorem re_smul ( g : GL( 2 , ℝ ) ⁺ ) ( z : ℍ ) : g • z . re = num g z / denom g z . re := rfl
#align upper_half_plane.re_smul UpperHalfPlane.re_smul

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `im_smul [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`g]
         [":"
          (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
           "GL("
           (num "2")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")"
           "⁺")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`z]
         [":" (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `im)
         "="
         (Term.proj («term_/_» (Term.app `num [`g `z]) "/" (Term.app `denom [`g `z])) "." `im))))
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
       (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `im)
       "="
       (Term.proj («term_/_» (Term.app `num [`g `z]) "/" (Term.app `denom [`g `z])) "." `im))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj («term_/_» (Term.app `num [`g `z]) "/" (Term.app `denom [`g `z])) "." `im)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_/_» (Term.app `num [`g `z]) "/" (Term.app `denom [`g `z]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `denom [`g `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `denom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `num [`g `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `num
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_/_» (Term.app `num [`g `z]) "/" (Term.app `denom [`g `z]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `im)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Algebra.Group.Defs.«term_•_» `g " • " `z)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 73, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Group.Defs.«term_•_» `g " • " `z)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
       "GL("
       (num "2")
       ", "
       (Data.Real.Basic.termℝ "ℝ")
       ")"
       "⁺")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»', expected 'Analysis.Complex.UpperHalfPlane.Basic.termGL(_,_)⁺._@.Analysis.Complex.UpperHalfPlane.Basic._hyg.63'
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
theorem im_smul ( g : GL( 2 , ℝ ) ⁺ ) ( z : ℍ ) : g • z . im = num g z / denom g z . im := rfl
#align upper_half_plane.im_smul UpperHalfPlane.im_smul

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `im_smul_eq_div_norm_sq [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`g]
         [":"
          (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
           "GL("
           (num "2")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")"
           "⁺")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`z]
         [":" (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `im)
         "="
         («term_/_»
          («term_*_»
           (Term.app `det [(Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g)])
           "*"
           (Term.proj `z "." `im))
          "/"
          (Term.app `Complex.normSq [(Term.app `denom [`g `z])])))))
      (Command.declValSimple ":=" (Term.app `smul_aux'_im [`g `z]) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `smul_aux'_im [`g `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `smul_aux'_im
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.proj (Algebra.Group.Defs.«term_•_» `g " • " `z) "." `im)
       "="
       («term_/_»
        («term_*_»
         (Term.app `det [(Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g)])
         "*"
         (Term.proj `z "." `im))
        "/"
        (Term.app `Complex.normSq [(Term.app `denom [`g `z])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_»
       («term_*_»
        (Term.app `det [(Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g)])
        "*"
        (Term.proj `z "." `im))
       "/"
       (Term.app `Complex.normSq [(Term.app `denom [`g `z])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Complex.normSq [(Term.app `denom [`g `z])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `denom [`g `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `denom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `denom [`g `z]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Complex.normSq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_*_»
       (Term.app `det [(Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g)])
       "*"
       (Term.proj `z "." `im))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `z "." `im)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `z
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `det [(Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_»', expected 'Analysis.Complex.UpperHalfPlane.Basic.term↑ₘ_._@.Analysis.Complex.UpperHalfPlane.Basic._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  im_smul_eq_div_norm_sq
  ( g : GL( 2 , ℝ ) ⁺ ) ( z : ℍ ) : g • z . im = det ↑ₘ g * z . im / Complex.normSq denom g z
  := smul_aux'_im g z
#align upper_half_plane.im_smul_eq_div_norm_sq UpperHalfPlane.im_smul_eq_div_norm_sq

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
      (Command.declId `neg_smul [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`g]
         [":"
          (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
           "GL("
           (num "2")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")"
           "⁺")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`z]
         [":" (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Algebra.Group.Defs.«term_•_» («term-_» "-" `g) " • " `z)
         "="
         (Algebra.Group.Defs.«term_•_» `g " • " `z))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.Ext.tacticExt1___ "ext1" [])
           []
           (Tactic.change
            "change"
            («term_=_»
             («term_/_» (Term.hole "_") "/" (Term.hole "_"))
             "="
             («term_/_» (Term.hole "_") "/" (Term.hole "_")))
            [])
           []
           (Tactic.fieldSimp
            "field_simp"
            []
            []
            []
            [(Tactic.simpArgs
              "["
              [(Tactic.simpLemma [] [] `denom_ne_zero)
               ","
               (Tactic.simpErase "-" `denom)
               ","
               (Tactic.simpErase "-" `Num)]
              "]")]
            [])
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `Num)
              ","
              (Tactic.simpLemma [] [] `denom)
              ","
              (Tactic.simpLemma [] [] `coe_coe)
              ","
              (Tactic.simpLemma [] [] `Complex.of_real_neg)
              ","
              (Tactic.simpLemma [] [] `neg_mul)
              ","
              (Tactic.simpLemma [] [] `GL_pos.coe_neg_GL)
              ","
              (Tactic.simpLemma [] [] `Units.val_neg)
              ","
              (Tactic.simpLemma [] [] `Pi.neg_apply)]
             "]"]
            [])
           []
           (Mathlib.Tactic.RingNF.ringNF "ring_nf" [] [] [])])))
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
         [(Std.Tactic.Ext.tacticExt1___ "ext1" [])
          []
          (Tactic.change
           "change"
           («term_=_»
            («term_/_» (Term.hole "_") "/" (Term.hole "_"))
            "="
            («term_/_» (Term.hole "_") "/" (Term.hole "_")))
           [])
          []
          (Tactic.fieldSimp
           "field_simp"
           []
           []
           []
           [(Tactic.simpArgs
             "["
             [(Tactic.simpLemma [] [] `denom_ne_zero)
              ","
              (Tactic.simpErase "-" `denom)
              ","
              (Tactic.simpErase "-" `Num)]
             "]")]
           [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `Num)
             ","
             (Tactic.simpLemma [] [] `denom)
             ","
             (Tactic.simpLemma [] [] `coe_coe)
             ","
             (Tactic.simpLemma [] [] `Complex.of_real_neg)
             ","
             (Tactic.simpLemma [] [] `neg_mul)
             ","
             (Tactic.simpLemma [] [] `GL_pos.coe_neg_GL)
             ","
             (Tactic.simpLemma [] [] `Units.val_neg)
             ","
             (Tactic.simpLemma [] [] `Pi.neg_apply)]
            "]"]
           [])
          []
          (Mathlib.Tactic.RingNF.ringNF "ring_nf" [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.RingNF.ringNF "ring_nf" [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `Num)
         ","
         (Tactic.simpLemma [] [] `denom)
         ","
         (Tactic.simpLemma [] [] `coe_coe)
         ","
         (Tactic.simpLemma [] [] `Complex.of_real_neg)
         ","
         (Tactic.simpLemma [] [] `neg_mul)
         ","
         (Tactic.simpLemma [] [] `GL_pos.coe_neg_GL)
         ","
         (Tactic.simpLemma [] [] `Units.val_neg)
         ","
         (Tactic.simpLemma [] [] `Pi.neg_apply)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Pi.neg_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Units.val_neg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `GL_pos.coe_neg_GL
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `neg_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Complex.of_real_neg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `denom
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Num
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.fieldSimp
       "field_simp"
       []
       []
       []
       [(Tactic.simpArgs
         "["
         [(Tactic.simpLemma [] [] `denom_ne_zero)
          ","
          (Tactic.simpErase "-" `denom)
          ","
          (Tactic.simpErase "-" `Num)]
         "]")]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpErase', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Num
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpErase', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `denom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `denom_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       («term_=_»
        («term_/_» (Term.hole "_") "/" (Term.hole "_"))
        "="
        («term_/_» (Term.hole "_") "/" (Term.hole "_")))
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       («term_/_» (Term.hole "_") "/" (Term.hole "_"))
       "="
       («term_/_» (Term.hole "_") "/" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» (Term.hole "_") "/" (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_/_» (Term.hole "_") "/" (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.tacticExt1___ "ext1" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Algebra.Group.Defs.«term_•_» («term-_» "-" `g) " • " `z)
       "="
       (Algebra.Group.Defs.«term_•_» `g " • " `z))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_» `g " • " `z)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Algebra.Group.Defs.«term_•_» («term-_» "-" `g) " • " `z)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      («term-_» "-" `g)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 74 >? 75, (some 75, term) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 73, (some 73, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
       "GL("
       (num "2")
       ", "
       (Data.Real.Basic.termℝ "ℝ")
       ")"
       "⁺")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»', expected 'Analysis.Complex.UpperHalfPlane.Basic.termGL(_,_)⁺._@.Analysis.Complex.UpperHalfPlane.Basic._hyg.63'
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
@[ simp ]
  theorem
    neg_smul
    ( g : GL( 2 , ℝ ) ⁺ ) ( z : ℍ ) : - g • z = g • z
    :=
      by
        ext1
          change _ / _ = _ / _
          field_simp [ denom_ne_zero , - denom , - Num ]
          simp
            only
            [
              Num
                ,
                denom
                ,
                coe_coe
                ,
                Complex.of_real_neg
                ,
                neg_mul
                ,
                GL_pos.coe_neg_GL
                ,
                Units.val_neg
                ,
                Pi.neg_apply
              ]
          ring_nf
#align upper_half_plane.neg_smul UpperHalfPlane.neg_smul

section SLModularAction

variable (g : SL(2, ℤ)) (z : ℍ) (Γ : Subgroup SL(2, ℤ))

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
      (Command.declId `sl_moeb [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`A]
         [":"
          (MatrixGroups.LinearAlgebra.SpecialLinearGroup.special_linear_group.fin
           "SL("
           (num "2")
           ", "
           (termℤ "ℤ")
           ")")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`z]
         [":" (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Algebra.Group.Defs.«term_•_» `A " • " `z)
         "="
         (Algebra.Group.Defs.«term_•_»
          (Term.typeAscription
           "("
           `A
           ":"
           [(Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
             "GL("
             (num "2")
             ", "
             (Data.Real.Basic.termℝ "ℝ")
             ")"
             "⁺")]
           ")")
          " • "
          `z))))
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
       (Algebra.Group.Defs.«term_•_» `A " • " `z)
       "="
       (Algebra.Group.Defs.«term_•_»
        (Term.typeAscription
         "("
         `A
         ":"
         [(Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
           "GL("
           (num "2")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")"
           "⁺")]
         ")")
        " • "
        `z))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_»
       (Term.typeAscription
        "("
        `A
        ":"
        [(Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
          "GL("
          (num "2")
          ", "
          (Data.Real.Basic.termℝ "ℝ")
          ")"
          "⁺")]
        ")")
       " • "
       `z)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      (Term.typeAscription
       "("
       `A
       ":"
       [(Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
         "GL("
         (num "2")
         ", "
         (Data.Real.Basic.termℝ "ℝ")
         ")"
         "⁺")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
       "GL("
       (num "2")
       ", "
       (Data.Real.Basic.termℝ "ℝ")
       ")"
       "⁺")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»', expected 'Analysis.Complex.UpperHalfPlane.Basic.termGL(_,_)⁺._@.Analysis.Complex.UpperHalfPlane.Basic._hyg.63'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ] theorem sl_moeb ( A : SL( 2 , ℤ ) ) ( z : ℍ ) : A • z = ( A : GL( 2 , ℝ ) ⁺ ) • z := rfl
#align upper_half_plane.sl_moeb UpperHalfPlane.sl_moeb

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `subgroup_moeb [])
      (Command.declSig
       [(Term.explicitBinder "(" [`A] [":" `Γ] [] ")")
        (Term.explicitBinder
         "("
         [`z]
         [":" (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Algebra.Group.Defs.«term_•_» `A " • " `z)
         "="
         (Algebra.Group.Defs.«term_•_»
          (Term.typeAscription
           "("
           `A
           ":"
           [(Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
             "GL("
             (num "2")
             ", "
             (Data.Real.Basic.termℝ "ℝ")
             ")"
             "⁺")]
           ")")
          " • "
          `z))))
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
       (Algebra.Group.Defs.«term_•_» `A " • " `z)
       "="
       (Algebra.Group.Defs.«term_•_»
        (Term.typeAscription
         "("
         `A
         ":"
         [(Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
           "GL("
           (num "2")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")"
           "⁺")]
         ")")
        " • "
        `z))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_»
       (Term.typeAscription
        "("
        `A
        ":"
        [(Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
          "GL("
          (num "2")
          ", "
          (Data.Real.Basic.termℝ "ℝ")
          ")"
          "⁺")]
        ")")
       " • "
       `z)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      (Term.typeAscription
       "("
       `A
       ":"
       [(Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
         "GL("
         (num "2")
         ", "
         (Data.Real.Basic.termℝ "ℝ")
         ")"
         "⁺")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»
       "GL("
       (num "2")
       ", "
       (Data.Real.Basic.termℝ "ℝ")
       ")"
       "⁺")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«termGL(_,_)⁺»', expected 'Analysis.Complex.UpperHalfPlane.Basic.termGL(_,_)⁺._@.Analysis.Complex.UpperHalfPlane.Basic._hyg.63'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem subgroup_moeb ( A : Γ ) ( z : ℍ ) : A • z = ( A : GL( 2 , ℝ ) ⁺ ) • z := rfl
#align upper_half_plane.subgroup_moeb UpperHalfPlane.subgroup_moeb

@[simp]
theorem subgroup_to_sl_moeb (A : Γ) (z : ℍ) : A • z = (A : SL(2, ℤ)) • z :=
  rfl
#align upper_half_plane.subgroup_to_sl_moeb UpperHalfPlane.subgroup_to_sl_moeb

@[simp]
theorem SL_neg_smul (g : SL(2, ℤ)) (z : ℍ) : -g • z = g • z := by
  simp only [coe_GL_pos_neg, sl_moeb, coe_coe, coe_int_neg, neg_smul]
#align upper_half_plane.SL_neg_smul UpperHalfPlane.SL_neg_smul

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `c_mul_im_sq_le_norm_sq_denom [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`z]
         [":" (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`g]
         [":"
          (MatrixGroups.LinearAlgebra.SpecialLinearGroup.special_linear_group.fin
           "SL("
           (num "2")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         («term_^_»
          («term_*_»
           (Term.typeAscription
            "("
            (Term.app
             (Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g)
             [(num "1") (num "0")])
            ":"
            [(Data.Real.Basic.termℝ "ℝ")]
            ")")
           "*"
           (Term.proj `z "." `im))
          "^"
          (num "2"))
         "≤"
         (Term.app `Complex.normSq [(Term.app `denom [`g `z])]))))
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
              `c
              []
              []
              ":="
              (Term.typeAscription
               "("
               (Term.app
                (Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g)
                [(num "1") (num "0")])
               ":"
               [(Data.Real.Basic.termℝ "ℝ")]
               ")"))))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `d
              []
              []
              ":="
              (Term.typeAscription
               "("
               (Term.app
                (Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g)
                [(num "1") (num "1")])
               ":"
               [(Data.Real.Basic.termℝ "ℝ")]
               ")"))))
           []
           (calcTactic
            "calc"
            (calcStep
             («term_≤_»
              («term_^_» («term_*_» `c "*" `z.im) "^" (num "2"))
              "≤"
              («term_+_»
               («term_^_» («term_*_» `c "*" `z.im) "^" (num "2"))
               "+"
               («term_^_» («term_+_» («term_*_» `c "*" `z.re) "+" `d) "^" (num "2"))))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(choice
                  (Tactic.nlinarith "nlinarith" [] [] [])
                  (nlinarith "nlinarith" [] (linarithArgsRest [] [] [])))]))))
            [(calcStep
              («term_=_» (Term.hole "_") "=" (Term.app `Complex.normSq [(Term.app `denom [`g `z])]))
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.«tactic_<;>_»
                   (Tactic.simp
                    "simp"
                    []
                    []
                    []
                    ["[" [(Tactic.simpLemma [] [] `Complex.normSq)] "]"]
                    [])
                   "<;>"
                   (Mathlib.Tactic.RingNF.ring "ring"))]))))])])))
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
             `c
             []
             []
             ":="
             (Term.typeAscription
              "("
              (Term.app
               (Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g)
               [(num "1") (num "0")])
              ":"
              [(Data.Real.Basic.termℝ "ℝ")]
              ")"))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `d
             []
             []
             ":="
             (Term.typeAscription
              "("
              (Term.app
               (Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g)
               [(num "1") (num "1")])
              ":"
              [(Data.Real.Basic.termℝ "ℝ")]
              ")"))))
          []
          (calcTactic
           "calc"
           (calcStep
            («term_≤_»
             («term_^_» («term_*_» `c "*" `z.im) "^" (num "2"))
             "≤"
             («term_+_»
              («term_^_» («term_*_» `c "*" `z.im) "^" (num "2"))
              "+"
              («term_^_» («term_+_» («term_*_» `c "*" `z.re) "+" `d) "^" (num "2"))))
            ":="
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(choice
                 (Tactic.nlinarith "nlinarith" [] [] [])
                 (nlinarith "nlinarith" [] (linarithArgsRest [] [] [])))]))))
           [(calcStep
             («term_=_» (Term.hole "_") "=" (Term.app `Complex.normSq [(Term.app `denom [`g `z])]))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.«tactic_<;>_»
                  (Tactic.simp
                   "simp"
                   []
                   []
                   []
                   ["[" [(Tactic.simpLemma [] [] `Complex.normSq)] "]"]
                   [])
                  "<;>"
                  (Mathlib.Tactic.RingNF.ring "ring"))]))))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_≤_»
         («term_^_» («term_*_» `c "*" `z.im) "^" (num "2"))
         "≤"
         («term_+_»
          («term_^_» («term_*_» `c "*" `z.im) "^" (num "2"))
          "+"
          («term_^_» («term_+_» («term_*_» `c "*" `z.re) "+" `d) "^" (num "2"))))
        ":="
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(choice
             (Tactic.nlinarith "nlinarith" [] [] [])
             (nlinarith "nlinarith" [] (linarithArgsRest [] [] [])))]))))
       [(calcStep
         («term_=_» (Term.hole "_") "=" (Term.app `Complex.normSq [(Term.app `denom [`g `z])]))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.«tactic_<;>_»
              (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Complex.normSq)] "]"] [])
              "<;>"
              (Mathlib.Tactic.RingNF.ring "ring"))]))))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Complex.normSq)] "]"] [])
           "<;>"
           (Mathlib.Tactic.RingNF.ring "ring"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Complex.normSq)] "]"] [])
       "<;>"
       (Mathlib.Tactic.RingNF.ring "ring"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.RingNF.ring "ring")
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Complex.normSq)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Complex.normSq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.hole "_") "=" (Term.app `Complex.normSq [(Term.app `denom [`g `z])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Complex.normSq [(Term.app `denom [`g `z])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `denom [`g `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `denom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `denom [`g `z]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Complex.normSq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(choice
           (Tactic.nlinarith "nlinarith" [] [] [])
           (nlinarith "nlinarith" [] (linarithArgsRest [] [] [])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (choice
       (Tactic.nlinarith "nlinarith" [] [] [])
       (nlinarith "nlinarith" [] (linarithArgsRest [] [] [])))
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       («term_^_» («term_*_» `c "*" `z.im) "^" (num "2"))
       "≤"
       («term_+_»
        («term_^_» («term_*_» `c "*" `z.im) "^" (num "2"))
        "+"
        («term_^_» («term_+_» («term_*_» `c "*" `z.re) "+" `d) "^" (num "2"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       («term_^_» («term_*_» `c "*" `z.im) "^" (num "2"))
       "+"
       («term_^_» («term_+_» («term_*_» `c "*" `z.re) "+" `d) "^" (num "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» («term_+_» («term_*_» `c "*" `z.re) "+" `d) "^" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      («term_+_» («term_*_» `c "*" `z.re) "+" `d)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `d
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_*_» `c "*" `z.re)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z.re
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 70, (some 71, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 65, (some 66, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_+_» («term_*_» `c "*" `z.re) "+" `d)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_^_» («term_*_» `c "*" `z.im) "^" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      («term_*_» `c "*" `z.im)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z.im
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 70, (some 71, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_*_» `c "*" `z.im) ")")
[PrettyPrinter.parenthesize] ...precedences are 65 >? 80, (some 80, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_^_» («term_*_» `c "*" `z.im) "^" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      («term_*_» `c "*" `z.im)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z.im
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 70, (some 71, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_*_» `c "*" `z.im) ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticLet_
       "let"
       (Term.letDecl
        (Term.letIdDecl
         `d
         []
         []
         ":="
         (Term.typeAscription
          "("
          (Term.app (Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g) [(num "1") (num "1")])
          ":"
          [(Data.Real.Basic.termℝ "ℝ")]
          ")"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.app (Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g) [(num "1") (num "1")])
       ":"
       [(Data.Real.Basic.termℝ "ℝ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g) [(num "1") (num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_» "↑ₘ" `g)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.UpperHalfPlane.Basic.«term↑ₘ_»', expected 'Analysis.Complex.UpperHalfPlane.Basic.term↑ₘ_._@.Analysis.Complex.UpperHalfPlane.Basic._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letEqnsDecl'
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
  c_mul_im_sq_le_norm_sq_denom
  ( z : ℍ ) ( g : SL( 2 , ℝ ) ) : ( ↑ₘ g 1 0 : ℝ ) * z . im ^ 2 ≤ Complex.normSq denom g z
  :=
    by
      let c := ( ↑ₘ g 1 0 : ℝ )
        let d := ( ↑ₘ g 1 1 : ℝ )
        calc
          c * z.im ^ 2 ≤ c * z.im ^ 2 + c * z.re + d ^ 2 := by nlinarith nlinarith
          _ = Complex.normSq denom g z := by simp [ Complex.normSq ] <;> ring
#align upper_half_plane.c_mul_im_sq_le_norm_sq_denom UpperHalfPlane.c_mul_im_sq_le_norm_sq_denom

theorem SpecialLinearGroup.im_smul_eq_div_norm_sq :
    (g • z).im = z.im / Complex.normSq (denom g z) :=
  by
  convert im_smul_eq_div_norm_sq g z
  simp only [coe_coe, general_linear_group.coe_det_apply, coe_GL_pos_coe_GL_coe_matrix,
    Int.coe_castRingHom, (g : SL(2, ℝ)).Prop, one_mul]
#align
  upper_half_plane.special_linear_group.im_smul_eq_div_norm_sq UpperHalfPlane.SpecialLinearGroup.im_smul_eq_div_norm_sq

theorem denom_apply (g : SL(2, ℤ)) (z : ℍ) :
    denom g z = (↑g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * z + (↑g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 := by
  simp
#align upper_half_plane.denom_apply UpperHalfPlane.denom_apply

end SLModularAction

section PosRealAction

instance posRealAction : MulAction { x : ℝ // 0 < x } ℍ
    where
  smul x z := mk ((x : ℝ) • z) <| by simpa using mul_pos x.2 z.2
  one_smul z := Subtype.ext <| one_smul _ _
  mul_smul x y z := Subtype.ext <| mul_smul (x : ℝ) y (z : ℂ)
#align upper_half_plane.pos_real_action UpperHalfPlane.posRealAction

variable (x : { x : ℝ // 0 < x }) (z : ℍ)

@[simp]
theorem coe_pos_real_smul : ↑(x • z) = (x : ℝ) • (z : ℂ) :=
  rfl
#align upper_half_plane.coe_pos_real_smul UpperHalfPlane.coe_pos_real_smul

@[simp]
theorem pos_real_im : (x • z).im = x * z.im :=
  Complex.smul_im _ _
#align upper_half_plane.pos_real_im UpperHalfPlane.pos_real_im

@[simp]
theorem pos_real_re : (x • z).re = x * z.re :=
  Complex.smul_re _ _
#align upper_half_plane.pos_real_re UpperHalfPlane.pos_real_re

end PosRealAction

section RealAddAction

instance : AddAction ℝ ℍ
    where
  vadd x z := mk (x + z) <| by simpa using z.im_pos
  zero_vadd z := Subtype.ext <| by simp
  add_vadd x y z := Subtype.ext <| by simp [add_assoc]

variable (x : ℝ) (z : ℍ)

@[simp]
theorem coe_vadd : ↑(x +ᵥ z) = (x + z : ℂ) :=
  rfl
#align upper_half_plane.coe_vadd UpperHalfPlane.coe_vadd

@[simp]
theorem vadd_re : (x +ᵥ z).re = x + z.re :=
  rfl
#align upper_half_plane.vadd_re UpperHalfPlane.vadd_re

@[simp]
theorem vadd_im : (x +ᵥ z).im = z.im :=
  zero_add _
#align upper_half_plane.vadd_im UpperHalfPlane.vadd_im

end RealAddAction

end UpperHalfPlane

