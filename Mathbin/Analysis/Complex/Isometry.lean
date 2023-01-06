/-
Copyright (c) 2021 François Sunatori. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François Sunatori

! This file was ported from Lean 3 source module analysis.complex.isometry
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Complex.Circle
import Mathbin.LinearAlgebra.Determinant
import Mathbin.LinearAlgebra.GeneralLinearGroup

/-!
# Isometries of the Complex Plane

The lemma `linear_isometry_complex` states the classification of isometries in the complex plane.
Specifically, isometries with rotations but without translation.
The proof involves:
1. creating a linear isometry `g` with two fixed points, `g(0) = 0`, `g(1) = 1`
2. applying `linear_isometry_complex_aux` to `g`
The proof of `linear_isometry_complex_aux` is separated in the following parts:
1. show that the real parts match up: `linear_isometry.re_apply_eq_re`
2. show that I maps to either I or -I
3. every z is a linear combination of a + b * I

## References

* [Isometries of the Complex Plane](http://helmut.knaust.info/mediawiki/images/b/b5/Iso.pdf)
-/


noncomputable section

open Complex

open ComplexConjugate

-- mathport name: complex.abs
local notation "|" x "|" => Complex.abs x

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "An element of the unit circle defines a `linear_isometry_equiv` from `ℂ` to itself, by\nrotation. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `rotation [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Algebra.Hom.Group.«term_→*_»
          `circle
          " →* "
          (Analysis.NormedSpace.LinearIsometry.«term_≃ₗᵢ[_]_»
           (Data.Complex.Basic.termℂ "ℂ")
           " ≃ₗᵢ["
           (Data.Real.Basic.termℝ "ℝ")
           "] "
           (Data.Complex.Basic.termℂ "ℂ"))))])
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `toFun
           [`a]
           []
           ":="
           (Term.structInst
            "{"
            [[(Term.app
               `DistribMulAction.toLinearEquiv
               [(Data.Real.Basic.termℝ "ℝ") (Data.Complex.Basic.termℂ "ℂ") `a])]
             "with"]
            [(Term.structInstField
              (Term.structInstLVal `norm_map' [])
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`x]
                []
                "=>"
                (Term.show
                 "show"
                 («term_=_»
                  (Analysis.Complex.Isometry.complex.abs "|" («term_*_» `a "*" `x) "|")
                  "="
                  (Analysis.Complex.Isometry.complex.abs "|" `x "|"))
                 (Term.byTactic'
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [] `map_mul)
                        ","
                        (Tactic.rwRule [] `abs_coe_circle)
                        ","
                        (Tactic.rwRule [] `one_mul)]
                       "]")
                      [])])))))))]
            (Term.optEllipsis [])
            []
            "}"))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `map_one'
           []
           []
           ":="
           («term_<|_» `LinearIsometryEquiv.ext "<|" (Term.app `one_smul [(Term.hole "_")])))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `map_mul'
           [(Term.hole "_") (Term.hole "_")]
           []
           ":="
           («term_<|_»
            `LinearIsometryEquiv.ext
            "<|"
            (Term.app `mul_smul [(Term.hole "_") (Term.hole "_")])))))]
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       `LinearIsometryEquiv.ext
       "<|"
       (Term.app `mul_smul [(Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_smul [(Term.hole "_") (Term.hole "_")])
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
      `mul_smul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `LinearIsometryEquiv.ext
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_» `LinearIsometryEquiv.ext "<|" (Term.app `one_smul [(Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `one_smul [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `one_smul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `LinearIsometryEquiv.ext
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       [[(Term.app
          `DistribMulAction.toLinearEquiv
          [(Data.Real.Basic.termℝ "ℝ") (Data.Complex.Basic.termℂ "ℂ") `a])]
        "with"]
       [(Term.structInstField
         (Term.structInstLVal `norm_map' [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`x]
           []
           "=>"
           (Term.show
            "show"
            («term_=_»
             (Analysis.Complex.Isometry.complex.abs "|" («term_*_» `a "*" `x) "|")
             "="
             (Analysis.Complex.Isometry.complex.abs "|" `x "|"))
            (Term.byTactic'
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `map_mul)
                   ","
                   (Tactic.rwRule [] `abs_coe_circle)
                   ","
                   (Tactic.rwRule [] `one_mul)]
                  "]")
                 [])])))))))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (Term.show
         "show"
         («term_=_»
          (Analysis.Complex.Isometry.complex.abs "|" («term_*_» `a "*" `x) "|")
          "="
          (Analysis.Complex.Isometry.complex.abs "|" `x "|"))
         (Term.byTactic'
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `map_mul)
                ","
                (Tactic.rwRule [] `abs_coe_circle)
                ","
                (Tactic.rwRule [] `one_mul)]
               "]")
              [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       («term_=_»
        (Analysis.Complex.Isometry.complex.abs "|" («term_*_» `a "*" `x) "|")
        "="
        (Analysis.Complex.Isometry.complex.abs "|" `x "|"))
       (Term.byTactic'
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `map_mul)
              ","
              (Tactic.rwRule [] `abs_coe_circle)
              ","
              (Tactic.rwRule [] `one_mul)]
             "]")
            [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `map_mul)
         ","
         (Tactic.rwRule [] `abs_coe_circle)
         ","
         (Tactic.rwRule [] `one_mul)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `abs_coe_circle
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Analysis.Complex.Isometry.complex.abs "|" («term_*_» `a "*" `x) "|")
       "="
       (Analysis.Complex.Isometry.complex.abs "|" `x "|"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Complex.Isometry.complex.abs "|" `x "|")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.Isometry.complex.abs', expected 'Analysis.Complex.Isometry.complex.abs._@.Analysis.Complex.Isometry._hyg.6'
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
    An element of the unit circle defines a `linear_isometry_equiv` from `ℂ` to itself, by
    rotation. -/
  def
    rotation
    : circle →* ℂ ≃ₗᵢ[ ℝ ] ℂ
    where
      toFun
          a
          :=
          {
            DistribMulAction.toLinearEquiv ℝ ℂ a with
            norm_map'
              :=
              fun x => show | a * x | = | x | by rw [ map_mul , abs_coe_circle , one_mul ]
            }
        map_one' := LinearIsometryEquiv.ext <| one_smul _
        map_mul' _ _ := LinearIsometryEquiv.ext <| mul_smul _ _
#align rotation rotation

@[simp]
theorem rotation_apply (a : circle) (z : ℂ) : rotation a z = a * z :=
  rfl
#align rotation_apply rotation_apply

@[simp]
theorem rotation_symm (a : circle) : (rotation a).symm = rotation a⁻¹ :=
  LinearIsometryEquiv.ext fun x => rfl
#align rotation_symm rotation_symm

@[simp]
theorem rotation_trans (a b : circle) : (rotation a).trans (rotation b) = rotation (b * a) :=
  by
  ext1
  simp
#align rotation_trans rotation_trans

theorem rotation_ne_conj_lie (a : circle) : rotation a ≠ conj_lie :=
  by
  intro h
  have h1 : rotation a 1 = conj 1 := LinearIsometryEquiv.congr_fun h 1
  have hI : rotation a I = conj I := LinearIsometryEquiv.congr_fun h I
  rw [rotation_apply, RingHom.map_one, mul_one] at h1
  rw [rotation_apply, conj_I, ← neg_one_mul, mul_left_inj' I_ne_zero, h1, eq_neg_self_iff] at hI
  exact one_ne_zero hI
#align rotation_ne_conj_lie rotation_ne_conj_lie

/-- Takes an element of `ℂ ≃ₗᵢ[ℝ] ℂ` and checks if it is a rotation, returns an element of the
unit circle. -/
@[simps]
def rotationOf (e : ℂ ≃ₗᵢ[ℝ] ℂ) : circle :=
  ⟨e 1 / Complex.abs (e 1), by simp⟩
#align rotation_of rotationOf

@[simp]
theorem rotation_of_rotation (a : circle) : rotationOf (rotation a) = a :=
  Subtype.ext <| by simp
#align rotation_of_rotation rotation_of_rotation

theorem rotation_injective : Function.Injective rotation :=
  Function.LeftInverse.injective rotation_of_rotation
#align rotation_injective rotation_injective

theorem LinearIsometry.re_apply_eq_re_of_add_conj_eq (f : ℂ →ₗᵢ[ℝ] ℂ)
    (h₃ : ∀ z, z + conj z = f z + conj (f z)) (z : ℂ) : (f z).re = z.re := by
  simpa [ext_iff, add_re, add_im, conj_re, conj_im, ← two_mul,
    show (2 : ℝ) ≠ 0 by simp [two_ne_zero]] using (h₃ z).symm
#align linear_isometry.re_apply_eq_re_of_add_conj_eq LinearIsometry.re_apply_eq_re_of_add_conj_eq

theorem LinearIsometry.im_apply_eq_im_or_neg_of_re_apply_eq_re {f : ℂ →ₗᵢ[ℝ] ℂ}
    (h₂ : ∀ z, (f z).re = z.re) (z : ℂ) : (f z).im = z.im ∨ (f z).im = -z.im :=
  by
  have h₁ := f.norm_map z
  simp only [Complex.abs_def, norm_eq_abs] at h₁
  rwa [Real.sqrt_inj (norm_sq_nonneg _) (norm_sq_nonneg _), norm_sq_apply (f z), norm_sq_apply z,
    h₂, add_left_cancel_iff, mul_self_eq_mul_self_iff] at h₁
#align
  linear_isometry.im_apply_eq_im_or_neg_of_re_apply_eq_re LinearIsometry.im_apply_eq_im_or_neg_of_re_apply_eq_re

theorem LinearIsometry.im_apply_eq_im {f : ℂ →ₗᵢ[ℝ] ℂ} (h : f 1 = 1) (z : ℂ) :
    z + conj z = f z + conj (f z) :=
  by
  have : ‖f z - 1‖ = ‖z - 1‖ := by rw [← f.norm_map (z - 1), f.map_sub, h]
  apply_fun fun x => x ^ 2  at this
  simp only [norm_eq_abs, ← norm_sq_eq_abs] at this
  rw [← of_real_inj, ← mul_conj, ← mul_conj] at this
  rw [RingHom.map_sub, RingHom.map_sub] at this
  simp only [sub_mul, mul_sub, one_mul, mul_one] at this
  rw [mul_conj, norm_sq_eq_abs, ← norm_eq_abs, LinearIsometry.norm_map] at this
  rw [mul_conj, norm_sq_eq_abs, ← norm_eq_abs] at this
  simp only [sub_sub, sub_right_inj, mul_one, of_real_pow, RingHom.map_one, norm_eq_abs] at this
  simp only [add_sub, sub_left_inj] at this
  rw [add_comm, ← this, add_comm]
#align linear_isometry.im_apply_eq_im LinearIsometry.im_apply_eq_im

theorem LinearIsometry.re_apply_eq_re {f : ℂ →ₗᵢ[ℝ] ℂ} (h : f 1 = 1) (z : ℂ) : (f z).re = z.re :=
  by
  apply LinearIsometry.re_apply_eq_re_of_add_conj_eq
  intro z
  apply LinearIsometry.im_apply_eq_im h
#align linear_isometry.re_apply_eq_re LinearIsometry.re_apply_eq_re

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `linear_isometry_complex_aux [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`f]
         [":"
          (Analysis.NormedSpace.LinearIsometry.«term_≃ₗᵢ[_]_»
           (Data.Complex.Basic.termℂ "ℂ")
           " ≃ₗᵢ["
           (Data.Real.Basic.termℝ "ℝ")
           "] "
           (Data.Complex.Basic.termℂ "ℂ"))]
         "}")
        (Term.explicitBinder
         "("
         [`h]
         [":" («term_=_» (Term.app `f [(num "1")]) "=" (num "1"))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_∨_»
         («term_=_»
          `f
          "="
          (Term.app
           `LinearIsometryEquiv.refl
           [(Data.Real.Basic.termℝ "ℝ") (Data.Complex.Basic.termℂ "ℂ")]))
         "∨"
         («term_=_» `f "=" `conj_lie))))
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
              [`h0 []]
              [(Term.typeSpec
                ":"
                («term_∨_»
                 («term_=_» (Term.app `f [`I]) "=" `I)
                 "∨"
                 («term_=_» (Term.app `f [`I]) "=" («term-_» "-" `I))))]
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
                     [(Term.typeSpec
                       ":"
                       («term_=_»
                        (Analysis.Complex.Isometry.complex.abs "|" (Term.app `f [`I]) "|")
                        "="
                        (num "1")))]
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
                           ["using" (Term.app `f.norm_map [`Complex.i])]))]))))))
                  []
                  (Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [] `ext_iff)
                     ","
                     (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `and_or_left)
                     ","
                     (Tactic.simpLemma [] [] `neg_re)
                     ","
                     (Tactic.simpLemma [] [] `I_re)
                     ","
                     (Tactic.simpLemma [] [] `neg_im)
                     ","
                     (Tactic.simpLemma [] [] `neg_zero)]
                    "]"]
                   [])
                  []
                  (Tactic.constructor "constructor")
                  []
                  (tactic__
                   (cdotTk (patternIgnore (token.«· » "·")))
                   [(Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `I_re)]
                      "]")
                     [])
                    []
                    (Tactic.exact
                     "exact"
                     (Term.app
                      (Term.explicit "@" `LinearIsometry.re_apply_eq_re)
                      [`f.to_linear_isometry `h `I]))])
                  []
                  (tactic__
                   (cdotTk (patternIgnore (token.«· » "·")))
                   [(Tactic.apply
                     "apply"
                     (Term.app
                      (Term.explicit "@" `LinearIsometry.im_apply_eq_im_or_neg_of_re_apply_eq_re)
                      [`f.to_linear_isometry]))
                    []
                    (Tactic.intro "intro" [`z])
                    []
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule
                        []
                        (Term.app
                         (Term.explicit "@" `LinearIsometry.re_apply_eq_re)
                         [`f.to_linear_isometry `h]))]
                      "]")
                     [])])]))))))
           []
           (Tactic.«tactic_<;>_»
            (Tactic.refine'
             "refine'"
             (Term.app
              `h0.imp
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`h']
                 [(Term.typeSpec ":" («term_=_» (Term.app `f [`I]) "=" `I))]
                 "=>"
                 (Term.hole "_")))
               (Term.fun
                "fun"
                (Term.basicFun
                 [`h']
                 [(Term.typeSpec ":" («term_=_» (Term.app `f [`I]) "=" («term-_» "-" `I)))]
                 "=>"
                 (Term.hole "_")))]))
            "<;>"
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.apply "apply" `LinearIsometryEquiv.to_linear_equiv_injective)
              []
              (Tactic.apply "apply" `complex.basis_one_I.ext')
              []
              (Tactic.intro "intro" [`i])
              []
              (Tactic.«tactic_<;>_»
               (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
               "<;>"
               (Tactic.simp
                "simp"
                []
                []
                []
                ["[" [(Tactic.simpLemma [] [] `h) "," (Tactic.simpLemma [] [] `h')] "]"]
                []))]))])))
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
             [`h0 []]
             [(Term.typeSpec
               ":"
               («term_∨_»
                («term_=_» (Term.app `f [`I]) "=" `I)
                "∨"
                («term_=_» (Term.app `f [`I]) "=" («term-_» "-" `I))))]
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
                    [(Term.typeSpec
                      ":"
                      («term_=_»
                       (Analysis.Complex.Isometry.complex.abs "|" (Term.app `f [`I]) "|")
                       "="
                       (num "1")))]
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
                          ["using" (Term.app `f.norm_map [`Complex.i])]))]))))))
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `ext_iff)
                    ","
                    (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `and_or_left)
                    ","
                    (Tactic.simpLemma [] [] `neg_re)
                    ","
                    (Tactic.simpLemma [] [] `I_re)
                    ","
                    (Tactic.simpLemma [] [] `neg_im)
                    ","
                    (Tactic.simpLemma [] [] `neg_zero)]
                   "]"]
                  [])
                 []
                 (Tactic.constructor "constructor")
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `I_re)]
                     "]")
                    [])
                   []
                   (Tactic.exact
                    "exact"
                    (Term.app
                     (Term.explicit "@" `LinearIsometry.re_apply_eq_re)
                     [`f.to_linear_isometry `h `I]))])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.apply
                    "apply"
                    (Term.app
                     (Term.explicit "@" `LinearIsometry.im_apply_eq_im_or_neg_of_re_apply_eq_re)
                     [`f.to_linear_isometry]))
                   []
                   (Tactic.intro "intro" [`z])
                   []
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule
                       []
                       (Term.app
                        (Term.explicit "@" `LinearIsometry.re_apply_eq_re)
                        [`f.to_linear_isometry `h]))]
                     "]")
                    [])])]))))))
          []
          (Tactic.«tactic_<;>_»
           (Tactic.refine'
            "refine'"
            (Term.app
             `h0.imp
             [(Term.fun
               "fun"
               (Term.basicFun
                [`h']
                [(Term.typeSpec ":" («term_=_» (Term.app `f [`I]) "=" `I))]
                "=>"
                (Term.hole "_")))
              (Term.fun
               "fun"
               (Term.basicFun
                [`h']
                [(Term.typeSpec ":" («term_=_» (Term.app `f [`I]) "=" («term-_» "-" `I)))]
                "=>"
                (Term.hole "_")))]))
           "<;>"
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.apply "apply" `LinearIsometryEquiv.to_linear_equiv_injective)
             []
             (Tactic.apply "apply" `complex.basis_one_I.ext')
             []
             (Tactic.intro "intro" [`i])
             []
             (Tactic.«tactic_<;>_»
              (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
              "<;>"
              (Tactic.simp
               "simp"
               []
               []
               []
               ["[" [(Tactic.simpLemma [] [] `h) "," (Tactic.simpLemma [] [] `h')] "]"]
               []))]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.refine'
        "refine'"
        (Term.app
         `h0.imp
         [(Term.fun
           "fun"
           (Term.basicFun
            [`h']
            [(Term.typeSpec ":" («term_=_» (Term.app `f [`I]) "=" `I))]
            "=>"
            (Term.hole "_")))
          (Term.fun
           "fun"
           (Term.basicFun
            [`h']
            [(Term.typeSpec ":" («term_=_» (Term.app `f [`I]) "=" («term-_» "-" `I)))]
            "=>"
            (Term.hole "_")))]))
       "<;>"
       (tactic__
        (cdotTk (patternIgnore (token.«· » "·")))
        [(Tactic.apply "apply" `LinearIsometryEquiv.to_linear_equiv_injective)
         []
         (Tactic.apply "apply" `complex.basis_one_I.ext')
         []
         (Tactic.intro "intro" [`i])
         []
         (Tactic.«tactic_<;>_»
          (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
          "<;>"
          (Tactic.simp
           "simp"
           []
           []
           []
           ["[" [(Tactic.simpLemma [] [] `h) "," (Tactic.simpLemma [] [] `h')] "]"]
           []))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.apply "apply" `LinearIsometryEquiv.to_linear_equiv_injective)
        []
        (Tactic.apply "apply" `complex.basis_one_I.ext')
        []
        (Tactic.intro "intro" [`i])
        []
        (Tactic.«tactic_<;>_»
         (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
         "<;>"
         (Tactic.simp
          "simp"
          []
          []
          []
          ["[" [(Tactic.simpLemma [] [] `h) "," (Tactic.simpLemma [] [] `h')] "]"]
          []))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
       "<;>"
       (Tactic.simp
        "simp"
        []
        []
        []
        ["[" [(Tactic.simpLemma [] [] `h) "," (Tactic.simpLemma [] [] `h')] "]"]
        []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["[" [(Tactic.simpLemma [] [] `h) "," (Tactic.simpLemma [] [] `h')] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
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
      (Tactic.intro "intro" [`i])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `complex.basis_one_I.ext')
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `complex.basis_one_I.ext'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `LinearIsometryEquiv.to_linear_equiv_injective)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearIsometryEquiv.to_linear_equiv_injective
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.refine'
       "refine'"
       (Term.app
        `h0.imp
        [(Term.fun
          "fun"
          (Term.basicFun
           [`h']
           [(Term.typeSpec ":" («term_=_» (Term.app `f [`I]) "=" `I))]
           "=>"
           (Term.hole "_")))
         (Term.fun
          "fun"
          (Term.basicFun
           [`h']
           [(Term.typeSpec ":" («term_=_» (Term.app `f [`I]) "=" («term-_» "-" `I)))]
           "=>"
           (Term.hole "_")))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `h0.imp
       [(Term.fun
         "fun"
         (Term.basicFun
          [`h']
          [(Term.typeSpec ":" («term_=_» (Term.app `f [`I]) "=" `I))]
          "=>"
          (Term.hole "_")))
        (Term.fun
         "fun"
         (Term.basicFun
          [`h']
          [(Term.typeSpec ":" («term_=_» (Term.app `f [`I]) "=" («term-_» "-" `I)))]
          "=>"
          (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`h']
        [(Term.typeSpec ":" («term_=_» (Term.app `f [`I]) "=" («term-_» "-" `I)))]
        "=>"
        (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.app `f [`I]) "=" («term-_» "-" `I))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" `I)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `I
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `f [`I])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `I
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `h'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`h']
        [(Term.typeSpec ":" («term_=_» (Term.app `f [`I]) "=" `I))]
        "=>"
        (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.app `f [`I]) "=" `I)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `I
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `f [`I])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `I
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `h'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`h']
       [(Term.typeSpec ":" («term_=_» (Term.app `f [`I]) "=" `I))]
       "=>"
       (Term.hole "_")))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h0.imp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`h0 []]
         [(Term.typeSpec
           ":"
           («term_∨_»
            («term_=_» (Term.app `f [`I]) "=" `I)
            "∨"
            («term_=_» (Term.app `f [`I]) "=" («term-_» "-" `I))))]
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
                [(Term.typeSpec
                  ":"
                  («term_=_»
                   (Analysis.Complex.Isometry.complex.abs "|" (Term.app `f [`I]) "|")
                   "="
                   (num "1")))]
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
                      ["using" (Term.app `f.norm_map [`Complex.i])]))]))))))
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `ext_iff)
                ","
                (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `and_or_left)
                ","
                (Tactic.simpLemma [] [] `neg_re)
                ","
                (Tactic.simpLemma [] [] `I_re)
                ","
                (Tactic.simpLemma [] [] `neg_im)
                ","
                (Tactic.simpLemma [] [] `neg_zero)]
               "]"]
              [])
             []
             (Tactic.constructor "constructor")
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `I_re)]
                 "]")
                [])
               []
               (Tactic.exact
                "exact"
                (Term.app
                 (Term.explicit "@" `LinearIsometry.re_apply_eq_re)
                 [`f.to_linear_isometry `h `I]))])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.apply
                "apply"
                (Term.app
                 (Term.explicit "@" `LinearIsometry.im_apply_eq_im_or_neg_of_re_apply_eq_re)
                 [`f.to_linear_isometry]))
               []
               (Tactic.intro "intro" [`z])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule
                   []
                   (Term.app
                    (Term.explicit "@" `LinearIsometry.re_apply_eq_re)
                    [`f.to_linear_isometry `h]))]
                 "]")
                [])])]))))))
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
             [(Term.typeSpec
               ":"
               («term_=_»
                (Analysis.Complex.Isometry.complex.abs "|" (Term.app `f [`I]) "|")
                "="
                (num "1")))]
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
                   ["using" (Term.app `f.norm_map [`Complex.i])]))]))))))
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `ext_iff)
             ","
             (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `and_or_left)
             ","
             (Tactic.simpLemma [] [] `neg_re)
             ","
             (Tactic.simpLemma [] [] `I_re)
             ","
             (Tactic.simpLemma [] [] `neg_im)
             ","
             (Tactic.simpLemma [] [] `neg_zero)]
            "]"]
           [])
          []
          (Tactic.constructor "constructor")
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `I_re)] "]")
             [])
            []
            (Tactic.exact
             "exact"
             (Term.app
              (Term.explicit "@" `LinearIsometry.re_apply_eq_re)
              [`f.to_linear_isometry `h `I]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.apply
             "apply"
             (Term.app
              (Term.explicit "@" `LinearIsometry.im_apply_eq_im_or_neg_of_re_apply_eq_re)
              [`f.to_linear_isometry]))
            []
            (Tactic.intro "intro" [`z])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                []
                (Term.app
                 (Term.explicit "@" `LinearIsometry.re_apply_eq_re)
                 [`f.to_linear_isometry `h]))]
              "]")
             [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.apply
         "apply"
         (Term.app
          (Term.explicit "@" `LinearIsometry.im_apply_eq_im_or_neg_of_re_apply_eq_re)
          [`f.to_linear_isometry]))
        []
        (Tactic.intro "intro" [`z])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            []
            (Term.app
             (Term.explicit "@" `LinearIsometry.re_apply_eq_re)
             [`f.to_linear_isometry `h]))]
          "]")
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          []
          (Term.app (Term.explicit "@" `LinearIsometry.re_apply_eq_re) [`f.to_linear_isometry `h]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.explicit "@" `LinearIsometry.re_apply_eq_re) [`f.to_linear_isometry `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f.to_linear_isometry
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `LinearIsometry.re_apply_eq_re)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearIsometry.re_apply_eq_re
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`z])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply
       "apply"
       (Term.app
        (Term.explicit "@" `LinearIsometry.im_apply_eq_im_or_neg_of_re_apply_eq_re)
        [`f.to_linear_isometry]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicit "@" `LinearIsometry.im_apply_eq_im_or_neg_of_re_apply_eq_re)
       [`f.to_linear_isometry])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f.to_linear_isometry
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `LinearIsometry.im_apply_eq_im_or_neg_of_re_apply_eq_re)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearIsometry.im_apply_eq_im_or_neg_of_re_apply_eq_re
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `I_re)] "]")
         [])
        []
        (Tactic.exact
         "exact"
         (Term.app
          (Term.explicit "@" `LinearIsometry.re_apply_eq_re)
          [`f.to_linear_isometry `h `I]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app (Term.explicit "@" `LinearIsometry.re_apply_eq_re) [`f.to_linear_isometry `h `I]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.explicit "@" `LinearIsometry.re_apply_eq_re) [`f.to_linear_isometry `h `I])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `I
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f.to_linear_isometry
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `LinearIsometry.re_apply_eq_re)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearIsometry.re_apply_eq_re
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `I_re)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `I_re
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.constructor "constructor")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `ext_iff)
         ","
         (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `and_or_left)
         ","
         (Tactic.simpLemma [] [] `neg_re)
         ","
         (Tactic.simpLemma [] [] `I_re)
         ","
         (Tactic.simpLemma [] [] `neg_im)
         ","
         (Tactic.simpLemma [] [] `neg_zero)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `neg_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `neg_im
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `I_re
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `neg_re
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `and_or_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ext_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
            (Analysis.Complex.Isometry.complex.abs "|" (Term.app `f [`I]) "|")
            "="
            (num "1")))]
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
               ["using" (Term.app `f.norm_map [`Complex.i])]))]))))))
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
            ["using" (Term.app `f.norm_map [`Complex.i])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" (Term.app `f.norm_map [`Complex.i])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f.norm_map [`Complex.i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Complex.i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f.norm_map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Analysis.Complex.Isometry.complex.abs "|" (Term.app `f [`I]) "|") "=" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.Complex.Isometry.complex.abs "|" (Term.app `f [`I]) "|")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Complex.Isometry.complex.abs', expected 'Analysis.Complex.Isometry.complex.abs._@.Analysis.Complex.Isometry._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
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
  linear_isometry_complex_aux
  { f : ℂ ≃ₗᵢ[ ℝ ] ℂ } ( h : f 1 = 1 ) : f = LinearIsometryEquiv.refl ℝ ℂ ∨ f = conj_lie
  :=
    by
      have
          h0
            : f I = I ∨ f I = - I
            :=
            by
              have : | f I | = 1 := by simpa using f.norm_map Complex.i
                simp only [ ext_iff , ← and_or_left , neg_re , I_re , neg_im , neg_zero ]
                constructor
                · rw [ ← I_re ] exact @ LinearIsometry.re_apply_eq_re f.to_linear_isometry h I
                ·
                  apply
                      @ LinearIsometry.im_apply_eq_im_or_neg_of_re_apply_eq_re f.to_linear_isometry
                    intro z
                    rw [ @ LinearIsometry.re_apply_eq_re f.to_linear_isometry h ]
        refine' h0.imp fun h' : f I = I => _ fun h' : f I = - I => _
          <;>
          ·
            apply LinearIsometryEquiv.to_linear_equiv_injective
              apply complex.basis_one_I.ext'
              intro i
              fin_cases i <;> simp [ h , h' ]
#align linear_isometry_complex_aux linear_isometry_complex_aux

theorem linear_isometry_complex (f : ℂ ≃ₗᵢ[ℝ] ℂ) :
    ∃ a : circle, f = rotation a ∨ f = conjLie.trans (rotation a) :=
  by
  let a : circle := ⟨f 1, by simpa using f.norm_map 1⟩
  use a
  have : (f.trans (rotation a).symm) 1 = 1 := by simpa using rotation_apply a⁻¹ (f 1)
  refine' (linear_isometry_complex_aux this).imp (fun h₁ => _) fun h₂ => _
  · simpa using eq_mul_of_inv_mul_eq h₁
  · exact eq_mul_of_inv_mul_eq h₂
#align linear_isometry_complex linear_isometry_complex

/-- The matrix representation of `rotation a` is equal to the conformal matrix
`!![re a, -im a; im a, re a]`. -/
theorem to_matrix_rotation (a : circle) :
    LinearMap.toMatrix basisOneI basisOneI (rotation a).toLinearEquiv =
      Matrix.planeConformalMatrix (re a) (im a) (by simp [pow_two, ← norm_sq_apply]) :=
  by
  ext (i j)
  simp [LinearMap.to_matrix_apply]
  fin_cases i <;> fin_cases j <;> simp
#align to_matrix_rotation to_matrix_rotation

/-- The determinant of `rotation` (as a linear map) is equal to `1`. -/
@[simp]
theorem det_rotation (a : circle) : ((rotation a).toLinearEquiv : ℂ →ₗ[ℝ] ℂ).det = 1 :=
  by
  rw [← LinearMap.det_to_matrix basis_one_I, to_matrix_rotation, Matrix.det_fin_two]
  simp [← norm_sq_apply]
#align det_rotation det_rotation

/-- The determinant of `rotation` (as a linear equiv) is equal to `1`. -/
@[simp]
theorem linear_equiv_det_rotation (a : circle) : (rotation a).toLinearEquiv.det = 1 := by
  rw [← Units.eq_iff, LinearEquiv.coe_det, det_rotation, Units.val_one]
#align linear_equiv_det_rotation linear_equiv_det_rotation

