/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck

! This file was ported from Lean 3 source module number_theory.modular_forms.slash_actions
! leanprover-community/mathlib commit 6d0adfa76594f304b4650d098273d4366edeb61b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Complex.UpperHalfPlane.Basic
import Mathbin.LinearAlgebra.GeneralLinearGroup
import Mathbin.LinearAlgebra.SpecialLinearGroup

/-!
# Slash actions

This file defines a class of slash actions, which are families of right actions of a given group
parametrized by some Type. This is modeled on the slash action of `GL_pos (fin 2) ℝ` on the space
of modular forms.
-/


open Complex UpperHalfPlane

open UpperHalfPlane

-- mathport name: «expr↑ₘ »
local prefix:1024 "↑ₘ" => @coe _ (Matrix (Fin 2) (Fin 2) _) _

-- mathport name: «exprGL( , )⁺»
local notation "GL(" n ", " R ")" "⁺" => Matrix.gLPos (Fin n) R

-- mathport name: «exprSL( , )»
local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

/-- A general version of the slash action of the space of modular forms.-/
class SlashAction (β G α γ : Type _) [Group G] [Zero α] [HasSmul γ α] [Add α] where
  map : β → G → α → α
  zero_slash : ∀ (k : β) (g : G), map k g 0 = 0
  slash_one : ∀ (k : β) (a : α), map k 1 a = a
  right_action : ∀ (k : β) (g h : G) (a : α), map k h (map k g a) = map k (g * h) a
  smul_action : ∀ (k : β) (g : G) (a : α) (z : γ), map k g (z • a) = z • map k g a
  AddAction : ∀ (k : β) (g : G) (a b : α), map k g (a + b) = map k g a + map k g b
#align slash_action SlashAction

/-- Slash_action induced by a monoid homomorphism.-/
def monoidHomSlashAction {β G H α γ : Type _} [Group G] [Zero α] [HasSmul γ α] [Add α] [Group H]
    [SlashAction β G α γ] (h : H →* G) : SlashAction β H α γ
    where
  map k g := SlashAction.map γ k (h g)
  zero_slash k g := SlashAction.zero_slash k (h g)
  slash_one k a := by simp only [map_one, SlashAction.slash_one]
  right_action k g gg a := by simp only [map_mul, SlashAction.right_action]
  smul_action _ _ := SlashAction.smul_action _ _
  AddAction _ g _ _ := SlashAction.add_action _ (h g) _ _
#align monoid_hom_slash_action monoidHomSlashAction

namespace ModularForm

noncomputable section

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The weight `k` action of `GL(2, ℝ)⁺` on functions `f : ℍ → ℂ`. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `slash [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`k] [":" (termℤ "ℤ")] [] ")")
        (Term.explicitBinder
         "("
         [`γ]
         [":"
          (NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»
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
         [`f]
         [":"
          (Term.arrow
           (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
           "→"
           (Data.Complex.Basic.termℂ "ℂ"))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`x]
         [":" (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")]
         []
         ")")]
       [(Term.typeSpec ":" (Data.Complex.Basic.termℂ "ℂ"))])
      (Command.declValSimple
       ":="
       («term_*_»
        («term_*_»
         (Term.app `f [(Algebra.Group.Defs.«term_•_» `γ " • " `x)])
         "*"
         («term_^_»
          (Term.typeAscription
           "("
           (Term.proj (NumberTheory.ModularForms.SlashActions.«term↑ₘ_» "↑ₘ" `γ) "." `det)
           ":"
           [(Data.Real.Basic.termℝ "ℝ")]
           ")")
          "^"
          («term_-_» `k "-" (num "1"))))
        "*"
        («term_^_» (Term.app `UpperHalfPlane.denom [`γ `x]) "^" («term-_» "-" `k)))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_*_»
        (Term.app `f [(Algebra.Group.Defs.«term_•_» `γ " • " `x)])
        "*"
        («term_^_»
         (Term.typeAscription
          "("
          (Term.proj (NumberTheory.ModularForms.SlashActions.«term↑ₘ_» "↑ₘ" `γ) "." `det)
          ":"
          [(Data.Real.Basic.termℝ "ℝ")]
          ")")
         "^"
         («term_-_» `k "-" (num "1"))))
       "*"
       («term_^_» (Term.app `UpperHalfPlane.denom [`γ `x]) "^" («term-_» "-" `k)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (Term.app `UpperHalfPlane.denom [`γ `x]) "^" («term-_» "-" `k))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" `k)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 80 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term-_» "-" `k) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `UpperHalfPlane.denom [`γ `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `γ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `UpperHalfPlane.denom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_*_»
       (Term.app `f [(Algebra.Group.Defs.«term_•_» `γ " • " `x)])
       "*"
       («term_^_»
        (Term.typeAscription
         "("
         (Term.proj (NumberTheory.ModularForms.SlashActions.«term↑ₘ_» "↑ₘ" `γ) "." `det)
         ":"
         [(Data.Real.Basic.termℝ "ℝ")]
         ")")
        "^"
        («term_-_» `k "-" (num "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       (Term.typeAscription
        "("
        (Term.proj (NumberTheory.ModularForms.SlashActions.«term↑ₘ_» "↑ₘ" `γ) "." `det)
        ":"
        [(Data.Real.Basic.termℝ "ℝ")]
        ")")
       "^"
       («term_-_» `k "-" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» `k "-" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_-_» `k "-" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.typeAscription
       "("
       (Term.proj (NumberTheory.ModularForms.SlashActions.«term↑ₘ_» "↑ₘ" `γ) "." `det)
       ":"
       [(Data.Real.Basic.termℝ "ℝ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (NumberTheory.ModularForms.SlashActions.«term↑ₘ_» "↑ₘ" `γ) "." `det)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (NumberTheory.ModularForms.SlashActions.«term↑ₘ_» "↑ₘ" `γ)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.SlashActions.«term↑ₘ_»', expected 'NumberTheory.ModularForms.SlashActions.term↑ₘ_._@.NumberTheory.ModularForms.SlashActions._hyg.8'
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
/-- The weight `k` action of `GL(2, ℝ)⁺` on functions `f : ℍ → ℂ`. -/
  def
    slash
    ( k : ℤ ) ( γ : GL( 2 , ℝ ) ⁺ ) ( f : ℍ → ℂ ) ( x : ℍ ) : ℂ
    := f γ • x * ( ↑ₘ γ . det : ℝ ) ^ k - 1 * UpperHalfPlane.denom γ x ^ - k
#align modular_form.slash ModularForm.slash

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.variable
     "variable"
     [(Term.implicitBinder
       "{"
       [`Γ]
       [":"
        (Term.app
         `Subgroup
         [(NumberTheory.ModularForms.SlashActions.«termSL(_,_)»
           "SL("
           (num "2")
           ", "
           (termℤ "ℤ")
           ")")])]
       "}")
      (Term.implicitBinder "{" [`k] [":" (termℤ "ℤ")] "}")
      (Term.explicitBinder
       "("
       [`f]
       [":"
        (Term.arrow
         (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
         "→"
         (Data.Complex.Basic.termℂ "ℂ"))]
       []
       ")")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
       "→"
       (Data.Complex.Basic.termℂ "ℂ"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℤ "ℤ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Subgroup
       [(NumberTheory.ModularForms.SlashActions.«termSL(_,_)»
         "SL("
         (num "2")
         ", "
         (termℤ "ℤ")
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.SlashActions.«termSL(_,_)»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.SlashActions.«termSL(_,_)»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.ModularForms.SlashActions.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.SlashActions.«termSL(_,_)»', expected 'NumberTheory.ModularForms.SlashActions.termSL(_,_)._@.NumberTheory.ModularForms.SlashActions._hyg.889'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.instBinder'-/-- failed to format: format: uncaught backtrack exception
variable { Γ : Subgroup SL( 2 , ℤ ) } { k : ℤ } ( f : ℍ → ℂ )

-- mathport name: modular_form.slash
scoped notation:100 f " ∣[" k "]" γ:100 => ModularForm.slash k γ f

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `slash_right_action [])
      (Command.declSig
       [(Term.explicitBinder "(" [`k] [":" (termℤ "ℤ")] [] ")")
        (Term.explicitBinder
         "("
         [`A `B]
         [":"
          (NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»
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
         [`f]
         [":"
          (Term.arrow
           (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
           "→"
           (Data.Complex.Basic.termℂ "ℂ"))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash
          (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash `f " ∣[" `k "]" `A)
          " ∣["
          `k
          "]"
          `B)
         "="
         (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash
          `f
          " ∣["
          `k
          "]"
          («term_*_» `A "*" `B)))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.Ext.tacticExt1___ "ext1" [])
           []
           (Mathlib.Tactic.tacticSimp_rw__
            "simp_rw"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `slash)
              ","
              (Tactic.rwRule [] (Term.app `UpperHalfPlane.denom_cocycle [`A `B `x]))]
             "]")
            [])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`e3 []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Algebra.Group.Defs.«term_•_» («term_*_» `A "*" `B) " • " `x)
                 "="
                 (Algebra.Group.Defs.«term_•_»
                  `A
                  " • "
                  (Algebra.Group.Defs.«term_•_» `B " • " `x))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(convert "convert" [] (Term.app `UpperHalfPlane.mul_smul' [`A `B `x]) [])]))))))
           []
           (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `e3)] "]") [])
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `UpperHalfPlane.num)
              ","
              (Tactic.simpLemma [] [] `UpperHalfPlane.denom)
              ","
              (Tactic.simpLemma [] [] `of_real_mul)
              ","
              (Tactic.simpLemma [] [] `Subgroup.coe_mul)
              ","
              (Tactic.simpLemma [] [] `coe_coe)
              ","
              (Tactic.simpLemma [] [] `UpperHalfPlane.coe_smul)
              ","
              (Tactic.simpLemma [] [] `Units.val_mul)
              ","
              (Tactic.simpLemma [] [] `Matrix.mul_eq_mul)
              ","
              (Tactic.simpLemma [] [] `Matrix.det_mul)
              ","
              (Tactic.simpLemma [] [] `UpperHalfPlane.smulAux)
              ","
              (Tactic.simpLemma [] [] `UpperHalfPlane.smulAux')
              ","
              (Tactic.simpLemma [] [] `Subtype.coe_mk)]
             "]"]
            [(Tactic.location "at" (Tactic.locationWildcard "*"))])
           []
           (Tactic.fieldSimp "field_simp" [] [] [] [] [])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                («term_=_»
                 («term_^_»
                  («term_*_»
                   (Term.typeAscription
                    "("
                    (Term.proj
                     (Term.typeAscription
                      "("
                      (coeNotation
                       "↑"
                       (Term.typeAscription
                        "("
                        (coeNotation "↑" `A)
                        ":"
                        [(Term.app
                          (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
                          [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
                        ")"))
                      ":"
                      [(Term.app
                        `Matrix
                        [(Term.app `Fin [(num "2")])
                         (Term.app `Fin [(num "2")])
                         (Data.Real.Basic.termℝ "ℝ")])]
                      ")")
                     "."
                     `det)
                    ":"
                    [(Data.Complex.Basic.termℂ "ℂ")]
                    ")")
                   "*"
                   (Term.typeAscription
                    "("
                    (Term.proj
                     (Term.typeAscription
                      "("
                      (coeNotation
                       "↑"
                       (Term.typeAscription
                        "("
                        (coeNotation "↑" `B)
                        ":"
                        [(Term.app
                          (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
                          [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
                        ")"))
                      ":"
                      [(Term.app
                        `Matrix
                        [(Term.app `Fin [(num "2")])
                         (Term.app `Fin [(num "2")])
                         (Data.Real.Basic.termℝ "ℝ")])]
                      ")")
                     "."
                     `det)
                    ":"
                    [(Data.Complex.Basic.termℂ "ℂ")]
                    ")"))
                  "^"
                  («term_-_» `k "-" (num "1")))
                 "="
                 («term_*_»
                  («term_^_»
                   (Term.typeAscription
                    "("
                    (Term.proj
                     (Term.typeAscription
                      "("
                      (coeNotation
                       "↑"
                       (Term.typeAscription
                        "("
                        (coeNotation "↑" `A)
                        ":"
                        [(Term.app
                          (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
                          [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
                        ")"))
                      ":"
                      [(Term.app
                        `Matrix
                        [(Term.app `Fin [(num "2")])
                         (Term.app `Fin [(num "2")])
                         (Data.Real.Basic.termℝ "ℝ")])]
                      ")")
                     "."
                     `det)
                    ":"
                    [(Data.Complex.Basic.termℂ "ℂ")]
                    ")")
                   "^"
                   («term_-_» `k "-" (num "1")))
                  "*"
                  («term_^_»
                   (Term.typeAscription
                    "("
                    (Term.proj
                     (Term.typeAscription
                      "("
                      (coeNotation
                       "↑"
                       (Term.typeAscription
                        "("
                        (coeNotation "↑" `B)
                        ":"
                        [(Term.app
                          (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
                          [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
                        ")"))
                      ":"
                      [(Term.app
                        `Matrix
                        [(Term.app `Fin [(num "2")])
                         (Term.app `Fin [(num "2")])
                         (Data.Real.Basic.termℝ "ℝ")])]
                      ")")
                     "."
                     `det)
                    ":"
                    [(Data.Complex.Basic.termℂ "ℂ")]
                    ")")
                   "^"
                   («term_-_» `k "-" (num "1"))))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Mathlib.Tactic.tacticSimp_rw__
                   "simp_rw"
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_zpow)]
                    "]")
                   [])]))))))
           []
           (Mathlib.Tactic.tacticSimp_rw__
            "simp_rw"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `this)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_zpow)]
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
         [(Std.Tactic.Ext.tacticExt1___ "ext1" [])
          []
          (Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `slash)
             ","
             (Tactic.rwRule [] (Term.app `UpperHalfPlane.denom_cocycle [`A `B `x]))]
            "]")
           [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`e3 []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Algebra.Group.Defs.«term_•_» («term_*_» `A "*" `B) " • " `x)
                "="
                (Algebra.Group.Defs.«term_•_»
                 `A
                 " • "
                 (Algebra.Group.Defs.«term_•_» `B " • " `x))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(convert "convert" [] (Term.app `UpperHalfPlane.mul_smul' [`A `B `x]) [])]))))))
          []
          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `e3)] "]") [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `UpperHalfPlane.num)
             ","
             (Tactic.simpLemma [] [] `UpperHalfPlane.denom)
             ","
             (Tactic.simpLemma [] [] `of_real_mul)
             ","
             (Tactic.simpLemma [] [] `Subgroup.coe_mul)
             ","
             (Tactic.simpLemma [] [] `coe_coe)
             ","
             (Tactic.simpLemma [] [] `UpperHalfPlane.coe_smul)
             ","
             (Tactic.simpLemma [] [] `Units.val_mul)
             ","
             (Tactic.simpLemma [] [] `Matrix.mul_eq_mul)
             ","
             (Tactic.simpLemma [] [] `Matrix.det_mul)
             ","
             (Tactic.simpLemma [] [] `UpperHalfPlane.smulAux)
             ","
             (Tactic.simpLemma [] [] `UpperHalfPlane.smulAux')
             ","
             (Tactic.simpLemma [] [] `Subtype.coe_mk)]
            "]"]
           [(Tactic.location "at" (Tactic.locationWildcard "*"))])
          []
          (Tactic.fieldSimp "field_simp" [] [] [] [] [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               («term_=_»
                («term_^_»
                 («term_*_»
                  (Term.typeAscription
                   "("
                   (Term.proj
                    (Term.typeAscription
                     "("
                     (coeNotation
                      "↑"
                      (Term.typeAscription
                       "("
                       (coeNotation "↑" `A)
                       ":"
                       [(Term.app
                         (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
                         [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
                       ")"))
                     ":"
                     [(Term.app
                       `Matrix
                       [(Term.app `Fin [(num "2")])
                        (Term.app `Fin [(num "2")])
                        (Data.Real.Basic.termℝ "ℝ")])]
                     ")")
                    "."
                    `det)
                   ":"
                   [(Data.Complex.Basic.termℂ "ℂ")]
                   ")")
                  "*"
                  (Term.typeAscription
                   "("
                   (Term.proj
                    (Term.typeAscription
                     "("
                     (coeNotation
                      "↑"
                      (Term.typeAscription
                       "("
                       (coeNotation "↑" `B)
                       ":"
                       [(Term.app
                         (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
                         [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
                       ")"))
                     ":"
                     [(Term.app
                       `Matrix
                       [(Term.app `Fin [(num "2")])
                        (Term.app `Fin [(num "2")])
                        (Data.Real.Basic.termℝ "ℝ")])]
                     ")")
                    "."
                    `det)
                   ":"
                   [(Data.Complex.Basic.termℂ "ℂ")]
                   ")"))
                 "^"
                 («term_-_» `k "-" (num "1")))
                "="
                («term_*_»
                 («term_^_»
                  (Term.typeAscription
                   "("
                   (Term.proj
                    (Term.typeAscription
                     "("
                     (coeNotation
                      "↑"
                      (Term.typeAscription
                       "("
                       (coeNotation "↑" `A)
                       ":"
                       [(Term.app
                         (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
                         [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
                       ")"))
                     ":"
                     [(Term.app
                       `Matrix
                       [(Term.app `Fin [(num "2")])
                        (Term.app `Fin [(num "2")])
                        (Data.Real.Basic.termℝ "ℝ")])]
                     ")")
                    "."
                    `det)
                   ":"
                   [(Data.Complex.Basic.termℂ "ℂ")]
                   ")")
                  "^"
                  («term_-_» `k "-" (num "1")))
                 "*"
                 («term_^_»
                  (Term.typeAscription
                   "("
                   (Term.proj
                    (Term.typeAscription
                     "("
                     (coeNotation
                      "↑"
                      (Term.typeAscription
                       "("
                       (coeNotation "↑" `B)
                       ":"
                       [(Term.app
                         (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
                         [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
                       ")"))
                     ":"
                     [(Term.app
                       `Matrix
                       [(Term.app `Fin [(num "2")])
                        (Term.app `Fin [(num "2")])
                        (Data.Real.Basic.termℝ "ℝ")])]
                     ")")
                    "."
                    `det)
                   ":"
                   [(Data.Complex.Basic.termℂ "ℂ")]
                   ")")
                  "^"
                  («term_-_» `k "-" (num "1"))))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Mathlib.Tactic.tacticSimp_rw__
                  "simp_rw"
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_zpow)]
                   "]")
                  [])]))))))
          []
          (Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `this)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_zpow)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `this)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_zpow)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_zpow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
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
            («term_^_»
             («term_*_»
              (Term.typeAscription
               "("
               (Term.proj
                (Term.typeAscription
                 "("
                 (coeNotation
                  "↑"
                  (Term.typeAscription
                   "("
                   (coeNotation "↑" `A)
                   ":"
                   [(Term.app
                     (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
                     [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
                   ")"))
                 ":"
                 [(Term.app
                   `Matrix
                   [(Term.app `Fin [(num "2")])
                    (Term.app `Fin [(num "2")])
                    (Data.Real.Basic.termℝ "ℝ")])]
                 ")")
                "."
                `det)
               ":"
               [(Data.Complex.Basic.termℂ "ℂ")]
               ")")
              "*"
              (Term.typeAscription
               "("
               (Term.proj
                (Term.typeAscription
                 "("
                 (coeNotation
                  "↑"
                  (Term.typeAscription
                   "("
                   (coeNotation "↑" `B)
                   ":"
                   [(Term.app
                     (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
                     [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
                   ")"))
                 ":"
                 [(Term.app
                   `Matrix
                   [(Term.app `Fin [(num "2")])
                    (Term.app `Fin [(num "2")])
                    (Data.Real.Basic.termℝ "ℝ")])]
                 ")")
                "."
                `det)
               ":"
               [(Data.Complex.Basic.termℂ "ℂ")]
               ")"))
             "^"
             («term_-_» `k "-" (num "1")))
            "="
            («term_*_»
             («term_^_»
              (Term.typeAscription
               "("
               (Term.proj
                (Term.typeAscription
                 "("
                 (coeNotation
                  "↑"
                  (Term.typeAscription
                   "("
                   (coeNotation "↑" `A)
                   ":"
                   [(Term.app
                     (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
                     [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
                   ")"))
                 ":"
                 [(Term.app
                   `Matrix
                   [(Term.app `Fin [(num "2")])
                    (Term.app `Fin [(num "2")])
                    (Data.Real.Basic.termℝ "ℝ")])]
                 ")")
                "."
                `det)
               ":"
               [(Data.Complex.Basic.termℂ "ℂ")]
               ")")
              "^"
              («term_-_» `k "-" (num "1")))
             "*"
             («term_^_»
              (Term.typeAscription
               "("
               (Term.proj
                (Term.typeAscription
                 "("
                 (coeNotation
                  "↑"
                  (Term.typeAscription
                   "("
                   (coeNotation "↑" `B)
                   ":"
                   [(Term.app
                     (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
                     [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
                   ")"))
                 ":"
                 [(Term.app
                   `Matrix
                   [(Term.app `Fin [(num "2")])
                    (Term.app `Fin [(num "2")])
                    (Data.Real.Basic.termℝ "ℝ")])]
                 ")")
                "."
                `det)
               ":"
               [(Data.Complex.Basic.termℂ "ℂ")]
               ")")
              "^"
              («term_-_» `k "-" (num "1"))))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Mathlib.Tactic.tacticSimp_rw__
              "simp_rw"
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_zpow)]
               "]")
              [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_zpow)] "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_zpow)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_zpow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       («term_^_»
        («term_*_»
         (Term.typeAscription
          "("
          (Term.proj
           (Term.typeAscription
            "("
            (coeNotation
             "↑"
             (Term.typeAscription
              "("
              (coeNotation "↑" `A)
              ":"
              [(Term.app
                (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
                [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
              ")"))
            ":"
            [(Term.app
              `Matrix
              [(Term.app `Fin [(num "2")])
               (Term.app `Fin [(num "2")])
               (Data.Real.Basic.termℝ "ℝ")])]
            ")")
           "."
           `det)
          ":"
          [(Data.Complex.Basic.termℂ "ℂ")]
          ")")
         "*"
         (Term.typeAscription
          "("
          (Term.proj
           (Term.typeAscription
            "("
            (coeNotation
             "↑"
             (Term.typeAscription
              "("
              (coeNotation "↑" `B)
              ":"
              [(Term.app
                (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
                [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
              ")"))
            ":"
            [(Term.app
              `Matrix
              [(Term.app `Fin [(num "2")])
               (Term.app `Fin [(num "2")])
               (Data.Real.Basic.termℝ "ℝ")])]
            ")")
           "."
           `det)
          ":"
          [(Data.Complex.Basic.termℂ "ℂ")]
          ")"))
        "^"
        («term_-_» `k "-" (num "1")))
       "="
       («term_*_»
        («term_^_»
         (Term.typeAscription
          "("
          (Term.proj
           (Term.typeAscription
            "("
            (coeNotation
             "↑"
             (Term.typeAscription
              "("
              (coeNotation "↑" `A)
              ":"
              [(Term.app
                (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
                [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
              ")"))
            ":"
            [(Term.app
              `Matrix
              [(Term.app `Fin [(num "2")])
               (Term.app `Fin [(num "2")])
               (Data.Real.Basic.termℝ "ℝ")])]
            ")")
           "."
           `det)
          ":"
          [(Data.Complex.Basic.termℂ "ℂ")]
          ")")
         "^"
         («term_-_» `k "-" (num "1")))
        "*"
        («term_^_»
         (Term.typeAscription
          "("
          (Term.proj
           (Term.typeAscription
            "("
            (coeNotation
             "↑"
             (Term.typeAscription
              "("
              (coeNotation "↑" `B)
              ":"
              [(Term.app
                (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
                [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
              ")"))
            ":"
            [(Term.app
              `Matrix
              [(Term.app `Fin [(num "2")])
               (Term.app `Fin [(num "2")])
               (Data.Real.Basic.termℝ "ℝ")])]
            ")")
           "."
           `det)
          ":"
          [(Data.Complex.Basic.termℂ "ℂ")]
          ")")
         "^"
         («term_-_» `k "-" (num "1")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_^_»
        (Term.typeAscription
         "("
         (Term.proj
          (Term.typeAscription
           "("
           (coeNotation
            "↑"
            (Term.typeAscription
             "("
             (coeNotation "↑" `A)
             ":"
             [(Term.app
               (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
               [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
             ")"))
           ":"
           [(Term.app
             `Matrix
             [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
           ")")
          "."
          `det)
         ":"
         [(Data.Complex.Basic.termℂ "ℂ")]
         ")")
        "^"
        («term_-_» `k "-" (num "1")))
       "*"
       («term_^_»
        (Term.typeAscription
         "("
         (Term.proj
          (Term.typeAscription
           "("
           (coeNotation
            "↑"
            (Term.typeAscription
             "("
             (coeNotation "↑" `B)
             ":"
             [(Term.app
               (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
               [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
             ")"))
           ":"
           [(Term.app
             `Matrix
             [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
           ")")
          "."
          `det)
         ":"
         [(Data.Complex.Basic.termℂ "ℂ")]
         ")")
        "^"
        («term_-_» `k "-" (num "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       (Term.typeAscription
        "("
        (Term.proj
         (Term.typeAscription
          "("
          (coeNotation
           "↑"
           (Term.typeAscription
            "("
            (coeNotation "↑" `B)
            ":"
            [(Term.app
              (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
              [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
            ")"))
          ":"
          [(Term.app
            `Matrix
            [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
          ")")
         "."
         `det)
        ":"
        [(Data.Complex.Basic.termℂ "ℂ")]
        ")")
       "^"
       («term_-_» `k "-" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» `k "-" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_-_» `k "-" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.typeAscription
       "("
       (Term.proj
        (Term.typeAscription
         "("
         (coeNotation
          "↑"
          (Term.typeAscription
           "("
           (coeNotation "↑" `B)
           ":"
           [(Term.app
             (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
             [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
           ")"))
         ":"
         [(Term.app
           `Matrix
           [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
         ")")
        "."
        `det)
       ":"
       [(Data.Complex.Basic.termℂ "ℂ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.typeAscription
        "("
        (coeNotation
         "↑"
         (Term.typeAscription
          "("
          (coeNotation "↑" `B)
          ":"
          [(Term.app
            (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
            [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
          ")"))
        ":"
        [(Term.app
          `Matrix
          [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
        ")")
       "."
       `det)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription
       "("
       (coeNotation
        "↑"
        (Term.typeAscription
         "("
         (coeNotation "↑" `B)
         ":"
         [(Term.app
           (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
           [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
         ")"))
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
      (coeNotation
       "↑"
       (Term.typeAscription
        "("
        (coeNotation "↑" `B)
        ":"
        [(Term.app
          (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
          [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (coeNotation "↑" `B)
       ":"
       [(Term.app
         (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
         [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
       [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (coeNotation "↑" `B)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `B
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_^_»
       (Term.typeAscription
        "("
        (Term.proj
         (Term.typeAscription
          "("
          (coeNotation
           "↑"
           (Term.typeAscription
            "("
            (coeNotation "↑" `A)
            ":"
            [(Term.app
              (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
              [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
            ")"))
          ":"
          [(Term.app
            `Matrix
            [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
          ")")
         "."
         `det)
        ":"
        [(Data.Complex.Basic.termℂ "ℂ")]
        ")")
       "^"
       («term_-_» `k "-" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» `k "-" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_-_» `k "-" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.typeAscription
       "("
       (Term.proj
        (Term.typeAscription
         "("
         (coeNotation
          "↑"
          (Term.typeAscription
           "("
           (coeNotation "↑" `A)
           ":"
           [(Term.app
             (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
             [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
           ")"))
         ":"
         [(Term.app
           `Matrix
           [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
         ")")
        "."
        `det)
       ":"
       [(Data.Complex.Basic.termℂ "ℂ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.typeAscription
        "("
        (coeNotation
         "↑"
         (Term.typeAscription
          "("
          (coeNotation "↑" `A)
          ":"
          [(Term.app
            (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
            [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
          ")"))
        ":"
        [(Term.app
          `Matrix
          [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
        ")")
       "."
       `det)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription
       "("
       (coeNotation
        "↑"
        (Term.typeAscription
         "("
         (coeNotation "↑" `A)
         ":"
         [(Term.app
           (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
           [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
         ")"))
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
      (coeNotation
       "↑"
       (Term.typeAscription
        "("
        (coeNotation "↑" `A)
        ":"
        [(Term.app
          (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
          [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (coeNotation "↑" `A)
       ":"
       [(Term.app
         (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
         [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
       [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (coeNotation "↑" `A)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 80, (some 80, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_^_»
       («term_*_»
        (Term.typeAscription
         "("
         (Term.proj
          (Term.typeAscription
           "("
           (coeNotation
            "↑"
            (Term.typeAscription
             "("
             (coeNotation "↑" `A)
             ":"
             [(Term.app
               (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
               [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
             ")"))
           ":"
           [(Term.app
             `Matrix
             [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
           ")")
          "."
          `det)
         ":"
         [(Data.Complex.Basic.termℂ "ℂ")]
         ")")
        "*"
        (Term.typeAscription
         "("
         (Term.proj
          (Term.typeAscription
           "("
           (coeNotation
            "↑"
            (Term.typeAscription
             "("
             (coeNotation "↑" `B)
             ":"
             [(Term.app
               (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
               [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
             ")"))
           ":"
           [(Term.app
             `Matrix
             [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
           ")")
          "."
          `det)
         ":"
         [(Data.Complex.Basic.termℂ "ℂ")]
         ")"))
       "^"
       («term_-_» `k "-" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» `k "-" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_-_» `k "-" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      («term_*_»
       (Term.typeAscription
        "("
        (Term.proj
         (Term.typeAscription
          "("
          (coeNotation
           "↑"
           (Term.typeAscription
            "("
            (coeNotation "↑" `A)
            ":"
            [(Term.app
              (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
              [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
            ")"))
          ":"
          [(Term.app
            `Matrix
            [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
          ")")
         "."
         `det)
        ":"
        [(Data.Complex.Basic.termℂ "ℂ")]
        ")")
       "*"
       (Term.typeAscription
        "("
        (Term.proj
         (Term.typeAscription
          "("
          (coeNotation
           "↑"
           (Term.typeAscription
            "("
            (coeNotation "↑" `B)
            ":"
            [(Term.app
              (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
              [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
            ")"))
          ":"
          [(Term.app
            `Matrix
            [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
          ")")
         "."
         `det)
        ":"
        [(Data.Complex.Basic.termℂ "ℂ")]
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.proj
        (Term.typeAscription
         "("
         (coeNotation
          "↑"
          (Term.typeAscription
           "("
           (coeNotation "↑" `B)
           ":"
           [(Term.app
             (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
             [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
           ")"))
         ":"
         [(Term.app
           `Matrix
           [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
         ")")
        "."
        `det)
       ":"
       [(Data.Complex.Basic.termℂ "ℂ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.typeAscription
        "("
        (coeNotation
         "↑"
         (Term.typeAscription
          "("
          (coeNotation "↑" `B)
          ":"
          [(Term.app
            (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
            [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
          ")"))
        ":"
        [(Term.app
          `Matrix
          [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
        ")")
       "."
       `det)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription
       "("
       (coeNotation
        "↑"
        (Term.typeAscription
         "("
         (coeNotation "↑" `B)
         ":"
         [(Term.app
           (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
           [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
         ")"))
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
      (coeNotation
       "↑"
       (Term.typeAscription
        "("
        (coeNotation "↑" `B)
        ":"
        [(Term.app
          (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
          [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (coeNotation "↑" `B)
       ":"
       [(Term.app
         (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
         [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
       [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (coeNotation "↑" `B)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `B
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.typeAscription
       "("
       (Term.proj
        (Term.typeAscription
         "("
         (coeNotation
          "↑"
          (Term.typeAscription
           "("
           (coeNotation "↑" `A)
           ":"
           [(Term.app
             (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
             [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
           ")"))
         ":"
         [(Term.app
           `Matrix
           [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
         ")")
        "."
        `det)
       ":"
       [(Data.Complex.Basic.termℂ "ℂ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.typeAscription
        "("
        (coeNotation
         "↑"
         (Term.typeAscription
          "("
          (coeNotation "↑" `A)
          ":"
          [(Term.app
            (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
            [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
          ")"))
        ":"
        [(Term.app
          `Matrix
          [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
        ")")
       "."
       `det)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription
       "("
       (coeNotation
        "↑"
        (Term.typeAscription
         "("
         (coeNotation "↑" `A)
         ":"
         [(Term.app
           (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
           [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
         ")"))
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
      (coeNotation
       "↑"
       (Term.typeAscription
        "("
        (coeNotation "↑" `A)
        ":"
        [(Term.app
          (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
          [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (coeNotation "↑" `A)
       ":"
       [(Term.app
         (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
         [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
       [(Term.app `Fin [(num "2")]) (Data.Real.Basic.termℝ "ℝ")])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (coeNotation "↑" `A)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 70, (some 71, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_*_»
      (Term.typeAscription
       "("
       (Term.proj
        (Term.typeAscription
         "("
         (coeNotation
          "↑"
          (Term.typeAscription
           "("
           (coeNotation "↑" `A)
           ":"
           [(Term.app
             (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
             [(Term.paren "(" (Term.app `Fin [(num "2")]) ")") (Data.Real.Basic.termℝ "ℝ")])]
           ")"))
         ":"
         [(Term.app
           `Matrix
           [(Term.paren "(" (Term.app `Fin [(num "2")]) ")")
            (Term.paren "(" (Term.app `Fin [(num "2")]) ")")
            (Data.Real.Basic.termℝ "ℝ")])]
         ")")
        "."
        `det)
       ":"
       [(Data.Complex.Basic.termℂ "ℂ")]
       ")")
      "*"
      (Term.typeAscription
       "("
       (Term.proj
        (Term.typeAscription
         "("
         (coeNotation
          "↑"
          (Term.typeAscription
           "("
           (coeNotation "↑" `B)
           ":"
           [(Term.app
             (Matrix.LinearAlgebra.GeneralLinearGroup.termGL "GL")
             [(Term.paren "(" (Term.app `Fin [(num "2")]) ")") (Data.Real.Basic.termℝ "ℝ")])]
           ")"))
         ":"
         [(Term.app
           `Matrix
           [(Term.paren "(" (Term.app `Fin [(num "2")]) ")")
            (Term.paren "(" (Term.app `Fin [(num "2")]) ")")
            (Data.Real.Basic.termℝ "ℝ")])]
         ")")
        "."
        `det)
       ":"
       [(Data.Complex.Basic.termℂ "ℂ")]
       ")"))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.fieldSimp "field_simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `UpperHalfPlane.num)
         ","
         (Tactic.simpLemma [] [] `UpperHalfPlane.denom)
         ","
         (Tactic.simpLemma [] [] `of_real_mul)
         ","
         (Tactic.simpLemma [] [] `Subgroup.coe_mul)
         ","
         (Tactic.simpLemma [] [] `coe_coe)
         ","
         (Tactic.simpLemma [] [] `UpperHalfPlane.coe_smul)
         ","
         (Tactic.simpLemma [] [] `Units.val_mul)
         ","
         (Tactic.simpLemma [] [] `Matrix.mul_eq_mul)
         ","
         (Tactic.simpLemma [] [] `Matrix.det_mul)
         ","
         (Tactic.simpLemma [] [] `UpperHalfPlane.smulAux)
         ","
         (Tactic.simpLemma [] [] `UpperHalfPlane.smulAux')
         ","
         (Tactic.simpLemma [] [] `Subtype.coe_mk)]
        "]"]
       [(Tactic.location "at" (Tactic.locationWildcard "*"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.coe_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `UpperHalfPlane.smulAux'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `UpperHalfPlane.smulAux
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Matrix.det_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Matrix.mul_eq_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Units.val_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `UpperHalfPlane.coe_smul
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
      `Subgroup.coe_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `of_real_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `UpperHalfPlane.denom
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `UpperHalfPlane.num
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `e3)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e3
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`e3 []]
         [(Term.typeSpec
           ":"
           («term_=_»
            (Algebra.Group.Defs.«term_•_» («term_*_» `A "*" `B) " • " `x)
            "="
            (Algebra.Group.Defs.«term_•_» `A " • " (Algebra.Group.Defs.«term_•_» `B " • " `x))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(convert "convert" [] (Term.app `UpperHalfPlane.mul_smul' [`A `B `x]) [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(convert "convert" [] (Term.app `UpperHalfPlane.mul_smul' [`A `B `x]) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert "convert" [] (Term.app `UpperHalfPlane.mul_smul' [`A `B `x]) [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `UpperHalfPlane.mul_smul' [`A `B `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `B
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `UpperHalfPlane.mul_smul'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Algebra.Group.Defs.«term_•_» («term_*_» `A "*" `B) " • " `x)
       "="
       (Algebra.Group.Defs.«term_•_» `A " • " (Algebra.Group.Defs.«term_•_» `B " • " `x)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_» `A " • " (Algebra.Group.Defs.«term_•_» `B " • " `x))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_» `B " • " `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      `B
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 73 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      `A
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Algebra.Group.Defs.«term_•_» («term_*_» `A "*" `B) " • " `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      («term_*_» `A "*" `B)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `B
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `A
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 74 >? 70, (some 71, term) <=? (some 73, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_*_» `A "*" `B) ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 73, (some 73, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `slash)
         ","
         (Tactic.rwRule [] (Term.app `UpperHalfPlane.denom_cocycle [`A `B `x]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `UpperHalfPlane.denom_cocycle [`A `B `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `B
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `UpperHalfPlane.denom_cocycle
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `slash
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.tacticExt1___ "ext1" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash
        (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash `f " ∣[" `k "]" `A)
        " ∣["
        `k
        "]"
        `B)
       "="
       (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash
        `f
        " ∣["
        `k
        "]"
        («term_*_» `A "*" `B)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash
       `f
       " ∣["
       `k
       "]"
       («term_*_» `A "*" `B))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `A "*" `B)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `B
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `A
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 100 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_*_» `A "*" `B) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 100, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 100, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 100, (some 100, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash
       (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash `f " ∣[" `k "]" `A)
       " ∣["
       `k
       "]"
       `B)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `B
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 100, term))
      (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash `f " ∣[" `k "]" `A)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 100, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 100, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 100, (some 100, term) <=? (some 100, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash `f " ∣[" `k "]" `A)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 100, (some 100, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
       "→"
       (Data.Complex.Basic.termℂ "ℂ"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»
       "GL("
       (num "2")
       ", "
       (Data.Real.Basic.termℝ "ℝ")
       ")"
       "⁺")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»', expected 'NumberTheory.ModularForms.SlashActions.termGL(_,_)⁺._@.NumberTheory.ModularForms.SlashActions._hyg.59'
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
  slash_right_action
  ( k : ℤ ) ( A B : GL( 2 , ℝ ) ⁺ ) ( f : ℍ → ℂ ) : f ∣[ k ] A ∣[ k ] B = f ∣[ k ] A * B
  :=
    by
      ext1
        simp_rw [ slash , UpperHalfPlane.denom_cocycle A B x ]
        have e3 : A * B • x = A • B • x := by convert UpperHalfPlane.mul_smul' A B x
        rw [ e3 ]
        simp
          only
          [
            UpperHalfPlane.num
              ,
              UpperHalfPlane.denom
              ,
              of_real_mul
              ,
              Subgroup.coe_mul
              ,
              coe_coe
              ,
              UpperHalfPlane.coe_smul
              ,
              Units.val_mul
              ,
              Matrix.mul_eq_mul
              ,
              Matrix.det_mul
              ,
              UpperHalfPlane.smulAux
              ,
              UpperHalfPlane.smulAux'
              ,
              Subtype.coe_mk
            ]
          at *
        field_simp
        have
          :
              ( ( ↑ ( ↑ A : GL Fin 2 ℝ ) : Matrix Fin 2 Fin 2 ℝ ) . det : ℂ )
                    *
                    ( ( ↑ ( ↑ B : GL Fin 2 ℝ ) : Matrix Fin 2 Fin 2 ℝ ) . det : ℂ )
                  ^
                  k - 1
                =
                ( ( ↑ ( ↑ A : GL Fin 2 ℝ ) : Matrix Fin 2 Fin 2 ℝ ) . det : ℂ ) ^ k - 1
                  *
                  ( ( ↑ ( ↑ B : GL Fin 2 ℝ ) : Matrix Fin 2 Fin 2 ℝ ) . det : ℂ ) ^ k - 1
            :=
            by simp_rw [ ← mul_zpow ]
        simp_rw [ this , ← mul_assoc , ← mul_zpow ]
#align modular_form.slash_right_action ModularForm.slash_right_action

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
      (Command.declId `slash_add [])
      (Command.declSig
       [(Term.explicitBinder "(" [`k] [":" (termℤ "ℤ")] [] ")")
        (Term.explicitBinder
         "("
         [`A]
         [":"
          (NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»
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
         [`f `g]
         [":"
          (Term.arrow
           (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
           "→"
           (Data.Complex.Basic.termℂ "ℂ"))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash
          («term_+_» `f "+" `g)
          " ∣["
          `k
          "]"
          `A)
         "="
         («term_+_»
          (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash `f " ∣[" `k "]" `A)
          "+"
          (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash
           `g
           " ∣["
           `k
           "]"
           `A)))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.Ext.tacticExt1___ "ext1" [])
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `slash)
              ","
              (Tactic.simpLemma [] [] `Pi.add_apply)
              ","
              (Tactic.simpLemma [] [] `denom)
              ","
              (Tactic.simpLemma [] [] `coe_coe)
              ","
              (Tactic.simpLemma [] [] `zpow_neg)]
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
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `slash)
             ","
             (Tactic.simpLemma [] [] `Pi.add_apply)
             ","
             (Tactic.simpLemma [] [] `denom)
             ","
             (Tactic.simpLemma [] [] `coe_coe)
             ","
             (Tactic.simpLemma [] [] `zpow_neg)]
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
        [(Tactic.simpLemma [] [] `slash)
         ","
         (Tactic.simpLemma [] [] `Pi.add_apply)
         ","
         (Tactic.simpLemma [] [] `denom)
         ","
         (Tactic.simpLemma [] [] `coe_coe)
         ","
         (Tactic.simpLemma [] [] `zpow_neg)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zpow_neg
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
      `Pi.add_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `slash
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.tacticExt1___ "ext1" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash
        («term_+_» `f "+" `g)
        " ∣["
        `k
        "]"
        `A)
       "="
       («term_+_»
        (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash `f " ∣[" `k "]" `A)
        "+"
        (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash `g " ∣[" `k "]" `A)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash `f " ∣[" `k "]" `A)
       "+"
       (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash `g " ∣[" `k "]" `A))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash `g " ∣[" `k "]" `A)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 100, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 100, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 100, (some 100, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash `f " ∣[" `k "]" `A)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 100, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 100, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 100, (some 100, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash
       («term_+_» `f "+" `g)
       " ∣["
       `k
       "]"
       `A)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 100, term))
      («term_+_» `f "+" `g)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (some 100, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `f "+" `g) ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 100, (some 100, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
       "→"
       (Data.Complex.Basic.termℂ "ℂ"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»
       "GL("
       (num "2")
       ", "
       (Data.Real.Basic.termℝ "ℝ")
       ")"
       "⁺")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»', expected 'NumberTheory.ModularForms.SlashActions.termGL(_,_)⁺._@.NumberTheory.ModularForms.SlashActions._hyg.59'
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
    slash_add
    ( k : ℤ ) ( A : GL( 2 , ℝ ) ⁺ ) ( f g : ℍ → ℂ ) : f + g ∣[ k ] A = f ∣[ k ] A + g ∣[ k ] A
    := by ext1 simp only [ slash , Pi.add_apply , denom , coe_coe , zpow_neg ] ring
#align modular_form.slash_add ModularForm.slash_add

@[simp]
theorem slash_one (k : ℤ) (f : ℍ → ℂ) : f ∣[k]1 = f :=
  funext <| by simp [slash]
#align modular_form.slash_one ModularForm.slash_one

variable {α : Type _} [HasSmul α ℂ] [IsScalarTower α ℂ ℂ]

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
      (Command.declId `smul_slash [])
      (Command.declSig
       [(Term.explicitBinder "(" [`k] [":" (termℤ "ℤ")] [] ")")
        (Term.explicitBinder
         "("
         [`A]
         [":"
          (NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»
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
         [`f]
         [":"
          (Term.arrow
           (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
           "→"
           (Data.Complex.Basic.termℂ "ℂ"))]
         []
         ")")
        (Term.explicitBinder "(" [`c] [":" `α] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash
          (Algebra.Group.Defs.«term_•_» `c " • " `f)
          " ∣["
          `k
          "]"
          `A)
         "="
         (Algebra.Group.Defs.«term_•_»
          `c
          " • "
          (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash
           `f
           " ∣["
           `k
           "]"
           `A)))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Mathlib.Tactic.tacticSimp_rw__
            "simp_rw"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app `smul_one_smul [(Data.Complex.Basic.termℂ "ℂ") `c `f]))
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app
                `smul_one_smul
                [(Data.Complex.Basic.termℂ "ℂ")
                 `c
                 (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash
                  `f
                  " ∣["
                  `k
                  "]"
                  `A)]))]
             "]")
            [])
           []
           (Std.Tactic.Ext.tacticExt1___ "ext1" [])
           []
           (Mathlib.Tactic.tacticSimp_rw__
            "simp_rw"
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `slash)] "]")
            [])
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `slash)
              ","
              (Tactic.simpLemma [] [] `Algebra.id.smul_eq_mul)
              ","
              (Tactic.simpLemma [] [] `Matrix.GeneralLinearGroup.coe_det_apply)
              ","
              (Tactic.simpLemma [] [] `Pi.smul_apply)
              ","
              (Tactic.simpLemma [] [] `Subtype.val_eq_coe)
              ","
              (Tactic.simpLemma [] [] `coe_coe)]
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
         [(Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app `smul_one_smul [(Data.Complex.Basic.termℂ "ℂ") `c `f]))
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app
               `smul_one_smul
               [(Data.Complex.Basic.termℂ "ℂ")
                `c
                (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash
                 `f
                 " ∣["
                 `k
                 "]"
                 `A)]))]
            "]")
           [])
          []
          (Std.Tactic.Ext.tacticExt1___ "ext1" [])
          []
          (Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `slash)] "]")
           [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `slash)
             ","
             (Tactic.simpLemma [] [] `Algebra.id.smul_eq_mul)
             ","
             (Tactic.simpLemma [] [] `Matrix.GeneralLinearGroup.coe_det_apply)
             ","
             (Tactic.simpLemma [] [] `Pi.smul_apply)
             ","
             (Tactic.simpLemma [] [] `Subtype.val_eq_coe)
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
        [(Tactic.simpLemma [] [] `slash)
         ","
         (Tactic.simpLemma [] [] `Algebra.id.smul_eq_mul)
         ","
         (Tactic.simpLemma [] [] `Matrix.GeneralLinearGroup.coe_det_apply)
         ","
         (Tactic.simpLemma [] [] `Pi.smul_apply)
         ","
         (Tactic.simpLemma [] [] `Subtype.val_eq_coe)
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
      `Subtype.val_eq_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Pi.smul_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Matrix.GeneralLinearGroup.coe_det_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Algebra.id.smul_eq_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `slash
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `slash)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `slash
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.tacticExt1___ "ext1" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app `smul_one_smul [(Data.Complex.Basic.termℂ "ℂ") `c `f]))
         ","
         (Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app
           `smul_one_smul
           [(Data.Complex.Basic.termℂ "ℂ")
            `c
            (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash
             `f
             " ∣["
             `k
             "]"
             `A)]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `smul_one_smul
       [(Data.Complex.Basic.termℂ "ℂ")
        `c
        (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash `f " ∣[" `k "]" `A)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash `f " ∣[" `k "]" `A)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 100, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 100, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 100, (some 100,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash `f " ∣[" `k "]" `A)
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Complex.Basic.termℂ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Complex.Basic.termℂ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `smul_one_smul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `smul_one_smul [(Data.Complex.Basic.termℂ "ℂ") `c `f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Complex.Basic.termℂ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Complex.Basic.termℂ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `smul_one_smul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash
        (Algebra.Group.Defs.«term_•_» `c " • " `f)
        " ∣["
        `k
        "]"
        `A)
       "="
       (Algebra.Group.Defs.«term_•_»
        `c
        " • "
        (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash `f " ∣[" `k "]" `A)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_»
       `c
       " • "
       (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash `f " ∣[" `k "]" `A))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash `f " ∣[" `k "]" `A)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 100, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 100, term)
[PrettyPrinter.parenthesize] ...precedences are 73 >? 100, (some 100, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash
       (Algebra.Group.Defs.«term_•_» `c " • " `f)
       " ∣["
       `k
       "]"
       `A)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 100, term))
      (Algebra.Group.Defs.«term_•_» `c " • " `f)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      `c
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 73, term) <=? (some 100, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Group.Defs.«term_•_» `c " • " `f)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 100, (some 100, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
       "→"
       (Data.Complex.Basic.termℂ "ℂ"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»
       "GL("
       (num "2")
       ", "
       (Data.Real.Basic.termℝ "ℝ")
       ")"
       "⁺")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»', expected 'NumberTheory.ModularForms.SlashActions.termGL(_,_)⁺._@.NumberTheory.ModularForms.SlashActions._hyg.59'
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
    smul_slash
    ( k : ℤ ) ( A : GL( 2 , ℝ ) ⁺ ) ( f : ℍ → ℂ ) ( c : α ) : c • f ∣[ k ] A = c • f ∣[ k ] A
    :=
      by
        simp_rw [ ← smul_one_smul ℂ c f , ← smul_one_smul ℂ c f ∣[ k ] A ]
          ext1
          simp_rw [ slash ]
          simp
            only
            [
              slash
                ,
                Algebra.id.smul_eq_mul
                ,
                Matrix.GeneralLinearGroup.coe_det_apply
                ,
                Pi.smul_apply
                ,
                Subtype.val_eq_coe
                ,
                coe_coe
              ]
          ring
#align modular_form.smul_slash ModularForm.smul_slash

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
      (Command.declId `neg_slash [])
      (Command.declSig
       [(Term.explicitBinder "(" [`k] [":" (termℤ "ℤ")] [] ")")
        (Term.explicitBinder
         "("
         [`A]
         [":"
          (NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»
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
         [`f]
         [":"
          (Term.arrow
           (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
           "→"
           (Data.Complex.Basic.termℂ "ℂ"))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash
          («term-_» "-" `f)
          " ∣["
          `k
          "]"
          `A)
         "="
         («term-_»
          "-"
          (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash
           `f
           " ∣["
           `k
           "]"
           `A)))))
      (Command.declValSimple
       ":="
       («term_<|_»
        `funext
        "<|"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `slash)] "]"] [])]))))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       `funext
       "<|"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `slash)] "]"] [])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `slash)] "]"] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `slash)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `slash
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `funext
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash
        («term-_» "-" `f)
        " ∣["
        `k
        "]"
        `A)
       "="
       («term-_»
        "-"
        (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash `f " ∣[" `k "]" `A)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_»
       "-"
       (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash `f " ∣[" `k "]" `A))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash `f " ∣[" `k "]" `A)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 100, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 100, term)
[PrettyPrinter.parenthesize] ...precedences are 75 >? 100, (some 100, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash
       («term-_» "-" `f)
       " ∣["
       `k
       "]"
       `A)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 100, term))
      («term-_» "-" `f)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 75, (some 75, term) <=? (some 100, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term-_» "-" `f) ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 100, (some 100, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
       "→"
       (Data.Complex.Basic.termℂ "ℂ"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»
       "GL("
       (num "2")
       ", "
       (Data.Real.Basic.termℝ "ℝ")
       ")"
       "⁺")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»', expected 'NumberTheory.ModularForms.SlashActions.termGL(_,_)⁺._@.NumberTheory.ModularForms.SlashActions._hyg.59'
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
    neg_slash
    ( k : ℤ ) ( A : GL( 2 , ℝ ) ⁺ ) ( f : ℍ → ℂ ) : - f ∣[ k ] A = - f ∣[ k ] A
    := funext <| by simp [ slash ]
#align modular_form.neg_slash ModularForm.neg_slash

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
      (Command.declId `zero_slash [])
      (Command.declSig
       [(Term.explicitBinder "(" [`k] [":" (termℤ "ℤ")] [] ")")
        (Term.explicitBinder
         "("
         [`A]
         [":"
          (NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»
           "GL("
           (num "2")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")"
           "⁺")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash
          (Term.typeAscription
           "("
           (num "0")
           ":"
           [(Term.arrow
             (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
             "→"
             (Data.Complex.Basic.termℂ "ℂ"))]
           ")")
          " ∣["
          `k
          "]"
          `A)
         "="
         (num "0"))))
      (Command.declValSimple
       ":="
       (Term.app
        `funext
        [(Term.fun
          "fun"
          (Term.basicFun
           [(Term.hole "_")]
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
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `slash)
                  ","
                  (Tactic.simpLemma [] [] `Pi.zero_apply)
                  ","
                  (Tactic.simpLemma [] [] `zero_mul)]
                 "]"]
                [])])))))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `funext
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.hole "_")]
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
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `slash)
                 ","
                 (Tactic.simpLemma [] [] `Pi.zero_apply)
                 ","
                 (Tactic.simpLemma [] [] `zero_mul)]
                "]"]
               [])])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.hole "_")]
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
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `slash)
               ","
               (Tactic.simpLemma [] [] `Pi.zero_apply)
               ","
               (Tactic.simpLemma [] [] `zero_mul)]
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
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `slash)
             ","
             (Tactic.simpLemma [] [] `Pi.zero_apply)
             ","
             (Tactic.simpLemma [] [] `zero_mul)]
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
        [(Tactic.simpLemma [] [] `slash)
         ","
         (Tactic.simpLemma [] [] `Pi.zero_apply)
         ","
         (Tactic.simpLemma [] [] `zero_mul)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Pi.zero_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `slash
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `funext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash
        (Term.typeAscription
         "("
         (num "0")
         ":"
         [(Term.arrow
           (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
           "→"
           (Data.Complex.Basic.termℂ "ℂ"))]
         ")")
        " ∣["
        `k
        "]"
        `A)
       "="
       (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (ModularForm.NumberTheory.ModularForms.SlashActions.modular_form.slash
       (Term.typeAscription
        "("
        (num "0")
        ":"
        [(Term.arrow
          (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
          "→"
          (Data.Complex.Basic.termℂ "ℂ"))]
        ")")
       " ∣["
       `k
       "]"
       `A)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 100, term))
      (Term.typeAscription
       "("
       (num "0")
       ":"
       [(Term.arrow
         (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
         "→"
         (Data.Complex.Basic.termℂ "ℂ"))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
       "→"
       (Data.Complex.Basic.termℂ "ℂ"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 100, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 100, (some 100, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»
       "GL("
       (num "2")
       ", "
       (Data.Real.Basic.termℝ "ℝ")
       ")"
       "⁺")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»', expected 'NumberTheory.ModularForms.SlashActions.termGL(_,_)⁺._@.NumberTheory.ModularForms.SlashActions._hyg.59'
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
    zero_slash
    ( k : ℤ ) ( A : GL( 2 , ℝ ) ⁺ ) : ( 0 : ℍ → ℂ ) ∣[ k ] A = 0
    := funext fun _ => by simp only [ slash , Pi.zero_apply , zero_mul ]
#align modular_form.zero_slash ModularForm.zero_slash

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
         `SlashAction
         [(termℤ "ℤ")
          (NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»
           "GL("
           (num "2")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")"
           "⁺")
          (Term.arrow
           (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
           "→"
           (Data.Complex.Basic.termℂ "ℂ"))
          (Data.Complex.Basic.termℂ "ℂ")])))
      (Command.whereStructInst
       "where"
       [(Command.whereStructField (Term.letDecl (Term.letIdDecl `map [] [] ":=" `slash)))
        []
        (Command.whereStructField
         (Term.letDecl (Term.letIdDecl `zero_slash [] [] ":=" `zero_slash)))
        []
        (Command.whereStructField (Term.letDecl (Term.letIdDecl `slash_one [] [] ":=" `slash_one)))
        []
        (Command.whereStructField
         (Term.letDecl (Term.letIdDecl `right_action [] [] ":=" `slash_right_action)))
        []
        (Command.whereStructField
         (Term.letDecl (Term.letIdDecl `smul_action [] [] ":=" `smul_slash)))
        []
        (Command.whereStructField (Term.letDecl (Term.letIdDecl `AddAction [] [] ":=" `slash_add)))]
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
      `slash_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `smul_slash
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `slash_right_action
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `slash_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_slash
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `slash
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `SlashAction
       [(termℤ "ℤ")
        (NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»
         "GL("
         (num "2")
         ", "
         (Data.Real.Basic.termℝ "ℝ")
         ")"
         "⁺")
        (Term.arrow
         (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
         "→"
         (Data.Complex.Basic.termℂ "ℂ"))
        (Data.Complex.Basic.termℂ "ℂ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Complex.Basic.termℂ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Complex.Basic.termℂ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.arrow', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.arrow', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.arrow
       (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
       "→"
       (Data.Complex.Basic.termℂ "ℂ"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 25, (some 25, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.arrow
      (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
      "→"
      (Data.Complex.Basic.termℂ "ℂ"))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»
       "GL("
       (num "2")
       ", "
       (Data.Real.Basic.termℝ "ℝ")
       ")"
       "⁺")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»', expected 'NumberTheory.ModularForms.SlashActions.termGL(_,_)⁺._@.NumberTheory.ModularForms.SlashActions._hyg.59'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  : SlashAction ℤ GL( 2 , ℝ ) ⁺ ℍ → ℂ ℂ
  where
    map := slash
      zero_slash := zero_slash
      slash_one := slash_one
      right_action := slash_right_action
      smul_action := smul_slash
      AddAction := slash_add

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `subgroupAction [])]
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`Γ]
         [":"
          (Term.app
           `Subgroup
           [(NumberTheory.ModularForms.SlashActions.«termSL(_,_)»
             "SL("
             (num "2")
             ", "
             (termℤ "ℤ")
             ")")])]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `SlashAction
         [(termℤ "ℤ")
          `Γ
          (Term.arrow
           (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
           "→"
           (Data.Complex.Basic.termℂ "ℂ"))
          (Data.Complex.Basic.termℂ "ℂ")])))
      (Command.declValSimple
       ":="
       (Term.app
        `monoidHomSlashAction
        [(Term.app
          `MonoidHom.comp
          [`Matrix.SpecialLinearGroup.toGLPos
           (Term.app
            `MonoidHom.comp
            [(Term.app
              `Matrix.SpecialLinearGroup.map
              [(Term.app `Int.castRingHom [(Data.Real.Basic.termℝ "ℝ")])])
             (Term.app `Subgroup.subtype [`Γ])])])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `monoidHomSlashAction
       [(Term.app
         `MonoidHom.comp
         [`Matrix.SpecialLinearGroup.toGLPos
          (Term.app
           `MonoidHom.comp
           [(Term.app
             `Matrix.SpecialLinearGroup.map
             [(Term.app `Int.castRingHom [(Data.Real.Basic.termℝ "ℝ")])])
            (Term.app `Subgroup.subtype [`Γ])])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `MonoidHom.comp
       [`Matrix.SpecialLinearGroup.toGLPos
        (Term.app
         `MonoidHom.comp
         [(Term.app
           `Matrix.SpecialLinearGroup.map
           [(Term.app `Int.castRingHom [(Data.Real.Basic.termℝ "ℝ")])])
          (Term.app `Subgroup.subtype [`Γ])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `MonoidHom.comp
       [(Term.app
         `Matrix.SpecialLinearGroup.map
         [(Term.app `Int.castRingHom [(Data.Real.Basic.termℝ "ℝ")])])
        (Term.app `Subgroup.subtype [`Γ])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Subgroup.subtype [`Γ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Γ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Subgroup.subtype
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Subgroup.subtype [`Γ]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `Matrix.SpecialLinearGroup.map
       [(Term.app `Int.castRingHom [(Data.Real.Basic.termℝ "ℝ")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Int.castRingHom [(Data.Real.Basic.termℝ "ℝ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Int.castRingHom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Int.castRingHom [(Data.Real.Basic.termℝ "ℝ")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Matrix.SpecialLinearGroup.map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `Matrix.SpecialLinearGroup.map
      [(Term.paren "(" (Term.app `Int.castRingHom [(Data.Real.Basic.termℝ "ℝ")]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `MonoidHom.comp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `MonoidHom.comp
      [(Term.paren
        "("
        (Term.app
         `Matrix.SpecialLinearGroup.map
         [(Term.paren "(" (Term.app `Int.castRingHom [(Data.Real.Basic.termℝ "ℝ")]) ")")])
        ")")
       (Term.paren "(" (Term.app `Subgroup.subtype [`Γ]) ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Matrix.SpecialLinearGroup.toGLPos
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `MonoidHom.comp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `MonoidHom.comp
      [`Matrix.SpecialLinearGroup.toGLPos
       (Term.paren
        "("
        (Term.app
         `MonoidHom.comp
         [(Term.paren
           "("
           (Term.app
            `Matrix.SpecialLinearGroup.map
            [(Term.paren "(" (Term.app `Int.castRingHom [(Data.Real.Basic.termℝ "ℝ")]) ")")])
           ")")
          (Term.paren "(" (Term.app `Subgroup.subtype [`Γ]) ")")])
        ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `monoidHomSlashAction
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `SlashAction
       [(termℤ "ℤ")
        `Γ
        (Term.arrow
         (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
         "→"
         (Data.Complex.Basic.termℂ "ℂ"))
        (Data.Complex.Basic.termℂ "ℂ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Complex.Basic.termℂ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Complex.Basic.termℂ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.arrow', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.arrow', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.arrow
       (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
       "→"
       (Data.Complex.Basic.termℂ "ℂ"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 25, (some 25, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.arrow
      (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
      "→"
      (Data.Complex.Basic.termℂ "ℂ"))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Γ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℤ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℤ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (termℤ "ℤ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `SlashAction
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Subgroup
       [(NumberTheory.ModularForms.SlashActions.«termSL(_,_)»
         "SL("
         (num "2")
         ", "
         (termℤ "ℤ")
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.SlashActions.«termSL(_,_)»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.SlashActions.«termSL(_,_)»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.ModularForms.SlashActions.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.SlashActions.«termSL(_,_)»', expected 'NumberTheory.ModularForms.SlashActions.termSL(_,_)._@.NumberTheory.ModularForms.SlashActions._hyg.889'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  subgroupAction
  ( Γ : Subgroup SL( 2 , ℤ ) ) : SlashAction ℤ Γ ℍ → ℂ ℂ
  :=
    monoidHomSlashAction
      MonoidHom.comp
        Matrix.SpecialLinearGroup.toGLPos
          MonoidHom.comp Matrix.SpecialLinearGroup.map Int.castRingHom ℝ Subgroup.subtype Γ
#align modular_form.subgroup_action ModularForm.subgroupAction

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
      (Command.declId `subgroup_slash [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`Γ]
         [":"
          (Term.app
           `Subgroup
           [(NumberTheory.ModularForms.SlashActions.«termSL(_,_)»
             "SL("
             (num "2")
             ", "
             (termℤ "ℤ")
             ")")])]
         []
         ")")
        (Term.explicitBinder "(" [`γ] [":" `Γ] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `SlashAction.map [(Data.Complex.Basic.termℂ "ℂ") `k `γ `f])
         "="
         (Term.app
          `slash
          [`k
           (Term.typeAscription
            "("
            `γ
            ":"
            [(NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»
              "GL("
              (num "2")
              ", "
              (Data.Real.Basic.termℝ "ℝ")
              ")"
              "⁺")]
            ")")
           `f]))))
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
       (Term.app `SlashAction.map [(Data.Complex.Basic.termℂ "ℂ") `k `γ `f])
       "="
       (Term.app
        `slash
        [`k
         (Term.typeAscription
          "("
          `γ
          ":"
          [(NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»
            "GL("
            (num "2")
            ", "
            (Data.Real.Basic.termℝ "ℝ")
            ")"
            "⁺")]
          ")")
         `f]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `slash
       [`k
        (Term.typeAscription
         "("
         `γ
         ":"
         [(NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»
           "GL("
           (num "2")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")"
           "⁺")]
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
       `γ
       ":"
       [(NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»
         "GL("
         (num "2")
         ", "
         (Data.Real.Basic.termℝ "ℝ")
         ")"
         "⁺")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»
       "GL("
       (num "2")
       ", "
       (Data.Real.Basic.termℝ "ℝ")
       ")"
       "⁺")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»', expected 'NumberTheory.ModularForms.SlashActions.termGL(_,_)⁺._@.NumberTheory.ModularForms.SlashActions._hyg.59'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    subgroup_slash
    ( Γ : Subgroup SL( 2 , ℤ ) ) ( γ : Γ )
      : SlashAction.map ℂ k γ f = slash k ( γ : GL( 2 , ℝ ) ⁺ ) f
    := rfl
#align modular_form.subgroup_slash ModularForm.subgroup_slash

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `sLAction [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `SlashAction
         [(termℤ "ℤ")
          (NumberTheory.ModularForms.SlashActions.«termSL(_,_)»
           "SL("
           (num "2")
           ", "
           (termℤ "ℤ")
           ")")
          (Term.arrow
           (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
           "→"
           (Data.Complex.Basic.termℂ "ℂ"))
          (Data.Complex.Basic.termℂ "ℂ")])))
      (Command.declValSimple
       ":="
       (Term.app
        `monoidHomSlashAction
        [(Term.app
          `MonoidHom.comp
          [`Matrix.SpecialLinearGroup.toGLPos
           (Term.app
            `Matrix.SpecialLinearGroup.map
            [(Term.app `Int.castRingHom [(Data.Real.Basic.termℝ "ℝ")])])])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `monoidHomSlashAction
       [(Term.app
         `MonoidHom.comp
         [`Matrix.SpecialLinearGroup.toGLPos
          (Term.app
           `Matrix.SpecialLinearGroup.map
           [(Term.app `Int.castRingHom [(Data.Real.Basic.termℝ "ℝ")])])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `MonoidHom.comp
       [`Matrix.SpecialLinearGroup.toGLPos
        (Term.app
         `Matrix.SpecialLinearGroup.map
         [(Term.app `Int.castRingHom [(Data.Real.Basic.termℝ "ℝ")])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Matrix.SpecialLinearGroup.map
       [(Term.app `Int.castRingHom [(Data.Real.Basic.termℝ "ℝ")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Int.castRingHom [(Data.Real.Basic.termℝ "ℝ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Int.castRingHom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Int.castRingHom [(Data.Real.Basic.termℝ "ℝ")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Matrix.SpecialLinearGroup.map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `Matrix.SpecialLinearGroup.map
      [(Term.paren "(" (Term.app `Int.castRingHom [(Data.Real.Basic.termℝ "ℝ")]) ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Matrix.SpecialLinearGroup.toGLPos
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `MonoidHom.comp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `MonoidHom.comp
      [`Matrix.SpecialLinearGroup.toGLPos
       (Term.paren
        "("
        (Term.app
         `Matrix.SpecialLinearGroup.map
         [(Term.paren "(" (Term.app `Int.castRingHom [(Data.Real.Basic.termℝ "ℝ")]) ")")])
        ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `monoidHomSlashAction
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `SlashAction
       [(termℤ "ℤ")
        (NumberTheory.ModularForms.SlashActions.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")
        (Term.arrow
         (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
         "→"
         (Data.Complex.Basic.termℂ "ℂ"))
        (Data.Complex.Basic.termℂ "ℂ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Complex.Basic.termℂ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Complex.Basic.termℂ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.arrow', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.arrow', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.arrow
       (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
       "→"
       (Data.Complex.Basic.termℂ "ℂ"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 25, (some 25, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.arrow
      (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
      "→"
      (Data.Complex.Basic.termℂ "ℂ"))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.SlashActions.«termSL(_,_)»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.SlashActions.«termSL(_,_)»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (NumberTheory.ModularForms.SlashActions.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.SlashActions.«termSL(_,_)»', expected 'NumberTheory.ModularForms.SlashActions.termSL(_,_)._@.NumberTheory.ModularForms.SlashActions._hyg.889'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  sLAction
  : SlashAction ℤ SL( 2 , ℤ ) ℍ → ℂ ℂ
  :=
    monoidHomSlashAction
      MonoidHom.comp
        Matrix.SpecialLinearGroup.toGLPos Matrix.SpecialLinearGroup.map Int.castRingHom ℝ
#align modular_form.SL_action ModularForm.sLAction

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
      (Command.declId `SL_slash [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`γ]
         [":"
          (NumberTheory.ModularForms.SlashActions.«termSL(_,_)»
           "SL("
           (num "2")
           ", "
           (termℤ "ℤ")
           ")")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `SlashAction.map [(Data.Complex.Basic.termℂ "ℂ") `k `γ `f])
         "="
         (Term.app
          `slash
          [`k
           (Term.typeAscription
            "("
            `γ
            ":"
            [(NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»
              "GL("
              (num "2")
              ", "
              (Data.Real.Basic.termℝ "ℝ")
              ")"
              "⁺")]
            ")")
           `f]))))
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
       (Term.app `SlashAction.map [(Data.Complex.Basic.termℂ "ℂ") `k `γ `f])
       "="
       (Term.app
        `slash
        [`k
         (Term.typeAscription
          "("
          `γ
          ":"
          [(NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»
            "GL("
            (num "2")
            ", "
            (Data.Real.Basic.termℝ "ℝ")
            ")"
            "⁺")]
          ")")
         `f]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `slash
       [`k
        (Term.typeAscription
         "("
         `γ
         ":"
         [(NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»
           "GL("
           (num "2")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")"
           "⁺")]
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
       `γ
       ":"
       [(NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»
         "GL("
         (num "2")
         ", "
         (Data.Real.Basic.termℝ "ℝ")
         ")"
         "⁺")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»
       "GL("
       (num "2")
       ", "
       (Data.Real.Basic.termℝ "ℝ")
       ")"
       "⁺")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»', expected 'NumberTheory.ModularForms.SlashActions.termGL(_,_)⁺._@.NumberTheory.ModularForms.SlashActions._hyg.59'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    SL_slash
    ( γ : SL( 2 , ℤ ) ) : SlashAction.map ℂ k γ f = slash k ( γ : GL( 2 , ℝ ) ⁺ ) f
    := rfl
#align modular_form.SL_slash ModularForm.SL_slash

-- mathport name: «expr ∣[ , ]»
local notation:73 f "∣[" k:0 "," A "]" => SlashAction.map ℂ k A f

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The constant function 1 is invariant under any element of `SL(2, ℤ)`. -/")]
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `is_invariant_one [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`A]
         [":"
          (NumberTheory.ModularForms.SlashActions.«termSL(_,_)»
           "SL("
           (num "2")
           ", "
           (termℤ "ℤ")
           ")")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]»
          (Term.typeAscription
           "("
           (num "1")
           ":"
           [(Term.arrow
             (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
             "→"
             (Data.Complex.Basic.termℂ "ℂ"))]
           ")")
          "∣["
          (Term.typeAscription "(" (num "0") ":" [(termℤ "ℤ")] ")")
          ","
          `A
          "]")
         "="
         (Term.typeAscription
          "("
          (num "1")
          ":"
          [(Term.arrow
            (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
            "→"
            (Data.Complex.Basic.termℂ "ℂ"))]
          ")"))))
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
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Term.typeAscription
                  "("
                  (Term.proj
                   (NumberTheory.ModularForms.SlashActions.«term↑ₘ_»
                    "↑ₘ"
                    (Term.typeAscription
                     "("
                     `A
                     ":"
                     [(NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»
                       "GL("
                       (num "2")
                       ", "
                       (Data.Real.Basic.termℝ "ℝ")
                       ")"
                       "⁺")]
                     ")"))
                   "."
                   `det)
                  ":"
                  [(Data.Real.Basic.termℝ "ℝ")]
                  ")")
                 "="
                 (num "1")))]
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
                    [(Tactic.simpLemma [] [] `coe_coe)
                     ","
                     (Tactic.simpLemma
                      []
                      []
                      `Matrix.SpecialLinearGroup.coe_GL_pos_coe_GL_coe_matrix)
                     ","
                     (Tactic.simpLemma [] [] `Matrix.SpecialLinearGroup.det_coe)]
                    "]"]
                   [])]))))))
           []
           (tacticFunext__ "funext" [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `SL_slash)
              ","
              (Tactic.rwRule [] `slash)
              ","
              (Tactic.rwRule [] `zero_sub)
              ","
              (Tactic.rwRule [] `this)]
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
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.typeAscription
                 "("
                 (Term.proj
                  (NumberTheory.ModularForms.SlashActions.«term↑ₘ_»
                   "↑ₘ"
                   (Term.typeAscription
                    "("
                    `A
                    ":"
                    [(NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»
                      "GL("
                      (num "2")
                      ", "
                      (Data.Real.Basic.termℝ "ℝ")
                      ")"
                      "⁺")]
                    ")"))
                  "."
                  `det)
                 ":"
                 [(Data.Real.Basic.termℝ "ℝ")]
                 ")")
                "="
                (num "1")))]
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
                   [(Tactic.simpLemma [] [] `coe_coe)
                    ","
                    (Tactic.simpLemma [] [] `Matrix.SpecialLinearGroup.coe_GL_pos_coe_GL_coe_matrix)
                    ","
                    (Tactic.simpLemma [] [] `Matrix.SpecialLinearGroup.det_coe)]
                   "]"]
                  [])]))))))
          []
          (tacticFunext__ "funext" [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `SL_slash)
             ","
             (Tactic.rwRule [] `slash)
             ","
             (Tactic.rwRule [] `zero_sub)
             ","
             (Tactic.rwRule [] `this)]
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
        [(Tactic.rwRule [] `SL_slash)
         ","
         (Tactic.rwRule [] `slash)
         ","
         (Tactic.rwRule [] `zero_sub)
         ","
         (Tactic.rwRule [] `this)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `slash
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `SL_slash
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tacticFunext__ "funext" [])
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
            (Term.typeAscription
             "("
             (Term.proj
              (NumberTheory.ModularForms.SlashActions.«term↑ₘ_»
               "↑ₘ"
               (Term.typeAscription
                "("
                `A
                ":"
                [(NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»
                  "GL("
                  (num "2")
                  ", "
                  (Data.Real.Basic.termℝ "ℝ")
                  ")"
                  "⁺")]
                ")"))
              "."
              `det)
             ":"
             [(Data.Real.Basic.termℝ "ℝ")]
             ")")
            "="
            (num "1")))]
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
               [(Tactic.simpLemma [] [] `coe_coe)
                ","
                (Tactic.simpLemma [] [] `Matrix.SpecialLinearGroup.coe_GL_pos_coe_GL_coe_matrix)
                ","
                (Tactic.simpLemma [] [] `Matrix.SpecialLinearGroup.det_coe)]
               "]"]
              [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
            [(Tactic.simpLemma [] [] `coe_coe)
             ","
             (Tactic.simpLemma [] [] `Matrix.SpecialLinearGroup.coe_GL_pos_coe_GL_coe_matrix)
             ","
             (Tactic.simpLemma [] [] `Matrix.SpecialLinearGroup.det_coe)]
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
        [(Tactic.simpLemma [] [] `coe_coe)
         ","
         (Tactic.simpLemma [] [] `Matrix.SpecialLinearGroup.coe_GL_pos_coe_GL_coe_matrix)
         ","
         (Tactic.simpLemma [] [] `Matrix.SpecialLinearGroup.det_coe)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Matrix.SpecialLinearGroup.det_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Matrix.SpecialLinearGroup.coe_GL_pos_coe_GL_coe_matrix
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.typeAscription
        "("
        (Term.proj
         (NumberTheory.ModularForms.SlashActions.«term↑ₘ_»
          "↑ₘ"
          (Term.typeAscription
           "("
           `A
           ":"
           [(NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»
             "GL("
             (num "2")
             ", "
             (Data.Real.Basic.termℝ "ℝ")
             ")"
             "⁺")]
           ")"))
         "."
         `det)
        ":"
        [(Data.Real.Basic.termℝ "ℝ")]
        ")")
       "="
       (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription
       "("
       (Term.proj
        (NumberTheory.ModularForms.SlashActions.«term↑ₘ_»
         "↑ₘ"
         (Term.typeAscription
          "("
          `A
          ":"
          [(NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»
            "GL("
            (num "2")
            ", "
            (Data.Real.Basic.termℝ "ℝ")
            ")"
            "⁺")]
          ")"))
        "."
        `det)
       ":"
       [(Data.Real.Basic.termℝ "ℝ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (NumberTheory.ModularForms.SlashActions.«term↑ₘ_»
        "↑ₘ"
        (Term.typeAscription
         "("
         `A
         ":"
         [(NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»
           "GL("
           (num "2")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")"
           "⁺")]
         ")"))
       "."
       `det)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (NumberTheory.ModularForms.SlashActions.«term↑ₘ_»
       "↑ₘ"
       (Term.typeAscription
        "("
        `A
        ":"
        [(NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»
          "GL("
          (num "2")
          ", "
          (Data.Real.Basic.termℝ "ℝ")
          ")"
          "⁺")]
        ")"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.SlashActions.«term↑ₘ_»', expected 'NumberTheory.ModularForms.SlashActions.term↑ₘ_._@.NumberTheory.ModularForms.SlashActions._hyg.8'
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
/-- The constant function 1 is invariant under any element of `SL(2, ℤ)`. -/ @[ simp ]
  theorem
    is_invariant_one
    ( A : SL( 2 , ℤ ) ) : ( 1 : ℍ → ℂ ) ∣[ ( 0 : ℤ ) , A ] = ( 1 : ℍ → ℂ )
    :=
      by
        have
            : ( ↑ₘ ( A : GL( 2 , ℝ ) ⁺ ) . det : ℝ ) = 1
              :=
              by
                simp
                  only
                  [
                    coe_coe
                      ,
                      Matrix.SpecialLinearGroup.coe_GL_pos_coe_GL_coe_matrix
                      ,
                      Matrix.SpecialLinearGroup.det_coe
                    ]
          funext
          rw [ SL_slash , slash , zero_sub , this ]
          simp
#align modular_form.is_invariant_one ModularForm.is_invariant_one

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "A function `f : ℍ → ℂ` is `slash_invariant`, of weight `k ∈ ℤ` and level `Γ`,\n  if for every matrix `γ ∈ Γ` we have `f(γ • z)= (c*z+d)^k f(z)` where `γ= ![![a, b], ![c, d]]`,\n  and it acts on `ℍ` via Möbius transformations. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `slash_action_eq'_iff [])
      (Command.declSig
       [(Term.explicitBinder "(" [`k] [":" (termℤ "ℤ")] [] ")")
        (Term.explicitBinder
         "("
         [`Γ]
         [":"
          (Term.app
           `Subgroup
           [(NumberTheory.ModularForms.SlashActions.«termSL(_,_)»
             "SL("
             (num "2")
             ", "
             (termℤ "ℤ")
             ")")])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`f]
         [":"
          (Term.arrow
           (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
           "→"
           (Data.Complex.Basic.termℂ "ℂ"))]
         []
         ")")
        (Term.explicitBinder "(" [`γ] [":" `Γ] [] ")")
        (Term.explicitBinder
         "("
         [`z]
         [":" (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_=_»
          (Term.app
           (ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]» `f "∣[" `k "," `γ "]")
           [`z])
          "="
          (Term.app `f [`z]))
         "↔"
         («term_=_»
          (Term.app `f [(Algebra.Group.Defs.«term_•_» `γ " • " `z)])
          "="
          («term_*_»
           («term_^_»
            («term_+_»
             («term_*_»
              (Term.typeAscription
               "("
               (Term.app
                (NumberTheory.ModularForms.SlashActions.«term↑ₘ_» "↑ₘ" `γ)
                [(num "1") (num "0")])
               ":"
               [(Data.Complex.Basic.termℂ "ℂ")]
               ")")
              "*"
              `z)
             "+"
             (Term.typeAscription
              "("
              (Term.app
               (NumberTheory.ModularForms.SlashActions.«term↑ₘ_» "↑ₘ" `γ)
               [(num "1") (num "1")])
              ":"
              [(Data.Complex.Basic.termℂ "ℂ")]
              ")"))
            "^"
            `k)
           "*"
           (Term.app `f [`z]))))))
      (Command.declValSimple
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
             [(Tactic.simpLemma [] [] `subgroup_slash)
              ","
              (Tactic.simpLemma [] [] `ModularForm.slash)]
             "]"]
            [])
           []
           (convert
            "convert"
            []
            (Term.app `inv_mul_eq_iff_eq_mul₀ [(Term.hole "_")])
            ["using" (num "2")])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]") [])
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `denom)
                ","
                (Tactic.simpLemma [] [] `coe_coe)
                ","
                (Tactic.simpLemma [] [] `Matrix.SpecialLinearGroup.coe_GL_pos_coe_GL_coe_matrix)
                ","
                (Tactic.simpLemma [] [] `zpow_neg)
                ","
                (Tactic.simpLemma [] [] `Matrix.SpecialLinearGroup.det_coe)
                ","
                (Tactic.simpLemma [] [] `of_real_one)
                ","
                (Tactic.simpLemma [] [] `one_zpow)
                ","
                (Tactic.simpLemma [] [] `mul_one)
                ","
                (Tactic.simpLemma [] [] `subgroup_to_sl_moeb)
                ","
                (Tactic.simpLemma [] [] `sl_moeb)]
               "]"]
              [])
             []
             (Tactic.tacticRfl "rfl")])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(convert
              "convert"
              []
              (Term.app `zpow_ne_zero [`k (Term.app `denom_ne_zero [`γ `z])])
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
         [(Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `subgroup_slash)
             ","
             (Tactic.simpLemma [] [] `ModularForm.slash)]
            "]"]
           [])
          []
          (convert
           "convert"
           []
           (Term.app `inv_mul_eq_iff_eq_mul₀ [(Term.hole "_")])
           ["using" (num "2")])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]") [])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `denom)
               ","
               (Tactic.simpLemma [] [] `coe_coe)
               ","
               (Tactic.simpLemma [] [] `Matrix.SpecialLinearGroup.coe_GL_pos_coe_GL_coe_matrix)
               ","
               (Tactic.simpLemma [] [] `zpow_neg)
               ","
               (Tactic.simpLemma [] [] `Matrix.SpecialLinearGroup.det_coe)
               ","
               (Tactic.simpLemma [] [] `of_real_one)
               ","
               (Tactic.simpLemma [] [] `one_zpow)
               ","
               (Tactic.simpLemma [] [] `mul_one)
               ","
               (Tactic.simpLemma [] [] `subgroup_to_sl_moeb)
               ","
               (Tactic.simpLemma [] [] `sl_moeb)]
              "]"]
             [])
            []
            (Tactic.tacticRfl "rfl")])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(convert
             "convert"
             []
             (Term.app `zpow_ne_zero [`k (Term.app `denom_ne_zero [`γ `z])])
             [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(convert "convert" [] (Term.app `zpow_ne_zero [`k (Term.app `denom_ne_zero [`γ `z])]) [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert "convert" [] (Term.app `zpow_ne_zero [`k (Term.app `denom_ne_zero [`γ `z])]) [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `zpow_ne_zero [`k (Term.app `denom_ne_zero [`γ `z])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `denom_ne_zero [`γ `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `γ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `denom_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `denom_ne_zero [`γ `z]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `zpow_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]") [])
        []
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `denom)
           ","
           (Tactic.simpLemma [] [] `coe_coe)
           ","
           (Tactic.simpLemma [] [] `Matrix.SpecialLinearGroup.coe_GL_pos_coe_GL_coe_matrix)
           ","
           (Tactic.simpLemma [] [] `zpow_neg)
           ","
           (Tactic.simpLemma [] [] `Matrix.SpecialLinearGroup.det_coe)
           ","
           (Tactic.simpLemma [] [] `of_real_one)
           ","
           (Tactic.simpLemma [] [] `one_zpow)
           ","
           (Tactic.simpLemma [] [] `mul_one)
           ","
           (Tactic.simpLemma [] [] `subgroup_to_sl_moeb)
           ","
           (Tactic.simpLemma [] [] `sl_moeb)]
          "]"]
         [])
        []
        (Tactic.tacticRfl "rfl")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `denom)
         ","
         (Tactic.simpLemma [] [] `coe_coe)
         ","
         (Tactic.simpLemma [] [] `Matrix.SpecialLinearGroup.coe_GL_pos_coe_GL_coe_matrix)
         ","
         (Tactic.simpLemma [] [] `zpow_neg)
         ","
         (Tactic.simpLemma [] [] `Matrix.SpecialLinearGroup.det_coe)
         ","
         (Tactic.simpLemma [] [] `of_real_one)
         ","
         (Tactic.simpLemma [] [] `one_zpow)
         ","
         (Tactic.simpLemma [] [] `mul_one)
         ","
         (Tactic.simpLemma [] [] `subgroup_to_sl_moeb)
         ","
         (Tactic.simpLemma [] [] `sl_moeb)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sl_moeb
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `subgroup_to_sl_moeb
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_zpow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `of_real_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Matrix.SpecialLinearGroup.det_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zpow_neg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Matrix.SpecialLinearGroup.coe_GL_pos_coe_GL_coe_matrix
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_comm)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert
       "convert"
       []
       (Term.app `inv_mul_eq_iff_eq_mul₀ [(Term.hole "_")])
       ["using" (num "2")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `inv_mul_eq_iff_eq_mul₀ [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `inv_mul_eq_iff_eq_mul₀
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `subgroup_slash) "," (Tactic.simpLemma [] [] `ModularForm.slash)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ModularForm.slash
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `subgroup_slash
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_=_»
        (Term.app
         (ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]» `f "∣[" `k "," `γ "]")
         [`z])
        "="
        (Term.app `f [`z]))
       "↔"
       («term_=_»
        (Term.app `f [(Algebra.Group.Defs.«term_•_» `γ " • " `z)])
        "="
        («term_*_»
         («term_^_»
          («term_+_»
           («term_*_»
            (Term.typeAscription
             "("
             (Term.app
              (NumberTheory.ModularForms.SlashActions.«term↑ₘ_» "↑ₘ" `γ)
              [(num "1") (num "0")])
             ":"
             [(Data.Complex.Basic.termℂ "ℂ")]
             ")")
            "*"
            `z)
           "+"
           (Term.typeAscription
            "("
            (Term.app
             (NumberTheory.ModularForms.SlashActions.«term↑ₘ_» "↑ₘ" `γ)
             [(num "1") (num "1")])
            ":"
            [(Data.Complex.Basic.termℂ "ℂ")]
            ")"))
          "^"
          `k)
         "*"
         (Term.app `f [`z]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app `f [(Algebra.Group.Defs.«term_•_» `γ " • " `z)])
       "="
       («term_*_»
        («term_^_»
         («term_+_»
          («term_*_»
           (Term.typeAscription
            "("
            (Term.app
             (NumberTheory.ModularForms.SlashActions.«term↑ₘ_» "↑ₘ" `γ)
             [(num "1") (num "0")])
            ":"
            [(Data.Complex.Basic.termℂ "ℂ")]
            ")")
           "*"
           `z)
          "+"
          (Term.typeAscription
           "("
           (Term.app
            (NumberTheory.ModularForms.SlashActions.«term↑ₘ_» "↑ₘ" `γ)
            [(num "1") (num "1")])
           ":"
           [(Data.Complex.Basic.termℂ "ℂ")]
           ")"))
         "^"
         `k)
        "*"
        (Term.app `f [`z])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_^_»
        («term_+_»
         («term_*_»
          (Term.typeAscription
           "("
           (Term.app
            (NumberTheory.ModularForms.SlashActions.«term↑ₘ_» "↑ₘ" `γ)
            [(num "1") (num "0")])
           ":"
           [(Data.Complex.Basic.termℂ "ℂ")]
           ")")
          "*"
          `z)
         "+"
         (Term.typeAscription
          "("
          (Term.app
           (NumberTheory.ModularForms.SlashActions.«term↑ₘ_» "↑ₘ" `γ)
           [(num "1") (num "1")])
          ":"
          [(Data.Complex.Basic.termℂ "ℂ")]
          ")"))
        "^"
        `k)
       "*"
       (Term.app `f [`z]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_^_»
       («term_+_»
        («term_*_»
         (Term.typeAscription
          "("
          (Term.app
           (NumberTheory.ModularForms.SlashActions.«term↑ₘ_» "↑ₘ" `γ)
           [(num "1") (num "0")])
          ":"
          [(Data.Complex.Basic.termℂ "ℂ")]
          ")")
         "*"
         `z)
        "+"
        (Term.typeAscription
         "("
         (Term.app (NumberTheory.ModularForms.SlashActions.«term↑ₘ_» "↑ₘ" `γ) [(num "1") (num "1")])
         ":"
         [(Data.Complex.Basic.termℂ "ℂ")]
         ")"))
       "^"
       `k)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      («term_+_»
       («term_*_»
        (Term.typeAscription
         "("
         (Term.app (NumberTheory.ModularForms.SlashActions.«term↑ₘ_» "↑ₘ" `γ) [(num "1") (num "0")])
         ":"
         [(Data.Complex.Basic.termℂ "ℂ")]
         ")")
        "*"
        `z)
       "+"
       (Term.typeAscription
        "("
        (Term.app (NumberTheory.ModularForms.SlashActions.«term↑ₘ_» "↑ₘ" `γ) [(num "1") (num "1")])
        ":"
        [(Data.Complex.Basic.termℂ "ℂ")]
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.app (NumberTheory.ModularForms.SlashActions.«term↑ₘ_» "↑ₘ" `γ) [(num "1") (num "1")])
       ":"
       [(Data.Complex.Basic.termℂ "ℂ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (NumberTheory.ModularForms.SlashActions.«term↑ₘ_» "↑ₘ" `γ) [(num "1") (num "1")])
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
      (NumberTheory.ModularForms.SlashActions.«term↑ₘ_» "↑ₘ" `γ)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.SlashActions.«term↑ₘ_»', expected 'NumberTheory.ModularForms.SlashActions.term↑ₘ_._@.NumberTheory.ModularForms.SlashActions._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    A function `f : ℍ → ℂ` is `slash_invariant`, of weight `k ∈ ℤ` and level `Γ`,
      if for every matrix `γ ∈ Γ` we have `f(γ • z)= (c*z+d)^k f(z)` where `γ= ![![a, b], ![c, d]]`,
      and it acts on `ℍ` via Möbius transformations. -/
  theorem
    slash_action_eq'_iff
    ( k : ℤ ) ( Γ : Subgroup SL( 2 , ℤ ) ) ( f : ℍ → ℂ ) ( γ : Γ ) ( z : ℍ )
      : f ∣[ k , γ ] z = f z ↔ f γ • z = ( ↑ₘ γ 1 0 : ℂ ) * z + ( ↑ₘ γ 1 1 : ℂ ) ^ k * f z
    :=
      by
        simp only [ subgroup_slash , ModularForm.slash ]
          convert inv_mul_eq_iff_eq_mul₀ _ using 2
          ·
            rw [ mul_comm ]
              simp
                only
                [
                  denom
                    ,
                    coe_coe
                    ,
                    Matrix.SpecialLinearGroup.coe_GL_pos_coe_GL_coe_matrix
                    ,
                    zpow_neg
                    ,
                    Matrix.SpecialLinearGroup.det_coe
                    ,
                    of_real_one
                    ,
                    one_zpow
                    ,
                    mul_one
                    ,
                    subgroup_to_sl_moeb
                    ,
                    sl_moeb
                  ]
              rfl
          · convert zpow_ne_zero k denom_ne_zero γ z
#align modular_form.slash_action_eq'_iff ModularForm.slash_action_eq'_iff

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mul_slash [])
      (Command.declSig
       [(Term.explicitBinder "(" [`k1 `k2] [":" (termℤ "ℤ")] [] ")")
        (Term.explicitBinder
         "("
         [`A]
         [":"
          (NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»
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
         [`f `g]
         [":"
          (Term.arrow
           (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
           "→"
           (Data.Complex.Basic.termℂ "ℂ"))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]»
          («term_*_» `f "*" `g)
          "∣["
          («term_+_» `k1 "+" `k2)
          ","
          `A
          "]")
         "="
         («term_*_»
          (Algebra.Group.Defs.«term_•_»
           (Term.typeAscription
            "("
            (Term.proj (NumberTheory.ModularForms.SlashActions.«term↑ₘ_» "↑ₘ" `A) "." `det)
            ":"
            [(Data.Real.Basic.termℝ "ℝ")]
            ")")
           " • "
           (ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]»
            `f
            "∣["
            `k1
            ","
            `A
            "]"))
          "*"
          (ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]»
           `g
           "∣["
           `k2
           ","
           `A
           "]")))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.Ext.tacticExt1___ "ext1" [])
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `SlashAction.map)
              ","
              (Tactic.simpLemma [] [] `slash)
              ","
              (Tactic.simpLemma [] [] `Matrix.GeneralLinearGroup.coe_det_apply)
              ","
              (Tactic.simpLemma [] [] `Subtype.val_eq_coe)
              ","
              (Tactic.simpLemma [] [] `Pi.mul_apply)
              ","
              (Tactic.simpLemma [] [] `Pi.smul_apply)
              ","
              (Tactic.simpLemma [] [] `Algebra.smul_mul_assoc)
              ","
              (Tactic.simpLemma [] [] `real_smul)]
             "]"]
            [])
           []
           (Mathlib.Tactic.set
            "set"
            []
            (Mathlib.Tactic.setArgsRest
             `d
             [":" (Data.Complex.Basic.termℂ "ℂ")]
             ":="
             (coeNotation
              "↑"
              (Term.typeAscription
               "("
               (Term.proj (NumberTheory.ModularForms.SlashActions.«term↑ₘ_» "↑ₘ" `A) "." `det)
               ":"
               [(Data.Real.Basic.termℝ "ℝ")]
               ")"))
             []))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`h1 []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 («term_^_» `d "^" («term_-_» («term_+_» `k1 "+" `k2) "-" (num "1")))
                 "="
                 («term_*_»
                  («term_*_» `d "*" («term_^_» `d "^" («term_-_» `k1 "-" (num "1"))))
                  "*"
                  («term_^_» `d "^" («term_-_» `k2 "-" (num "1"))))))]
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
                     [(Term.typeSpec ":" («term_≠_» `d "≠" (num "0")))]
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `d)] "]"] [])
                         []
                         (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
                         []
                         (Tactic.exact "exact" (Term.app `Matrix.gLPos.det_ne_zero [`A]))]))))))
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule
                      [(patternIgnore (token.«← » "←"))]
                      (Term.app `zpow_one_add₀ [`this]))
                     ","
                     (Tactic.rwRule
                      [(patternIgnore (token.«← » "←"))]
                      (Term.app `zpow_add₀ [`this]))]
                    "]")
                   [])
                  []
                  (Mathlib.Tactic.RingNF.ring "ring")]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`h22 []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 («term_^_» (Term.app `denom [`A `x]) "^" («term-_» "-" («term_+_» `k1 "+" `k2)))
                 "="
                 («term_*_»
                  («term_^_» (Term.app `denom [`A `x]) "^" («term-_» "-" `k1))
                  "*"
                  («term_^_» (Term.app `denom [`A `x]) "^" («term-_» "-" `k2)))))]
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
                    [(Tactic.rwRule [] `Int.neg_add) "," (Tactic.rwRule [] `zpow_add₀)]
                    "]")
                   [])
                  []
                  (Tactic.exact "exact" (Term.app `UpperHalfPlane.denom_ne_zero [`A `x]))]))))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h1) "," (Tactic.rwRule [] `h22)] "]")
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
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `SlashAction.map)
             ","
             (Tactic.simpLemma [] [] `slash)
             ","
             (Tactic.simpLemma [] [] `Matrix.GeneralLinearGroup.coe_det_apply)
             ","
             (Tactic.simpLemma [] [] `Subtype.val_eq_coe)
             ","
             (Tactic.simpLemma [] [] `Pi.mul_apply)
             ","
             (Tactic.simpLemma [] [] `Pi.smul_apply)
             ","
             (Tactic.simpLemma [] [] `Algebra.smul_mul_assoc)
             ","
             (Tactic.simpLemma [] [] `real_smul)]
            "]"]
           [])
          []
          (Mathlib.Tactic.set
           "set"
           []
           (Mathlib.Tactic.setArgsRest
            `d
            [":" (Data.Complex.Basic.termℂ "ℂ")]
            ":="
            (coeNotation
             "↑"
             (Term.typeAscription
              "("
              (Term.proj (NumberTheory.ModularForms.SlashActions.«term↑ₘ_» "↑ₘ" `A) "." `det)
              ":"
              [(Data.Real.Basic.termℝ "ℝ")]
              ")"))
            []))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h1 []]
             [(Term.typeSpec
               ":"
               («term_=_»
                («term_^_» `d "^" («term_-_» («term_+_» `k1 "+" `k2) "-" (num "1")))
                "="
                («term_*_»
                 («term_*_» `d "*" («term_^_» `d "^" («term_-_» `k1 "-" (num "1"))))
                 "*"
                 («term_^_» `d "^" («term_-_» `k2 "-" (num "1"))))))]
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
                    [(Term.typeSpec ":" («term_≠_» `d "≠" (num "0")))]
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `d)] "]"] [])
                        []
                        (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
                        []
                        (Tactic.exact "exact" (Term.app `Matrix.gLPos.det_ne_zero [`A]))]))))))
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     (Term.app `zpow_one_add₀ [`this]))
                    ","
                    (Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     (Term.app `zpow_add₀ [`this]))]
                   "]")
                  [])
                 []
                 (Mathlib.Tactic.RingNF.ring "ring")]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h22 []]
             [(Term.typeSpec
               ":"
               («term_=_»
                («term_^_» (Term.app `denom [`A `x]) "^" («term-_» "-" («term_+_» `k1 "+" `k2)))
                "="
                («term_*_»
                 («term_^_» (Term.app `denom [`A `x]) "^" («term-_» "-" `k1))
                 "*"
                 («term_^_» (Term.app `denom [`A `x]) "^" («term-_» "-" `k2)))))]
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
                   [(Tactic.rwRule [] `Int.neg_add) "," (Tactic.rwRule [] `zpow_add₀)]
                   "]")
                  [])
                 []
                 (Tactic.exact "exact" (Term.app `UpperHalfPlane.denom_ne_zero [`A `x]))]))))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h1) "," (Tactic.rwRule [] `h22)] "]")
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
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h1) "," (Tactic.rwRule [] `h22)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h22
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`h22 []]
         [(Term.typeSpec
           ":"
           («term_=_»
            («term_^_» (Term.app `denom [`A `x]) "^" («term-_» "-" («term_+_» `k1 "+" `k2)))
            "="
            («term_*_»
             («term_^_» (Term.app `denom [`A `x]) "^" («term-_» "-" `k1))
             "*"
             («term_^_» (Term.app `denom [`A `x]) "^" («term-_» "-" `k2)))))]
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
               [(Tactic.rwRule [] `Int.neg_add) "," (Tactic.rwRule [] `zpow_add₀)]
               "]")
              [])
             []
             (Tactic.exact "exact" (Term.app `UpperHalfPlane.denom_ne_zero [`A `x]))]))))))
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
            [(Tactic.rwRule [] `Int.neg_add) "," (Tactic.rwRule [] `zpow_add₀)]
            "]")
           [])
          []
          (Tactic.exact "exact" (Term.app `UpperHalfPlane.denom_ne_zero [`A `x]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `UpperHalfPlane.denom_ne_zero [`A `x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `UpperHalfPlane.denom_ne_zero [`A `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `UpperHalfPlane.denom_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `Int.neg_add) "," (Tactic.rwRule [] `zpow_add₀)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zpow_add₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.neg_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       («term_^_» (Term.app `denom [`A `x]) "^" («term-_» "-" («term_+_» `k1 "+" `k2)))
       "="
       («term_*_»
        («term_^_» (Term.app `denom [`A `x]) "^" («term-_» "-" `k1))
        "*"
        («term_^_» (Term.app `denom [`A `x]) "^" («term-_» "-" `k2))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_^_» (Term.app `denom [`A `x]) "^" («term-_» "-" `k1))
       "*"
       («term_^_» (Term.app `denom [`A `x]) "^" («term-_» "-" `k2)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (Term.app `denom [`A `x]) "^" («term-_» "-" `k2))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" `k2)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k2
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 80 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term-_» "-" `k2) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `denom [`A `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `denom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_^_» (Term.app `denom [`A `x]) "^" («term-_» "-" `k1))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" `k1)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k1
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 80 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term-_» "-" `k1) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `denom [`A `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `denom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 80, (some 80, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_^_» (Term.app `denom [`A `x]) "^" («term-_» "-" («term_+_» `k1 "+" `k2)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" («term_+_» `k1 "+" `k2))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `k1 "+" `k2)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k2
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `k1
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 75 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `k1 "+" `k2) ")")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term-_» "-" (Term.paren "(" («term_+_» `k1 "+" `k2) ")"))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.app `denom [`A `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `denom
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 1023, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`h1 []]
         [(Term.typeSpec
           ":"
           («term_=_»
            («term_^_» `d "^" («term_-_» («term_+_» `k1 "+" `k2) "-" (num "1")))
            "="
            («term_*_»
             («term_*_» `d "*" («term_^_» `d "^" («term_-_» `k1 "-" (num "1"))))
             "*"
             («term_^_» `d "^" («term_-_» `k2 "-" (num "1"))))))]
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
                [(Term.typeSpec ":" («term_≠_» `d "≠" (num "0")))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `d)] "]"] [])
                    []
                    (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
                    []
                    (Tactic.exact "exact" (Term.app `Matrix.gLPos.det_ne_zero [`A]))]))))))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `zpow_one_add₀ [`this]))
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `zpow_add₀ [`this]))]
               "]")
              [])
             []
             (Mathlib.Tactic.RingNF.ring "ring")]))))))
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
             [(Term.typeSpec ":" («term_≠_» `d "≠" (num "0")))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `d)] "]"] [])
                 []
                 (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
                 []
                 (Tactic.exact "exact" (Term.app `Matrix.gLPos.det_ne_zero [`A]))]))))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `zpow_one_add₀ [`this]))
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `zpow_add₀ [`this]))]
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
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `zpow_one_add₀ [`this]))
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `zpow_add₀ [`this]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `zpow_add₀ [`this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `zpow_add₀
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `zpow_one_add₀ [`this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `zpow_one_add₀
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
         [(Term.typeSpec ":" («term_≠_» `d "≠" (num "0")))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `d)] "]"] [])
             []
             (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
             []
             (Tactic.exact "exact" (Term.app `Matrix.gLPos.det_ne_zero [`A]))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `d)] "]"] [])
          []
          (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
          []
          (Tactic.exact "exact" (Term.app `Matrix.gLPos.det_ne_zero [`A]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `Matrix.gLPos.det_ne_zero [`A]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Matrix.gLPos.det_ne_zero [`A])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Matrix.gLPos.det_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `d)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `d
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» `d "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `d
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       («term_^_» `d "^" («term_-_» («term_+_» `k1 "+" `k2) "-" (num "1")))
       "="
       («term_*_»
        («term_*_» `d "*" («term_^_» `d "^" («term_-_» `k1 "-" (num "1"))))
        "*"
        («term_^_» `d "^" («term_-_» `k2 "-" (num "1")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_*_» `d "*" («term_^_» `d "^" («term_-_» `k1 "-" (num "1"))))
       "*"
       («term_^_» `d "^" («term_-_» `k2 "-" (num "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `d "^" («term_-_» `k2 "-" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» `k2 "-" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `k2
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_-_» `k2 "-" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `d
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_*_» `d "*" («term_^_» `d "^" («term_-_» `k1 "-" (num "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `d "^" («term_-_» `k1 "-" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» `k1 "-" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `k1
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_-_» `k1 "-" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `d
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `d
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_^_» `d "^" («term_-_» («term_+_» `k1 "+" `k2) "-" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» («term_+_» `k1 "+" `k2) "-" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_+_» `k1 "+" `k2)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k2
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `k1
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 65, (some 66, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_-_» («term_+_» `k1 "+" `k2) "-" (num "1"))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `d
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.set
       "set"
       []
       (Mathlib.Tactic.setArgsRest
        `d
        [":" (Data.Complex.Basic.termℂ "ℂ")]
        ":="
        (coeNotation
         "↑"
         (Term.typeAscription
          "("
          (Term.proj (NumberTheory.ModularForms.SlashActions.«term↑ₘ_» "↑ₘ" `A) "." `det)
          ":"
          [(Data.Real.Basic.termℝ "ℝ")]
          ")"))
        []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (coeNotation
       "↑"
       (Term.typeAscription
        "("
        (Term.proj (NumberTheory.ModularForms.SlashActions.«term↑ₘ_» "↑ₘ" `A) "." `det)
        ":"
        [(Data.Real.Basic.termℝ "ℝ")]
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.proj (NumberTheory.ModularForms.SlashActions.«term↑ₘ_» "↑ₘ" `A) "." `det)
       ":"
       [(Data.Real.Basic.termℝ "ℝ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (NumberTheory.ModularForms.SlashActions.«term↑ₘ_» "↑ₘ" `A) "." `det)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (NumberTheory.ModularForms.SlashActions.«term↑ₘ_» "↑ₘ" `A)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.SlashActions.«term↑ₘ_»', expected 'NumberTheory.ModularForms.SlashActions.term↑ₘ_._@.NumberTheory.ModularForms.SlashActions._hyg.8'
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
  mul_slash
  ( k1 k2 : ℤ ) ( A : GL( 2 , ℝ ) ⁺ ) ( f g : ℍ → ℂ )
    : f * g ∣[ k1 + k2 , A ] = ( ↑ₘ A . det : ℝ ) • f ∣[ k1 , A ] * g ∣[ k2 , A ]
  :=
    by
      ext1
        simp
          only
          [
            SlashAction.map
              ,
              slash
              ,
              Matrix.GeneralLinearGroup.coe_det_apply
              ,
              Subtype.val_eq_coe
              ,
              Pi.mul_apply
              ,
              Pi.smul_apply
              ,
              Algebra.smul_mul_assoc
              ,
              real_smul
            ]
        set d : ℂ := ↑ ( ↑ₘ A . det : ℝ )
        have
          h1
            : d ^ k1 + k2 - 1 = d * d ^ k1 - 1 * d ^ k2 - 1
            :=
            by
              have : d ≠ 0 := by dsimp [ d ] norm_cast exact Matrix.gLPos.det_ne_zero A
                rw [ ← zpow_one_add₀ this , ← zpow_add₀ this ]
                ring
        have
          h22
            : denom A x ^ - k1 + k2 = denom A x ^ - k1 * denom A x ^ - k2
            :=
            by rw [ Int.neg_add , zpow_add₀ ] exact UpperHalfPlane.denom_ne_zero A x
        rw [ h1 , h22 ]
        ring
#align modular_form.mul_slash ModularForm.mul_slash

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
      (Command.declId `mul_slash_SL2 [])
      (Command.declSig
       [(Term.explicitBinder "(" [`k1 `k2] [":" (termℤ "ℤ")] [] ")")
        (Term.explicitBinder
         "("
         [`A]
         [":"
          (NumberTheory.ModularForms.SlashActions.«termSL(_,_)»
           "SL("
           (num "2")
           ", "
           (termℤ "ℤ")
           ")")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`f `g]
         [":"
          (Term.arrow
           (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
           "→"
           (Data.Complex.Basic.termℂ "ℂ"))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]»
          («term_*_» `f "*" `g)
          "∣["
          («term_+_» `k1 "+" `k2)
          ","
          `A
          "]")
         "="
         («term_*_»
          (ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]» `f "∣[" `k1 "," `A "]")
          "*"
          (ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]»
           `g
           "∣["
           `k2
           ","
           `A
           "]")))))
      (Command.declValSimple
       ":="
       (calc
        "calc"
        (calcStep
         («term_=_»
          (ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]»
           («term_*_» `f "*" `g)
           "∣["
           («term_+_» `k1 "+" `k2)
           ","
           (Term.typeAscription
            "("
            `A
            ":"
            [(NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»
              "GL("
              (num "2")
              ", "
              (Data.Real.Basic.termℝ "ℝ")
              ")"
              "⁺")]
            ")")
           "]")
          "="
          («term_*_»
           (Algebra.Group.Defs.«term_•_»
            (Term.hole "_")
            " • "
            (ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]»
             `f
             "∣["
             `k1
             ","
             `A
             "]"))
           "*"
           (ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]»
            `g
            "∣["
            `k2
            ","
            `A
            "]")))
         ":="
         (Term.app
          `mul_slash
          [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")]))
        [(calcStep
          («term_=_»
           (Term.hole "_")
           "="
           («term_*_»
            (Algebra.Group.Defs.«term_•_»
             (Term.typeAscription "(" (num "1") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
             " • "
             (ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]»
              `f
              "∣["
              `k1
              ","
              `A
              "]"))
            "*"
            (ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]»
             `g
             "∣["
             `k2
             ","
             `A
             "]")))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.simp
               "simp"
               []
               []
               []
               ["[" [(Tactic.simpErase "-" `Matrix.SpecialLinearGroup.coe_matrix_coe)] "]"]
               [])]))))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           («term_*_»
            (ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]»
             `f
             "∣["
             `k1
             ","
             `A
             "]")
            "*"
            (ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]»
             `g
             "∣["
             `k2
             ","
             `A
             "]")))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])]))))])
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
         (ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]»
          («term_*_» `f "*" `g)
          "∣["
          («term_+_» `k1 "+" `k2)
          ","
          (Term.typeAscription
           "("
           `A
           ":"
           [(NumberTheory.ModularForms.SlashActions.«termGL(_,_)⁺»
             "GL("
             (num "2")
             ", "
             (Data.Real.Basic.termℝ "ℝ")
             ")"
             "⁺")]
           ")")
          "]")
         "="
         («term_*_»
          (Algebra.Group.Defs.«term_•_»
           (Term.hole "_")
           " • "
           (ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]»
            `f
            "∣["
            `k1
            ","
            `A
            "]"))
          "*"
          (ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]»
           `g
           "∣["
           `k2
           ","
           `A
           "]")))
        ":="
        (Term.app
         `mul_slash
         [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")]))
       [(calcStep
         («term_=_»
          (Term.hole "_")
          "="
          («term_*_»
           (Algebra.Group.Defs.«term_•_»
            (Term.typeAscription "(" (num "1") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
            " • "
            (ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]»
             `f
             "∣["
             `k1
             ","
             `A
             "]"))
           "*"
           (ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]»
            `g
            "∣["
            `k2
            ","
            `A
            "]")))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.simp
              "simp"
              []
              []
              []
              ["[" [(Tactic.simpErase "-" `Matrix.SpecialLinearGroup.coe_matrix_coe)] "]"]
              [])]))))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          («term_*_»
           (ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]» `f "∣[" `k1 "," `A "]")
           "*"
           (ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]»
            `g
            "∣["
            `k2
            ","
            `A
            "]")))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])]))))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       («term_*_»
        (ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]» `f "∣[" `k1 "," `A "]")
        "*"
        (ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]» `g "∣[" `k2 "," `A "]")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]» `f "∣[" `k1 "," `A "]")
       "*"
       (ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]» `g "∣[" `k2 "," `A "]"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]» `g "∣[" `k2 "," `A "]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]»', expected 'ModularForm.NumberTheory.ModularForms.SlashActions.term_∣[_,_]._@.NumberTheory.ModularForms.SlashActions._hyg.2396'
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
    mul_slash_SL2
    ( k1 k2 : ℤ ) ( A : SL( 2 , ℤ ) ) ( f g : ℍ → ℂ )
      : f * g ∣[ k1 + k2 , A ] = f ∣[ k1 , A ] * g ∣[ k2 , A ]
    :=
      calc
        f * g ∣[ k1 + k2 , ( A : GL( 2 , ℝ ) ⁺ ) ] = _ • f ∣[ k1 , A ] * g ∣[ k2 , A ]
          :=
          mul_slash _ _ _ _ _
        _ = ( 1 : ℝ ) • f ∣[ k1 , A ] * g ∣[ k2 , A ]
            :=
            by simp [ - Matrix.SpecialLinearGroup.coe_matrix_coe ]
          _ = f ∣[ k1 , A ] * g ∣[ k2 , A ] := by simp
#align modular_form.mul_slash_SL2 ModularForm.mul_slash_SL2

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mul_slash_subgroup [])
      (Command.declSig
       [(Term.explicitBinder "(" [`k1 `k2] [":" (termℤ "ℤ")] [] ")")
        (Term.explicitBinder
         "("
         [`Γ]
         [":"
          (Term.app
           `Subgroup
           [(NumberTheory.ModularForms.SlashActions.«termSL(_,_)»
             "SL("
             (num "2")
             ", "
             (termℤ "ℤ")
             ")")])]
         []
         ")")
        (Term.explicitBinder "(" [`A] [":" `Γ] [] ")")
        (Term.explicitBinder
         "("
         [`f `g]
         [":"
          (Term.arrow
           (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
           "→"
           (Data.Complex.Basic.termℂ "ℂ"))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]»
          («term_*_» `f "*" `g)
          "∣["
          («term_+_» `k1 "+" `k2)
          ","
          `A
          "]")
         "="
         («term_*_»
          (ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]» `f "∣[" `k1 "," `A "]")
          "*"
          (ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]»
           `g
           "∣["
           `k2
           ","
           `A
           "]")))))
      (Command.declValSimple ":=" (Term.app `mul_slash_SL2 [`k1 `k2 `A `f `g]) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_slash_SL2 [`k1 `k2 `A `f `g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k2
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_slash_SL2
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]»
        («term_*_» `f "*" `g)
        "∣["
        («term_+_» `k1 "+" `k2)
        ","
        `A
        "]")
       "="
       («term_*_»
        (ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]» `f "∣[" `k1 "," `A "]")
        "*"
        (ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]» `g "∣[" `k2 "," `A "]")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]» `f "∣[" `k1 "," `A "]")
       "*"
       (ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]» `g "∣[" `k2 "," `A "]"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]» `g "∣[" `k2 "," `A "]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ModularForm.NumberTheory.ModularForms.SlashActions.«term_∣[_,_]»', expected 'ModularForm.NumberTheory.ModularForms.SlashActions.term_∣[_,_]._@.NumberTheory.ModularForms.SlashActions._hyg.2396'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  mul_slash_subgroup
  ( k1 k2 : ℤ ) ( Γ : Subgroup SL( 2 , ℤ ) ) ( A : Γ ) ( f g : ℍ → ℂ )
    : f * g ∣[ k1 + k2 , A ] = f ∣[ k1 , A ] * g ∣[ k2 , A ]
  := mul_slash_SL2 k1 k2 A f g
#align modular_form.mul_slash_subgroup ModularForm.mul_slash_subgroup

end ModularForm

