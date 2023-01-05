/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck

! This file was ported from Lean 3 source module number_theory.modular_forms.congruence_subgroups
! leanprover-community/mathlib commit 6d0adfa76594f304b4650d098273d4366edeb61b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.SpecialLinearGroup
import Mathbin.Data.Zmod.Basic
import Mathbin.GroupTheory.Subgroup.Pointwise
import Mathbin.GroupTheory.GroupAction.ConjAct

/-!
# Congruence subgroups

This defines congruence subgroups of `SL(2, ℤ)` such as `Γ(N)`, `Γ₀(N)` and `Γ₁(N)` for `N` a
natural number.

It also contains basic results about congruence subgroups.

-/


-- mathport name: «exprSL( , )»
local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToFun

-- mathport name: «expr↑ₘ »
local prefix:1024 "↑ₘ" => @coe _ (Matrix (Fin 2) (Fin 2) _) _

open Matrix.SpecialLinearGroup Matrix

variable (N : ℕ)

-- mathport name: «exprSLMOD( )»
local notation "SLMOD(" N ")" =>
  @Matrix.SpecialLinearGroup.map (Fin 2) _ _ _ _ _ _ (Int.castRingHom (Zmod N))

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
      (Command.declId `SL_reduction_mod_hom_val [])
      (Command.declSig
       [(Term.explicitBinder "(" [`N] [":" (termℕ "ℕ")] [] ")")
        (Term.explicitBinder
         "("
         [`γ]
         [":"
          (NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»
           "SL("
           (num "2")
           ", "
           (termℤ "ℤ")
           ")")]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.forall
         "∀"
         [`i `j]
         [(Term.typeSpec ":" (Term.app `Fin [(num "2")]))]
         ","
         («term_=_»
          (Term.app
           (Term.typeAscription
            "("
            (Term.app
             (NumberTheory.ModularForms.CongruenceSubgroups.«termSLMOD(_)» "SLMOD(" `N ")")
             [`γ])
            ":"
            [(Term.app
              `Matrix
              [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (Term.app `Zmod [`N])])]
            ")")
           [`i `j])
          "="
          (Term.typeAscription
           "("
           (Term.typeAscription
            "("
            (Term.app (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `γ) [`i `j])
            ":"
            [(termℤ "ℤ")]
            ")")
           ":"
           [(Term.app `Zmod [`N])]
           ")")))))
      (Command.declValSimple ":=" (Term.fun "fun" (Term.basicFun [`i `j] [] "=>" `rfl)) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`i `j] [] "=>" `rfl))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.forall
       "∀"
       [`i `j]
       [(Term.typeSpec ":" (Term.app `Fin [(num "2")]))]
       ","
       («term_=_»
        (Term.app
         (Term.typeAscription
          "("
          (Term.app
           (NumberTheory.ModularForms.CongruenceSubgroups.«termSLMOD(_)» "SLMOD(" `N ")")
           [`γ])
          ":"
          [(Term.app
            `Matrix
            [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (Term.app `Zmod [`N])])]
          ")")
         [`i `j])
        "="
        (Term.typeAscription
         "("
         (Term.typeAscription
          "("
          (Term.app (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `γ) [`i `j])
          ":"
          [(termℤ "ℤ")]
          ")")
         ":"
         [(Term.app `Zmod [`N])]
         ")")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app
        (Term.typeAscription
         "("
         (Term.app
          (NumberTheory.ModularForms.CongruenceSubgroups.«termSLMOD(_)» "SLMOD(" `N ")")
          [`γ])
         ":"
         [(Term.app
           `Matrix
           [(Term.app `Fin [(num "2")]) (Term.app `Fin [(num "2")]) (Term.app `Zmod [`N])])]
         ")")
        [`i `j])
       "="
       (Term.typeAscription
        "("
        (Term.typeAscription
         "("
         (Term.app (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `γ) [`i `j])
         ":"
         [(termℤ "ℤ")]
         ")")
        ":"
        [(Term.app `Zmod [`N])]
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.typeAscription
        "("
        (Term.app (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `γ) [`i `j])
        ":"
        [(termℤ "ℤ")]
        ")")
       ":"
       [(Term.app `Zmod [`N])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Zmod [`N])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `N
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Zmod
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.app (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `γ) [`i `j])
       ":"
       [(termℤ "ℤ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℤ "ℤ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `γ) [`i `j])
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
      (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `γ)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_»', expected 'NumberTheory.ModularForms.CongruenceSubgroups.term↑ₘ_._@.NumberTheory.ModularForms.CongruenceSubgroups._hyg.836'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    SL_reduction_mod_hom_val
    ( N : ℕ ) ( γ : SL( 2 , ℤ ) )
      :
        ∀
          i j
          : Fin 2
          ,
          ( SLMOD( N ) γ : Matrix Fin 2 Fin 2 Zmod N ) i j = ( ( ↑ₘ γ i j : ℤ ) : Zmod N )
    := fun i j => rfl
#align SL_reduction_mod_hom_val SL_reduction_mod_hom_val

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The full level `N` congruence subgroup of `SL(2, ℤ)` of matrices that reduce to the identity\nmodulo `N`.-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `gamma [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`N] [":" (termℕ "ℕ")] [] ")")]
       [(Term.typeSpec
         ":"
         (Term.app
          `Subgroup
          [(NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»
            "SL("
            (num "2")
            ", "
            (termℤ "ℤ")
            ")")]))])
      (Command.declValSimple
       ":="
       (Term.proj
        (NumberTheory.ModularForms.CongruenceSubgroups.«termSLMOD(_)» "SLMOD(" `N ")")
        "."
        `ker)
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (NumberTheory.ModularForms.CongruenceSubgroups.«termSLMOD(_)» "SLMOD(" `N ")")
       "."
       `ker)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (NumberTheory.ModularForms.CongruenceSubgroups.«termSLMOD(_)» "SLMOD(" `N ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.CongruenceSubgroups.«termSLMOD(_)»', expected 'NumberTheory.ModularForms.CongruenceSubgroups.termSLMOD(_)._@.NumberTheory.ModularForms.CongruenceSubgroups._hyg.879'
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
    The full level `N` congruence subgroup of `SL(2, ℤ)` of matrices that reduce to the identity
    modulo `N`.-/
  def gamma ( N : ℕ ) : Subgroup SL( 2 , ℤ ) := SLMOD( N ) . ker
#align Gamma gamma

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `Gamma_mem' [])
      (Command.declSig
       [(Term.explicitBinder "(" [`N] [":" (termℕ "ℕ")] [] ")")
        (Term.explicitBinder
         "("
         [`γ]
         [":"
          (NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»
           "SL("
           (num "2")
           ", "
           (termℤ "ℤ")
           ")")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_∈_» `γ "∈" (Term.app `gamma [`N]))
         "↔"
         («term_=_»
          (Term.app
           (NumberTheory.ModularForms.CongruenceSubgroups.«termSLMOD(_)» "SLMOD(" `N ")")
           [`γ])
          "="
          (num "1")))))
      (Command.declValSimple ":=" `Iff.rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Iff.rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_∈_» `γ "∈" (Term.app `gamma [`N]))
       "↔"
       («term_=_»
        (Term.app
         (NumberTheory.ModularForms.CongruenceSubgroups.«termSLMOD(_)» "SLMOD(" `N ")")
         [`γ])
        "="
        (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app
        (NumberTheory.ModularForms.CongruenceSubgroups.«termSLMOD(_)» "SLMOD(" `N ")")
        [`γ])
       "="
       (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (NumberTheory.ModularForms.CongruenceSubgroups.«termSLMOD(_)» "SLMOD(" `N ")") [`γ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `γ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (NumberTheory.ModularForms.CongruenceSubgroups.«termSLMOD(_)» "SLMOD(" `N ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.CongruenceSubgroups.«termSLMOD(_)»', expected 'NumberTheory.ModularForms.CongruenceSubgroups.termSLMOD(_)._@.NumberTheory.ModularForms.CongruenceSubgroups._hyg.879'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem Gamma_mem' ( N : ℕ ) ( γ : SL( 2 , ℤ ) ) : γ ∈ gamma N ↔ SLMOD( N ) γ = 1 := Iff.rfl
#align Gamma_mem' Gamma_mem'

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
      (Command.declId `Gamma_mem [])
      (Command.declSig
       [(Term.explicitBinder "(" [`N] [":" (termℕ "ℕ")] [] ")")
        (Term.explicitBinder
         "("
         [`γ]
         [":"
          (NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»
           "SL("
           (num "2")
           ", "
           (termℤ "ℤ")
           ")")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_∈_» `γ "∈" (Term.app `gamma [`N]))
         "↔"
         («term_∧_»
          («term_=_»
           (Term.typeAscription
            "("
            (Term.typeAscription
             "("
             (Term.app
              (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `γ)
              [(num "0") (num "0")])
             ":"
             [(termℤ "ℤ")]
             ")")
            ":"
            [(Term.app `Zmod [`N])]
            ")")
           "="
           (num "1"))
          "∧"
          («term_∧_»
           («term_=_»
            (Term.typeAscription
             "("
             (Term.typeAscription
              "("
              (Term.app
               (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `γ)
               [(num "0") (num "1")])
              ":"
              [(termℤ "ℤ")]
              ")")
             ":"
             [(Term.app `Zmod [`N])]
             ")")
            "="
            (num "0"))
           "∧"
           («term_∧_»
            («term_=_»
             (Term.typeAscription
              "("
              (Term.typeAscription
               "("
               (Term.app
                (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `γ)
                [(num "1") (num "0")])
               ":"
               [(termℤ "ℤ")]
               ")")
              ":"
              [(Term.app `Zmod [`N])]
              ")")
             "="
             (num "0"))
            "∧"
            («term_=_»
             (Term.typeAscription
              "("
              (Term.typeAscription
               "("
               (Term.app
                (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `γ)
                [(num "1") (num "1")])
               ":"
               [(termℤ "ℤ")]
               ")")
              ":"
              [(Term.app `Zmod [`N])]
              ")")
             "="
             (num "1"))))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Gamma_mem')] "]") [])
           []
           (Tactic.constructor "constructor")
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.intro "intro" [`h])
             []
             (Tactic.simp
              "simp"
              []
              []
              []
              ["["
               [(Tactic.simpLemma
                 []
                 [(patternIgnore (token.«← » "←"))]
                 (Term.app `SL_reduction_mod_hom_val [`N `γ]))
                ","
                (Tactic.simpLemma [] [] `h)]
               "]"]
              [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.intro "intro" [`h])
             []
             (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] (Term.app `SL_reduction_mod_hom_val [`N `γ]))]
               "]")
              [])
             []
             (Tactic.«tactic_<;>_»
              (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
              "<;>"
              (Lean.Elab.Tactic.finCases "fin_cases" [`j] []))
             []
             (Tactic.allGoals
              "all_goals"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Mathlib.Tactic.tacticSimp_rw__
                  "simp_rw"
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]")
                  [])
                 ";"
                 (Tactic.tacticRfl "rfl")])))])])))
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
         [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Gamma_mem')] "]") [])
          []
          (Tactic.constructor "constructor")
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro "intro" [`h])
            []
            (Tactic.simp
             "simp"
             []
             []
             []
             ["["
              [(Tactic.simpLemma
                []
                [(patternIgnore (token.«← » "←"))]
                (Term.app `SL_reduction_mod_hom_val [`N `γ]))
               ","
               (Tactic.simpLemma [] [] `h)]
              "]"]
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro "intro" [`h])
            []
            (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] (Term.app `SL_reduction_mod_hom_val [`N `γ]))]
              "]")
             [])
            []
            (Tactic.«tactic_<;>_»
             (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
             "<;>"
             (Lean.Elab.Tactic.finCases "fin_cases" [`j] []))
            []
            (Tactic.allGoals
             "all_goals"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Mathlib.Tactic.tacticSimp_rw__
                 "simp_rw"
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]")
                 [])
                ";"
                (Tactic.tacticRfl "rfl")])))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.intro "intro" [`h])
        []
        (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] (Term.app `SL_reduction_mod_hom_val [`N `γ]))]
          "]")
         [])
        []
        (Tactic.«tactic_<;>_»
         (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
         "<;>"
         (Lean.Elab.Tactic.finCases "fin_cases" [`j] []))
        []
        (Tactic.allGoals
         "all_goals"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Mathlib.Tactic.tacticSimp_rw__
             "simp_rw"
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]")
             [])
            ";"
            (Tactic.tacticRfl "rfl")])))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.allGoals
       "all_goals"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]")
           [])
          ";"
          (Tactic.tacticRfl "rfl")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Lean.Elab.Tactic.finCases "fin_cases" [`i] [])
       "<;>"
       (Lean.Elab.Tactic.finCases "fin_cases" [`j] []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Lean.Elab.Tactic.finCases "fin_cases" [`j] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'token.«*»'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
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
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `SL_reduction_mod_hom_val [`N `γ]))] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `SL_reduction_mod_hom_val [`N `γ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `γ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `N
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `SL_reduction_mod_hom_val
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`h])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.intro "intro" [`h])
        []
        (Tactic.simp
         "simp"
         []
         []
         []
         ["["
          [(Tactic.simpLemma
            []
            [(patternIgnore (token.«← » "←"))]
            (Term.app `SL_reduction_mod_hom_val [`N `γ]))
           ","
           (Tactic.simpLemma [] [] `h)]
          "]"]
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpLemma
          []
          [(patternIgnore (token.«← » "←"))]
          (Term.app `SL_reduction_mod_hom_val [`N `γ]))
         ","
         (Tactic.simpLemma [] [] `h)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `SL_reduction_mod_hom_val [`N `γ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `γ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `N
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `SL_reduction_mod_hom_val
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`h])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.constructor "constructor")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Gamma_mem')] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Gamma_mem'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_∈_» `γ "∈" (Term.app `gamma [`N]))
       "↔"
       («term_∧_»
        («term_=_»
         (Term.typeAscription
          "("
          (Term.typeAscription
           "("
           (Term.app
            (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `γ)
            [(num "0") (num "0")])
           ":"
           [(termℤ "ℤ")]
           ")")
          ":"
          [(Term.app `Zmod [`N])]
          ")")
         "="
         (num "1"))
        "∧"
        («term_∧_»
         («term_=_»
          (Term.typeAscription
           "("
           (Term.typeAscription
            "("
            (Term.app
             (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `γ)
             [(num "0") (num "1")])
            ":"
            [(termℤ "ℤ")]
            ")")
           ":"
           [(Term.app `Zmod [`N])]
           ")")
          "="
          (num "0"))
         "∧"
         («term_∧_»
          («term_=_»
           (Term.typeAscription
            "("
            (Term.typeAscription
             "("
             (Term.app
              (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `γ)
              [(num "1") (num "0")])
             ":"
             [(termℤ "ℤ")]
             ")")
            ":"
            [(Term.app `Zmod [`N])]
            ")")
           "="
           (num "0"))
          "∧"
          («term_=_»
           (Term.typeAscription
            "("
            (Term.typeAscription
             "("
             (Term.app
              (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `γ)
              [(num "1") (num "1")])
             ":"
             [(termℤ "ℤ")]
             ")")
            ":"
            [(Term.app `Zmod [`N])]
            ")")
           "="
           (num "1"))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∧_»
       («term_=_»
        (Term.typeAscription
         "("
         (Term.typeAscription
          "("
          (Term.app
           (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `γ)
           [(num "0") (num "0")])
          ":"
          [(termℤ "ℤ")]
          ")")
         ":"
         [(Term.app `Zmod [`N])]
         ")")
        "="
        (num "1"))
       "∧"
       («term_∧_»
        («term_=_»
         (Term.typeAscription
          "("
          (Term.typeAscription
           "("
           (Term.app
            (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `γ)
            [(num "0") (num "1")])
           ":"
           [(termℤ "ℤ")]
           ")")
          ":"
          [(Term.app `Zmod [`N])]
          ")")
         "="
         (num "0"))
        "∧"
        («term_∧_»
         («term_=_»
          (Term.typeAscription
           "("
           (Term.typeAscription
            "("
            (Term.app
             (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `γ)
             [(num "1") (num "0")])
            ":"
            [(termℤ "ℤ")]
            ")")
           ":"
           [(Term.app `Zmod [`N])]
           ")")
          "="
          (num "0"))
         "∧"
         («term_=_»
          (Term.typeAscription
           "("
           (Term.typeAscription
            "("
            (Term.app
             (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `γ)
             [(num "1") (num "1")])
            ":"
            [(termℤ "ℤ")]
            ")")
           ":"
           [(Term.app `Zmod [`N])]
           ")")
          "="
          (num "1")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∧_»
       («term_=_»
        (Term.typeAscription
         "("
         (Term.typeAscription
          "("
          (Term.app
           (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `γ)
           [(num "0") (num "1")])
          ":"
          [(termℤ "ℤ")]
          ")")
         ":"
         [(Term.app `Zmod [`N])]
         ")")
        "="
        (num "0"))
       "∧"
       («term_∧_»
        («term_=_»
         (Term.typeAscription
          "("
          (Term.typeAscription
           "("
           (Term.app
            (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `γ)
            [(num "1") (num "0")])
           ":"
           [(termℤ "ℤ")]
           ")")
          ":"
          [(Term.app `Zmod [`N])]
          ")")
         "="
         (num "0"))
        "∧"
        («term_=_»
         (Term.typeAscription
          "("
          (Term.typeAscription
           "("
           (Term.app
            (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `γ)
            [(num "1") (num "1")])
           ":"
           [(termℤ "ℤ")]
           ")")
          ":"
          [(Term.app `Zmod [`N])]
          ")")
         "="
         (num "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∧_»
       («term_=_»
        (Term.typeAscription
         "("
         (Term.typeAscription
          "("
          (Term.app
           (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `γ)
           [(num "1") (num "0")])
          ":"
          [(termℤ "ℤ")]
          ")")
         ":"
         [(Term.app `Zmod [`N])]
         ")")
        "="
        (num "0"))
       "∧"
       («term_=_»
        (Term.typeAscription
         "("
         (Term.typeAscription
          "("
          (Term.app
           (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `γ)
           [(num "1") (num "1")])
          ":"
          [(termℤ "ℤ")]
          ")")
         ":"
         [(Term.app `Zmod [`N])]
         ")")
        "="
        (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.typeAscription
        "("
        (Term.typeAscription
         "("
         (Term.app
          (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `γ)
          [(num "1") (num "1")])
         ":"
         [(termℤ "ℤ")]
         ")")
        ":"
        [(Term.app `Zmod [`N])]
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
       (Term.typeAscription
        "("
        (Term.app
         (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `γ)
         [(num "1") (num "1")])
        ":"
        [(termℤ "ℤ")]
        ")")
       ":"
       [(Term.app `Zmod [`N])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Zmod [`N])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `N
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Zmod
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.app
        (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `γ)
        [(num "1") (num "1")])
       ":"
       [(termℤ "ℤ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℤ "ℤ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `γ)
       [(num "1") (num "1")])
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
      (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `γ)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_»', expected 'NumberTheory.ModularForms.CongruenceSubgroups.term↑ₘ_._@.NumberTheory.ModularForms.CongruenceSubgroups._hyg.836'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    Gamma_mem
    ( N : ℕ ) ( γ : SL( 2 , ℤ ) )
      :
        γ ∈ gamma N
          ↔
          ( ( ↑ₘ γ 0 0 : ℤ ) : Zmod N ) = 1
            ∧
            ( ( ↑ₘ γ 0 1 : ℤ ) : Zmod N ) = 0
              ∧
              ( ( ↑ₘ γ 1 0 : ℤ ) : Zmod N ) = 0 ∧ ( ( ↑ₘ γ 1 1 : ℤ ) : Zmod N ) = 1
    :=
      by
        rw [ Gamma_mem' ]
          constructor
          · intro h simp [ ← SL_reduction_mod_hom_val N γ , h ]
          ·
            intro h
              ext
              rw [ SL_reduction_mod_hom_val N γ ]
              fin_cases i <;> fin_cases j
              all_goals simp_rw [ h ] ; rfl
#align Gamma_mem Gamma_mem

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `Gamma_normal [])
      (Command.declSig
       [(Term.explicitBinder "(" [`N] [":" (termℕ "ℕ")] [] ")")]
       (Term.typeSpec ":" (Term.app `Subgroup.Normal [(Term.app `gamma [`N])])))
      (Command.declValSimple
       ":="
       (Term.proj
        (NumberTheory.ModularForms.CongruenceSubgroups.«termSLMOD(_)» "SLMOD(" `N ")")
        "."
        `normal_ker)
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (NumberTheory.ModularForms.CongruenceSubgroups.«termSLMOD(_)» "SLMOD(" `N ")")
       "."
       `normal_ker)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (NumberTheory.ModularForms.CongruenceSubgroups.«termSLMOD(_)» "SLMOD(" `N ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.CongruenceSubgroups.«termSLMOD(_)»', expected 'NumberTheory.ModularForms.CongruenceSubgroups.termSLMOD(_)._@.NumberTheory.ModularForms.CongruenceSubgroups._hyg.879'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem Gamma_normal ( N : ℕ ) : Subgroup.Normal gamma N := SLMOD( N ) . normal_ker
#align Gamma_normal Gamma_normal

theorem Gamma_one_top : gamma 1 = ⊤ := by
  ext
  simp
#align Gamma_one_top Gamma_one_top

theorem Gamma_zero_bot : gamma 0 = ⊥ := by
  ext
  simp only [Gamma_mem, coe_coe, coe_matrix_coe, Int.coe_castRingHom, map_apply, Int.cast_id,
    Subgroup.mem_bot]
  constructor
  · intro h
    ext
    fin_cases i <;> fin_cases j
    any_goals simp [h]
  · intro h
    simp [h]
#align Gamma_zero_bot Gamma_zero_bot

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The congruence subgroup of `SL(2, ℤ)` of matrices whose lower left-hand entry reduces to zero\nmodulo `N`. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `gamma0 [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`N] [":" (termℕ "ℕ")] [] ")")]
       [(Term.typeSpec
         ":"
         (Term.app
          `Subgroup
          [(NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»
            "SL("
            (num "2")
            ", "
            (termℤ "ℤ")
            ")")]))])
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `carrier
           []
           []
           ":="
           (Set.«term{_|_}»
            "{"
            (Std.ExtendedBinder.extBinder
             (Lean.binderIdent `g)
             [(group
               ":"
               (NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»
                "SL("
                (num "2")
                ", "
                (termℤ "ℤ")
                ")"))])
            "|"
            («term_=_»
             (Term.typeAscription
              "("
              (Term.typeAscription
               "("
               (Term.app
                (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `g)
                [(num "1") (num "0")])
               ":"
               [(termℤ "ℤ")]
               ")")
              ":"
              [(Term.app `Zmod [`N])]
              ")")
             "="
             (num "0"))
            "}"))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `one_mem'
           []
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])]))))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `mul_mem'
           []
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.intro "intro" [`a `b `ha `hb])
               []
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["[" [(Tactic.simpLemma [] [] `Set.mem_setOf_eq)] "]"]
                [])
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`h []]
                  []
                  ":="
                  (Term.proj
                   (Term.proj
                    (Term.proj
                     (Term.app
                      `Matrix.two_mul_expl
                      [(Term.proj `a "." (fieldIdx "1")) (Term.proj `b "." (fieldIdx "1"))])
                     "."
                     (fieldIdx "2"))
                    "."
                    (fieldIdx "2"))
                   "."
                   (fieldIdx "1")))))
               []
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `coe_coe)
                  ","
                  (Tactic.simpLemma [] [] `coe_matrix_coe)
                  ","
                  (Tactic.simpLemma [] [] `coe_mul)
                  ","
                  (Tactic.simpLemma [] [] `Int.coe_castRingHom)
                  ","
                  (Tactic.simpLemma [] [] `map_apply)
                  ","
                  (Tactic.simpLemma [] [] `Set.mem_setOf_eq)
                  ","
                  (Tactic.simpLemma [] [] `Subtype.val_eq_coe)
                  ","
                  (Tactic.simpLemma [] [] `mul_eq_mul)]
                 "]"]
                [(Tactic.location "at" (Tactic.locationWildcard "*"))])
               []
               (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") [])
               []
               (Tactic.simp
                "simp"
                []
                []
                []
                ["[" [(Tactic.simpLemma [] [] `ha) "," (Tactic.simpLemma [] [] `hb)] "]"]
                [])]))))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `inv_mem'
           []
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.intro "intro" [`a `ha])
               []
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `Set.mem_setOf_eq)
                  ","
                  (Tactic.simpLemma [] [] `Subtype.val_eq_coe)]
                 "]"]
                [])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `SL2_inv_expl [`a]))] "]")
                [])
               []
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `Subtype.val_eq_coe)
                  ","
                  (Tactic.simpLemma [] [] `cons_val_zero)
                  ","
                  (Tactic.simpLemma [] [] `cons_val_one)
                  ","
                  (Tactic.simpLemma [] [] `head_cons)
                  ","
                  (Tactic.simpLemma [] [] `coe_coe)
                  ","
                  (Tactic.simpLemma [] [] `coe_matrix_coe)
                  ","
                  (Tactic.simpLemma [] [] `coe_mk)
                  ","
                  (Tactic.simpLemma [] [] `Int.coe_castRingHom)
                  ","
                  (Tactic.simpLemma [] [] `map_apply)
                  ","
                  (Tactic.simpLemma [] [] `Int.cast_neg)
                  ","
                  (Tactic.simpLemma [] [] `neg_eq_zero)
                  ","
                  (Tactic.simpLemma [] [] `Set.mem_setOf_eq)]
                 "]"]
                [(Tactic.location "at" (Tactic.locationWildcard "*"))])
               []
               (Tactic.exact "exact" `ha)]))))))]
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intro "intro" [`a `ha])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `Set.mem_setOf_eq)
             ","
             (Tactic.simpLemma [] [] `Subtype.val_eq_coe)]
            "]"]
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `SL2_inv_expl [`a]))] "]")
           [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `Subtype.val_eq_coe)
             ","
             (Tactic.simpLemma [] [] `cons_val_zero)
             ","
             (Tactic.simpLemma [] [] `cons_val_one)
             ","
             (Tactic.simpLemma [] [] `head_cons)
             ","
             (Tactic.simpLemma [] [] `coe_coe)
             ","
             (Tactic.simpLemma [] [] `coe_matrix_coe)
             ","
             (Tactic.simpLemma [] [] `coe_mk)
             ","
             (Tactic.simpLemma [] [] `Int.coe_castRingHom)
             ","
             (Tactic.simpLemma [] [] `map_apply)
             ","
             (Tactic.simpLemma [] [] `Int.cast_neg)
             ","
             (Tactic.simpLemma [] [] `neg_eq_zero)
             ","
             (Tactic.simpLemma [] [] `Set.mem_setOf_eq)]
            "]"]
           [(Tactic.location "at" (Tactic.locationWildcard "*"))])
          []
          (Tactic.exact "exact" `ha)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `ha)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
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
        [(Tactic.simpLemma [] [] `Subtype.val_eq_coe)
         ","
         (Tactic.simpLemma [] [] `cons_val_zero)
         ","
         (Tactic.simpLemma [] [] `cons_val_one)
         ","
         (Tactic.simpLemma [] [] `head_cons)
         ","
         (Tactic.simpLemma [] [] `coe_coe)
         ","
         (Tactic.simpLemma [] [] `coe_matrix_coe)
         ","
         (Tactic.simpLemma [] [] `coe_mk)
         ","
         (Tactic.simpLemma [] [] `Int.coe_castRingHom)
         ","
         (Tactic.simpLemma [] [] `map_apply)
         ","
         (Tactic.simpLemma [] [] `Int.cast_neg)
         ","
         (Tactic.simpLemma [] [] `neg_eq_zero)
         ","
         (Tactic.simpLemma [] [] `Set.mem_setOf_eq)]
        "]"]
       [(Tactic.location "at" (Tactic.locationWildcard "*"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.mem_setOf_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `neg_eq_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.cast_neg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.coe_castRingHom
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_matrix_coe
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
      `head_cons
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cons_val_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `cons_val_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.val_eq_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `SL2_inv_expl [`a]))] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `SL2_inv_expl [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `SL2_inv_expl
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
        [(Tactic.simpLemma [] [] `Set.mem_setOf_eq)
         ","
         (Tactic.simpLemma [] [] `Subtype.val_eq_coe)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.val_eq_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.mem_setOf_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`a `ha])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intro "intro" [`a `b `ha `hb])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["[" [(Tactic.simpLemma [] [] `Set.mem_setOf_eq)] "]"]
           [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h []]
             []
             ":="
             (Term.proj
              (Term.proj
               (Term.proj
                (Term.app
                 `Matrix.two_mul_expl
                 [(Term.proj `a "." (fieldIdx "1")) (Term.proj `b "." (fieldIdx "1"))])
                "."
                (fieldIdx "2"))
               "."
               (fieldIdx "2"))
              "."
              (fieldIdx "1")))))
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `coe_coe)
             ","
             (Tactic.simpLemma [] [] `coe_matrix_coe)
             ","
             (Tactic.simpLemma [] [] `coe_mul)
             ","
             (Tactic.simpLemma [] [] `Int.coe_castRingHom)
             ","
             (Tactic.simpLemma [] [] `map_apply)
             ","
             (Tactic.simpLemma [] [] `Set.mem_setOf_eq)
             ","
             (Tactic.simpLemma [] [] `Subtype.val_eq_coe)
             ","
             (Tactic.simpLemma [] [] `mul_eq_mul)]
            "]"]
           [(Tactic.location "at" (Tactic.locationWildcard "*"))])
          []
          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") [])
          []
          (Tactic.simp
           "simp"
           []
           []
           []
           ["[" [(Tactic.simpLemma [] [] `ha) "," (Tactic.simpLemma [] [] `hb)] "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["[" [(Tactic.simpLemma [] [] `ha) "," (Tactic.simpLemma [] [] `hb)] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hb
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
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
         (Tactic.simpLemma [] [] `coe_matrix_coe)
         ","
         (Tactic.simpLemma [] [] `coe_mul)
         ","
         (Tactic.simpLemma [] [] `Int.coe_castRingHom)
         ","
         (Tactic.simpLemma [] [] `map_apply)
         ","
         (Tactic.simpLemma [] [] `Set.mem_setOf_eq)
         ","
         (Tactic.simpLemma [] [] `Subtype.val_eq_coe)
         ","
         (Tactic.simpLemma [] [] `mul_eq_mul)]
        "]"]
       [(Tactic.location "at" (Tactic.locationWildcard "*"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_eq_mul
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
      `Set.mem_setOf_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.coe_castRingHom
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_matrix_coe
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
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`h []]
         []
         ":="
         (Term.proj
          (Term.proj
           (Term.proj
            (Term.app
             `Matrix.two_mul_expl
             [(Term.proj `a "." (fieldIdx "1")) (Term.proj `b "." (fieldIdx "1"))])
            "."
            (fieldIdx "2"))
           "."
           (fieldIdx "2"))
          "."
          (fieldIdx "1")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.proj
        (Term.proj
         (Term.app
          `Matrix.two_mul_expl
          [(Term.proj `a "." (fieldIdx "1")) (Term.proj `b "." (fieldIdx "1"))])
         "."
         (fieldIdx "2"))
        "."
        (fieldIdx "2"))
       "."
       (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.proj
        (Term.app
         `Matrix.two_mul_expl
         [(Term.proj `a "." (fieldIdx "1")) (Term.proj `b "." (fieldIdx "1"))])
        "."
        (fieldIdx "2"))
       "."
       (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.app
        `Matrix.two_mul_expl
        [(Term.proj `a "." (fieldIdx "1")) (Term.proj `b "." (fieldIdx "1"))])
       "."
       (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `Matrix.two_mul_expl
       [(Term.proj `a "." (fieldIdx "1")) (Term.proj `b "." (fieldIdx "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `b "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `a "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Matrix.two_mul_expl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `Matrix.two_mul_expl
      [(Term.proj `a "." (fieldIdx "1")) (Term.proj `b "." (fieldIdx "1"))])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `Set.mem_setOf_eq)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.mem_setOf_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`a `b `ha `hb])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hb
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
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
      (Set.«term{_|_}»
       "{"
       (Std.ExtendedBinder.extBinder
        (Lean.binderIdent `g)
        [(group
          ":"
          (NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»
           "SL("
           (num "2")
           ", "
           (termℤ "ℤ")
           ")"))])
       "|"
       («term_=_»
        (Term.typeAscription
         "("
         (Term.typeAscription
          "("
          (Term.app
           (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `g)
           [(num "1") (num "0")])
          ":"
          [(termℤ "ℤ")]
          ")")
         ":"
         [(Term.app `Zmod [`N])]
         ")")
        "="
        (num "0"))
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.typeAscription
        "("
        (Term.typeAscription
         "("
         (Term.app
          (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `g)
          [(num "1") (num "0")])
         ":"
         [(termℤ "ℤ")]
         ")")
        ":"
        [(Term.app `Zmod [`N])]
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
       (Term.typeAscription
        "("
        (Term.app
         (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `g)
         [(num "1") (num "0")])
        ":"
        [(termℤ "ℤ")]
        ")")
       ":"
       [(Term.app `Zmod [`N])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Zmod [`N])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `N
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Zmod
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.app
        (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `g)
        [(num "1") (num "0")])
       ":"
       [(termℤ "ℤ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℤ "ℤ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `g)
       [(num "1") (num "0")])
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
      (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `g)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_»', expected 'NumberTheory.ModularForms.CongruenceSubgroups.term↑ₘ_._@.NumberTheory.ModularForms.CongruenceSubgroups._hyg.836'
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
    The congruence subgroup of `SL(2, ℤ)` of matrices whose lower left-hand entry reduces to zero
    modulo `N`. -/
  def
    gamma0
    ( N : ℕ ) : Subgroup SL( 2 , ℤ )
    where
      carrier := { g : SL( 2 , ℤ ) | ( ( ↑ₘ g 1 0 : ℤ ) : Zmod N ) = 0 }
        one_mem' := by simp
        mul_mem'
          :=
          by
            intro a b ha hb
              simp only [ Set.mem_setOf_eq ]
              have h := Matrix.two_mul_expl a . 1 b . 1 . 2 . 2 . 1
              simp
                only
                [
                  coe_coe
                    ,
                    coe_matrix_coe
                    ,
                    coe_mul
                    ,
                    Int.coe_castRingHom
                    ,
                    map_apply
                    ,
                    Set.mem_setOf_eq
                    ,
                    Subtype.val_eq_coe
                    ,
                    mul_eq_mul
                  ]
                at *
              rw [ h ]
              simp [ ha , hb ]
        inv_mem'
          :=
          by
            intro a ha
              simp only [ Set.mem_setOf_eq , Subtype.val_eq_coe ]
              rw [ SL2_inv_expl a ]
              simp
                only
                [
                  Subtype.val_eq_coe
                    ,
                    cons_val_zero
                    ,
                    cons_val_one
                    ,
                    head_cons
                    ,
                    coe_coe
                    ,
                    coe_matrix_coe
                    ,
                    coe_mk
                    ,
                    Int.coe_castRingHom
                    ,
                    map_apply
                    ,
                    Int.cast_neg
                    ,
                    neg_eq_zero
                    ,
                    Set.mem_setOf_eq
                  ]
                at *
              exact ha
#align Gamma0 gamma0

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
      (Command.declId `Gamma0_mem [])
      (Command.declSig
       [(Term.explicitBinder "(" [`N] [":" (termℕ "ℕ")] [] ")")
        (Term.explicitBinder
         "("
         [`A]
         [":"
          (NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»
           "SL("
           (num "2")
           ", "
           (termℤ "ℤ")
           ")")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_∈_» `A "∈" (Term.app `gamma0 [`N]))
         "↔"
         («term_=_»
          (Term.typeAscription
           "("
           (Term.typeAscription
            "("
            (Term.app
             (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
             [(num "1") (num "0")])
            ":"
            [(termℤ "ℤ")]
            ")")
           ":"
           [(Term.app `Zmod [`N])]
           ")")
          "="
          (num "0")))))
      (Command.declValSimple ":=" `Iff.rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Iff.rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_∈_» `A "∈" (Term.app `gamma0 [`N]))
       "↔"
       («term_=_»
        (Term.typeAscription
         "("
         (Term.typeAscription
          "("
          (Term.app
           (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
           [(num "1") (num "0")])
          ":"
          [(termℤ "ℤ")]
          ")")
         ":"
         [(Term.app `Zmod [`N])]
         ")")
        "="
        (num "0")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.typeAscription
        "("
        (Term.typeAscription
         "("
         (Term.app
          (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
          [(num "1") (num "0")])
         ":"
         [(termℤ "ℤ")]
         ")")
        ":"
        [(Term.app `Zmod [`N])]
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
       (Term.typeAscription
        "("
        (Term.app
         (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
         [(num "1") (num "0")])
        ":"
        [(termℤ "ℤ")]
        ")")
       ":"
       [(Term.app `Zmod [`N])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Zmod [`N])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `N
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Zmod
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.app
        (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
        [(num "1") (num "0")])
       ":"
       [(termℤ "ℤ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℤ "ℤ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
       [(num "1") (num "0")])
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
      (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_»', expected 'NumberTheory.ModularForms.CongruenceSubgroups.term↑ₘ_._@.NumberTheory.ModularForms.CongruenceSubgroups._hyg.836'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    Gamma0_mem
    ( N : ℕ ) ( A : SL( 2 , ℤ ) ) : A ∈ gamma0 N ↔ ( ( ↑ₘ A 1 0 : ℤ ) : Zmod N ) = 0
    := Iff.rfl
#align Gamma0_mem Gamma0_mem

theorem Gamma0_det (N : ℕ) (A : gamma0 N) : (A.1.1.det : Zmod N) = 1 := by simp [A.1.property]
#align Gamma0_det Gamma0_det

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The group homomorphism from `Gamma0` to `zmod N` given by mapping a matrix to its lower\nright-hand entry. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `gamma0Map [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`N] [":" (termℕ "ℕ")] [] ")")]
       [(Term.typeSpec
         ":"
         (Algebra.Hom.Group.«term_→*_» (Term.app `gamma0 [`N]) " →* " (Term.app `Zmod [`N])))])
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `toFun
           [`g]
           []
           ":="
           (Term.typeAscription
            "("
            (Term.typeAscription
             "("
             (Term.app
              (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `g)
              [(num "1") (num "1")])
             ":"
             [(termℤ "ℤ")]
             ")")
            ":"
            [(Term.app `Zmod [`N])]
            ")"))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `map_one'
           []
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])]))))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `map_mul'
           []
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.intro "intro" [`A `B])
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  []
                  []
                  ":="
                  (Term.proj
                   (Term.proj
                    (Term.proj
                     (Term.app
                      `two_mul_expl
                      [(Term.proj (Term.proj `A "." (fieldIdx "1")) "." (fieldIdx "1"))
                       (Term.proj (Term.proj `B "." (fieldIdx "1")) "." (fieldIdx "1"))])
                     "."
                     (fieldIdx "2"))
                    "."
                    (fieldIdx "2"))
                   "."
                   (fieldIdx "2")))))
               []
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `coe_coe)
                  ","
                  (Tactic.simpLemma [] [] `Subgroup.coe_mul)
                  ","
                  (Tactic.simpLemma [] [] `coe_matrix_coe)
                  ","
                  (Tactic.simpLemma [] [] `coe_mul)
                  ","
                  (Tactic.simpLemma [] [] `Int.coe_castRingHom)
                  ","
                  (Tactic.simpLemma [] [] `map_apply)
                  ","
                  (Tactic.simpLemma [] [] `Subtype.val_eq_coe)
                  ","
                  (Tactic.simpLemma [] [] `mul_eq_mul)]
                 "]"]
                [(Tactic.location "at" (Tactic.locationWildcard "*"))])
               []
               (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl (Term.haveIdDecl [`ha []] [] ":=" `A.property)))
               []
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `Int.cast_add)
                  ","
                  (Tactic.simpLemma [] [] `Int.cast_mul)
                  ","
                  (Tactic.simpLemma [] [] `add_left_eq_self)
                  ","
                  (Tactic.simpLemma [] [] `Subtype.val_eq_coe)
                  ","
                  (Tactic.simpLemma [] [] `Gamma0_mem)
                  ","
                  (Tactic.simpLemma [] [] `coe_coe)
                  ","
                  (Tactic.simpLemma [] [] `coe_matrix_coe)
                  ","
                  (Tactic.simpLemma [] [] `Int.coe_castRingHom)
                  ","
                  (Tactic.simpLemma [] [] `map_apply)]
                 "]"]
                [(Tactic.location "at" (Tactic.locationWildcard "*"))])
               []
               (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ha)] "]") [])
               []
               (Tactic.simp "simp" [] [] [] [] [])]))))))]
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intro "intro" [`A `B])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             []
             ":="
             (Term.proj
              (Term.proj
               (Term.proj
                (Term.app
                 `two_mul_expl
                 [(Term.proj (Term.proj `A "." (fieldIdx "1")) "." (fieldIdx "1"))
                  (Term.proj (Term.proj `B "." (fieldIdx "1")) "." (fieldIdx "1"))])
                "."
                (fieldIdx "2"))
               "."
               (fieldIdx "2"))
              "."
              (fieldIdx "2")))))
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `coe_coe)
             ","
             (Tactic.simpLemma [] [] `Subgroup.coe_mul)
             ","
             (Tactic.simpLemma [] [] `coe_matrix_coe)
             ","
             (Tactic.simpLemma [] [] `coe_mul)
             ","
             (Tactic.simpLemma [] [] `Int.coe_castRingHom)
             ","
             (Tactic.simpLemma [] [] `map_apply)
             ","
             (Tactic.simpLemma [] [] `Subtype.val_eq_coe)
             ","
             (Tactic.simpLemma [] [] `mul_eq_mul)]
            "]"]
           [(Tactic.location "at" (Tactic.locationWildcard "*"))])
          []
          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
          []
          (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [`ha []] [] ":=" `A.property)))
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `Int.cast_add)
             ","
             (Tactic.simpLemma [] [] `Int.cast_mul)
             ","
             (Tactic.simpLemma [] [] `add_left_eq_self)
             ","
             (Tactic.simpLemma [] [] `Subtype.val_eq_coe)
             ","
             (Tactic.simpLemma [] [] `Gamma0_mem)
             ","
             (Tactic.simpLemma [] [] `coe_coe)
             ","
             (Tactic.simpLemma [] [] `coe_matrix_coe)
             ","
             (Tactic.simpLemma [] [] `Int.coe_castRingHom)
             ","
             (Tactic.simpLemma [] [] `map_apply)]
            "]"]
           [(Tactic.location "at" (Tactic.locationWildcard "*"))])
          []
          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ha)] "]") [])
          []
          (Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ha)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
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
        [(Tactic.simpLemma [] [] `Int.cast_add)
         ","
         (Tactic.simpLemma [] [] `Int.cast_mul)
         ","
         (Tactic.simpLemma [] [] `add_left_eq_self)
         ","
         (Tactic.simpLemma [] [] `Subtype.val_eq_coe)
         ","
         (Tactic.simpLemma [] [] `Gamma0_mem)
         ","
         (Tactic.simpLemma [] [] `coe_coe)
         ","
         (Tactic.simpLemma [] [] `coe_matrix_coe)
         ","
         (Tactic.simpLemma [] [] `Int.coe_castRingHom)
         ","
         (Tactic.simpLemma [] [] `map_apply)]
        "]"]
       [(Tactic.location "at" (Tactic.locationWildcard "*"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.coe_castRingHom
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_matrix_coe
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
      `Gamma0_mem
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
      `add_left_eq_self
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.cast_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.cast_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [`ha []] [] ":=" `A.property)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A.property
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
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
         (Tactic.simpLemma [] [] `Subgroup.coe_mul)
         ","
         (Tactic.simpLemma [] [] `coe_matrix_coe)
         ","
         (Tactic.simpLemma [] [] `coe_mul)
         ","
         (Tactic.simpLemma [] [] `Int.coe_castRingHom)
         ","
         (Tactic.simpLemma [] [] `map_apply)
         ","
         (Tactic.simpLemma [] [] `Subtype.val_eq_coe)
         ","
         (Tactic.simpLemma [] [] `mul_eq_mul)]
        "]"]
       [(Tactic.location "at" (Tactic.locationWildcard "*"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_eq_mul
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
      `map_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.coe_castRingHom
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_matrix_coe
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         []
         ":="
         (Term.proj
          (Term.proj
           (Term.proj
            (Term.app
             `two_mul_expl
             [(Term.proj (Term.proj `A "." (fieldIdx "1")) "." (fieldIdx "1"))
              (Term.proj (Term.proj `B "." (fieldIdx "1")) "." (fieldIdx "1"))])
            "."
            (fieldIdx "2"))
           "."
           (fieldIdx "2"))
          "."
          (fieldIdx "2")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.proj
        (Term.proj
         (Term.app
          `two_mul_expl
          [(Term.proj (Term.proj `A "." (fieldIdx "1")) "." (fieldIdx "1"))
           (Term.proj (Term.proj `B "." (fieldIdx "1")) "." (fieldIdx "1"))])
         "."
         (fieldIdx "2"))
        "."
        (fieldIdx "2"))
       "."
       (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.proj
        (Term.app
         `two_mul_expl
         [(Term.proj (Term.proj `A "." (fieldIdx "1")) "." (fieldIdx "1"))
          (Term.proj (Term.proj `B "." (fieldIdx "1")) "." (fieldIdx "1"))])
        "."
        (fieldIdx "2"))
       "."
       (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.app
        `two_mul_expl
        [(Term.proj (Term.proj `A "." (fieldIdx "1")) "." (fieldIdx "1"))
         (Term.proj (Term.proj `B "." (fieldIdx "1")) "." (fieldIdx "1"))])
       "."
       (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `two_mul_expl
       [(Term.proj (Term.proj `A "." (fieldIdx "1")) "." (fieldIdx "1"))
        (Term.proj (Term.proj `B "." (fieldIdx "1")) "." (fieldIdx "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `B "." (fieldIdx "1")) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `B "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `B
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.proj `A "." (fieldIdx "1")) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `A "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `A
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `two_mul_expl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `two_mul_expl
      [(Term.proj (Term.proj `A "." (fieldIdx "1")) "." (fieldIdx "1"))
       (Term.proj (Term.proj `B "." (fieldIdx "1")) "." (fieldIdx "1"))])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`A `B])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `B
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
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
      (Term.typeAscription
       "("
       (Term.typeAscription
        "("
        (Term.app
         (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `g)
         [(num "1") (num "1")])
        ":"
        [(termℤ "ℤ")]
        ")")
       ":"
       [(Term.app `Zmod [`N])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Zmod [`N])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `N
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Zmod
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.app
        (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `g)
        [(num "1") (num "1")])
       ":"
       [(termℤ "ℤ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℤ "ℤ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `g)
       [(num "1") (num "1")])
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
      (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `g)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_»', expected 'NumberTheory.ModularForms.CongruenceSubgroups.term↑ₘ_._@.NumberTheory.ModularForms.CongruenceSubgroups._hyg.836'
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
    The group homomorphism from `Gamma0` to `zmod N` given by mapping a matrix to its lower
    right-hand entry. -/
  def
    gamma0Map
    ( N : ℕ ) : gamma0 N →* Zmod N
    where
      toFun g := ( ( ↑ₘ g 1 1 : ℤ ) : Zmod N )
        map_one' := by simp
        map_mul'
          :=
          by
            intro A B
              have := two_mul_expl A . 1 . 1 B . 1 . 1 . 2 . 2 . 2
              simp
                only
                [
                  coe_coe
                    ,
                    Subgroup.coe_mul
                    ,
                    coe_matrix_coe
                    ,
                    coe_mul
                    ,
                    Int.coe_castRingHom
                    ,
                    map_apply
                    ,
                    Subtype.val_eq_coe
                    ,
                    mul_eq_mul
                  ]
                at *
              rw [ this ]
              have ha := A.property
              simp
                only
                [
                  Int.cast_add
                    ,
                    Int.cast_mul
                    ,
                    add_left_eq_self
                    ,
                    Subtype.val_eq_coe
                    ,
                    Gamma0_mem
                    ,
                    coe_coe
                    ,
                    coe_matrix_coe
                    ,
                    Int.coe_castRingHom
                    ,
                    map_apply
                  ]
                at *
              rw [ ha ]
              simp
#align Gamma_0_map gamma0Map

/-- The congruence subgroup `Gamma1` (as a subgroup of `Gamma0`) of matrices whose bottom
row is congruent to `(0,1)` modulo `N`.-/
def gamma1' (N : ℕ) : Subgroup (gamma0 N) :=
  (gamma0Map N).ker
#align Gamma1' gamma1'

@[simp]
theorem Gamma1_mem' (N : ℕ) (γ : gamma0 N) : γ ∈ gamma1' N ↔ (gamma0Map N) γ = 1 :=
  Iff.rfl
#align Gamma1_mem' Gamma1_mem'

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `Gamma1_to_Gamma0_mem [])
      (Command.declSig
       [(Term.explicitBinder "(" [`N] [":" (termℕ "ℕ")] [] ")")
        (Term.explicitBinder "(" [`A] [":" (Term.app `gamma0 [`N])] [] ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_∈_» `A "∈" (Term.app `gamma1' [`N]))
         "↔"
         («term_∧_»
          («term_=_»
           (Term.typeAscription
            "("
            (Term.typeAscription
             "("
             (Term.app
              (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
              [(num "0") (num "0")])
             ":"
             [(termℤ "ℤ")]
             ")")
            ":"
            [(Term.app `Zmod [`N])]
            ")")
           "="
           (num "1"))
          "∧"
          («term_∧_»
           («term_=_»
            (Term.typeAscription
             "("
             (Term.typeAscription
              "("
              (Term.app
               (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
               [(num "1") (num "1")])
              ":"
              [(termℤ "ℤ")]
              ")")
             ":"
             [(Term.app `Zmod [`N])]
             ")")
            "="
            (num "1"))
           "∧"
           («term_=_»
            (Term.typeAscription
             "("
             (Term.typeAscription
              "("
              (Term.app
               (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
               [(num "1") (num "0")])
              ":"
              [(termℤ "ℤ")]
              ")")
             ":"
             [(Term.app `Zmod [`N])]
             ")")
            "="
            (num "0")))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.constructor "constructor")
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.intro "intro" [`ha])
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl (Term.haveIdDecl [`hA []] [] ":=" `A.property)))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Gamma0_mem)] "]")
              [(Tactic.location "at" (Tactic.locationHyp [`hA] []))])
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl (Term.haveIdDecl [`adet []] [] ":=" (Term.app `Gamma0_det [`N `A]))))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Matrix.det_fin_two)] "]")
              [(Tactic.location "at" (Tactic.locationHyp [`adet] []))])
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `gamma0Map)
                ","
                (Tactic.simpLemma [] [] `coe_coe)
                ","
                (Tactic.simpLemma [] [] `coe_matrix_coe)
                ","
                (Tactic.simpLemma [] [] `Int.coe_castRingHom)
                ","
                (Tactic.simpLemma [] [] `map_apply)
                ","
                (Tactic.simpLemma [] [] `Gamma1_mem')
                ","
                (Tactic.simpLemma [] [] `MonoidHom.coe_mk)
                ","
                (Tactic.simpLemma [] [] `Subtype.val_eq_coe)
                ","
                (Tactic.simpLemma [] [] `Int.cast_sub)
                ","
                (Tactic.simpLemma [] [] `Int.cast_mul)]
               "]"]
              [(Tactic.location "at" (Tactic.locationWildcard "*"))])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hA) "," (Tactic.rwRule [] `ha)] "]")
              [(Tactic.location "at" (Tactic.locationHyp [`adet] []))])
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `mul_one)
                ","
                (Tactic.simpLemma [] [] `mul_zero)
                ","
                (Tactic.simpLemma [] [] `sub_zero)]
               "]"]
              [(Tactic.location "at" (Tactic.locationHyp [`adet] []))])
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `adet)
                ","
                (Tactic.simpLemma [] [] `hA)
                ","
                (Tactic.simpLemma [] [] `ha)
                ","
                (Tactic.simpLemma [] [] `eq_self_iff_true)
                ","
                (Tactic.simpLemma [] [] `and_self_iff)]
               "]"]
              [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.intro "intro" [`ha])
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `Gamma1_mem')
                ","
                (Tactic.simpLemma [] [] `gamma0Map)
                ","
                (Tactic.simpLemma [] [] `MonoidHom.coe_mk)
                ","
                (Tactic.simpLemma [] [] `coe_coe)
                ","
                (Tactic.simpLemma [] [] `coe_matrix_coe)
                ","
                (Tactic.simpLemma [] [] `Int.coe_castRingHom)
                ","
                (Tactic.simpLemma [] [] `map_apply)]
               "]"]
              [])
             []
             (Tactic.exact
              "exact"
              (Term.proj (Term.proj `ha "." (fieldIdx "2")) "." (fieldIdx "1")))])])))
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
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro "intro" [`ha])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl (Term.haveIdDecl [`hA []] [] ":=" `A.property)))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Gamma0_mem)] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`hA] []))])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl (Term.haveIdDecl [`adet []] [] ":=" (Term.app `Gamma0_det [`N `A]))))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Matrix.det_fin_two)] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`adet] []))])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `gamma0Map)
               ","
               (Tactic.simpLemma [] [] `coe_coe)
               ","
               (Tactic.simpLemma [] [] `coe_matrix_coe)
               ","
               (Tactic.simpLemma [] [] `Int.coe_castRingHom)
               ","
               (Tactic.simpLemma [] [] `map_apply)
               ","
               (Tactic.simpLemma [] [] `Gamma1_mem')
               ","
               (Tactic.simpLemma [] [] `MonoidHom.coe_mk)
               ","
               (Tactic.simpLemma [] [] `Subtype.val_eq_coe)
               ","
               (Tactic.simpLemma [] [] `Int.cast_sub)
               ","
               (Tactic.simpLemma [] [] `Int.cast_mul)]
              "]"]
             [(Tactic.location "at" (Tactic.locationWildcard "*"))])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hA) "," (Tactic.rwRule [] `ha)] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`adet] []))])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `mul_one)
               ","
               (Tactic.simpLemma [] [] `mul_zero)
               ","
               (Tactic.simpLemma [] [] `sub_zero)]
              "]"]
             [(Tactic.location "at" (Tactic.locationHyp [`adet] []))])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `adet)
               ","
               (Tactic.simpLemma [] [] `hA)
               ","
               (Tactic.simpLemma [] [] `ha)
               ","
               (Tactic.simpLemma [] [] `eq_self_iff_true)
               ","
               (Tactic.simpLemma [] [] `and_self_iff)]
              "]"]
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro "intro" [`ha])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `Gamma1_mem')
               ","
               (Tactic.simpLemma [] [] `gamma0Map)
               ","
               (Tactic.simpLemma [] [] `MonoidHom.coe_mk)
               ","
               (Tactic.simpLemma [] [] `coe_coe)
               ","
               (Tactic.simpLemma [] [] `coe_matrix_coe)
               ","
               (Tactic.simpLemma [] [] `Int.coe_castRingHom)
               ","
               (Tactic.simpLemma [] [] `map_apply)]
              "]"]
             [])
            []
            (Tactic.exact
             "exact"
             (Term.proj (Term.proj `ha "." (fieldIdx "2")) "." (fieldIdx "1")))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.intro "intro" [`ha])
        []
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `Gamma1_mem')
           ","
           (Tactic.simpLemma [] [] `gamma0Map)
           ","
           (Tactic.simpLemma [] [] `MonoidHom.coe_mk)
           ","
           (Tactic.simpLemma [] [] `coe_coe)
           ","
           (Tactic.simpLemma [] [] `coe_matrix_coe)
           ","
           (Tactic.simpLemma [] [] `Int.coe_castRingHom)
           ","
           (Tactic.simpLemma [] [] `map_apply)]
          "]"]
         [])
        []
        (Tactic.exact "exact" (Term.proj (Term.proj `ha "." (fieldIdx "2")) "." (fieldIdx "1")))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.proj (Term.proj `ha "." (fieldIdx "2")) "." (fieldIdx "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `ha "." (fieldIdx "2")) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `ha "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
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
        [(Tactic.simpLemma [] [] `Gamma1_mem')
         ","
         (Tactic.simpLemma [] [] `gamma0Map)
         ","
         (Tactic.simpLemma [] [] `MonoidHom.coe_mk)
         ","
         (Tactic.simpLemma [] [] `coe_coe)
         ","
         (Tactic.simpLemma [] [] `coe_matrix_coe)
         ","
         (Tactic.simpLemma [] [] `Int.coe_castRingHom)
         ","
         (Tactic.simpLemma [] [] `map_apply)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.coe_castRingHom
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_matrix_coe
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
      `MonoidHom.coe_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `gamma0Map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Gamma1_mem'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`ha])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.intro "intro" [`ha])
        []
        (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [`hA []] [] ":=" `A.property)))
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Gamma0_mem)] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`hA] []))])
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl (Term.haveIdDecl [`adet []] [] ":=" (Term.app `Gamma0_det [`N `A]))))
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Matrix.det_fin_two)] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`adet] []))])
        []
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `gamma0Map)
           ","
           (Tactic.simpLemma [] [] `coe_coe)
           ","
           (Tactic.simpLemma [] [] `coe_matrix_coe)
           ","
           (Tactic.simpLemma [] [] `Int.coe_castRingHom)
           ","
           (Tactic.simpLemma [] [] `map_apply)
           ","
           (Tactic.simpLemma [] [] `Gamma1_mem')
           ","
           (Tactic.simpLemma [] [] `MonoidHom.coe_mk)
           ","
           (Tactic.simpLemma [] [] `Subtype.val_eq_coe)
           ","
           (Tactic.simpLemma [] [] `Int.cast_sub)
           ","
           (Tactic.simpLemma [] [] `Int.cast_mul)]
          "]"]
         [(Tactic.location "at" (Tactic.locationWildcard "*"))])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hA) "," (Tactic.rwRule [] `ha)] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`adet] []))])
        []
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `mul_one)
           ","
           (Tactic.simpLemma [] [] `mul_zero)
           ","
           (Tactic.simpLemma [] [] `sub_zero)]
          "]"]
         [(Tactic.location "at" (Tactic.locationHyp [`adet] []))])
        []
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `adet)
           ","
           (Tactic.simpLemma [] [] `hA)
           ","
           (Tactic.simpLemma [] [] `ha)
           ","
           (Tactic.simpLemma [] [] `eq_self_iff_true)
           ","
           (Tactic.simpLemma [] [] `and_self_iff)]
          "]"]
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `adet)
         ","
         (Tactic.simpLemma [] [] `hA)
         ","
         (Tactic.simpLemma [] [] `ha)
         ","
         (Tactic.simpLemma [] [] `eq_self_iff_true)
         ","
         (Tactic.simpLemma [] [] `and_self_iff)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `and_self_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq_self_iff_true
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hA
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `adet
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
        [(Tactic.simpLemma [] [] `mul_one)
         ","
         (Tactic.simpLemma [] [] `mul_zero)
         ","
         (Tactic.simpLemma [] [] `sub_zero)]
        "]"]
       [(Tactic.location "at" (Tactic.locationHyp [`adet] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `adet
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
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
      `mul_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hA) "," (Tactic.rwRule [] `ha)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`adet] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `adet
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hA
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
        [(Tactic.simpLemma [] [] `gamma0Map)
         ","
         (Tactic.simpLemma [] [] `coe_coe)
         ","
         (Tactic.simpLemma [] [] `coe_matrix_coe)
         ","
         (Tactic.simpLemma [] [] `Int.coe_castRingHom)
         ","
         (Tactic.simpLemma [] [] `map_apply)
         ","
         (Tactic.simpLemma [] [] `Gamma1_mem')
         ","
         (Tactic.simpLemma [] [] `MonoidHom.coe_mk)
         ","
         (Tactic.simpLemma [] [] `Subtype.val_eq_coe)
         ","
         (Tactic.simpLemma [] [] `Int.cast_sub)
         ","
         (Tactic.simpLemma [] [] `Int.cast_mul)]
        "]"]
       [(Tactic.location "at" (Tactic.locationWildcard "*"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.cast_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.cast_sub
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
      `MonoidHom.coe_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Gamma1_mem'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.coe_castRingHom
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_matrix_coe
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
      `gamma0Map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Matrix.det_fin_two)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`adet] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `adet
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Matrix.det_fin_two
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl (Term.haveIdDecl [`adet []] [] ":=" (Term.app `Gamma0_det [`N `A]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Gamma0_det [`N `A])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `N
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Gamma0_det
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Gamma0_mem)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`hA] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hA
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Gamma0_mem
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [`hA []] [] ":=" `A.property)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A.property
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`ha])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.constructor "constructor")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_∈_» `A "∈" (Term.app `gamma1' [`N]))
       "↔"
       («term_∧_»
        («term_=_»
         (Term.typeAscription
          "("
          (Term.typeAscription
           "("
           (Term.app
            (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
            [(num "0") (num "0")])
           ":"
           [(termℤ "ℤ")]
           ")")
          ":"
          [(Term.app `Zmod [`N])]
          ")")
         "="
         (num "1"))
        "∧"
        («term_∧_»
         («term_=_»
          (Term.typeAscription
           "("
           (Term.typeAscription
            "("
            (Term.app
             (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
             [(num "1") (num "1")])
            ":"
            [(termℤ "ℤ")]
            ")")
           ":"
           [(Term.app `Zmod [`N])]
           ")")
          "="
          (num "1"))
         "∧"
         («term_=_»
          (Term.typeAscription
           "("
           (Term.typeAscription
            "("
            (Term.app
             (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
             [(num "1") (num "0")])
            ":"
            [(termℤ "ℤ")]
            ")")
           ":"
           [(Term.app `Zmod [`N])]
           ")")
          "="
          (num "0")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∧_»
       («term_=_»
        (Term.typeAscription
         "("
         (Term.typeAscription
          "("
          (Term.app
           (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
           [(num "0") (num "0")])
          ":"
          [(termℤ "ℤ")]
          ")")
         ":"
         [(Term.app `Zmod [`N])]
         ")")
        "="
        (num "1"))
       "∧"
       («term_∧_»
        («term_=_»
         (Term.typeAscription
          "("
          (Term.typeAscription
           "("
           (Term.app
            (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
            [(num "1") (num "1")])
           ":"
           [(termℤ "ℤ")]
           ")")
          ":"
          [(Term.app `Zmod [`N])]
          ")")
         "="
         (num "1"))
        "∧"
        («term_=_»
         (Term.typeAscription
          "("
          (Term.typeAscription
           "("
           (Term.app
            (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
            [(num "1") (num "0")])
           ":"
           [(termℤ "ℤ")]
           ")")
          ":"
          [(Term.app `Zmod [`N])]
          ")")
         "="
         (num "0"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∧_»
       («term_=_»
        (Term.typeAscription
         "("
         (Term.typeAscription
          "("
          (Term.app
           (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
           [(num "1") (num "1")])
          ":"
          [(termℤ "ℤ")]
          ")")
         ":"
         [(Term.app `Zmod [`N])]
         ")")
        "="
        (num "1"))
       "∧"
       («term_=_»
        (Term.typeAscription
         "("
         (Term.typeAscription
          "("
          (Term.app
           (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
           [(num "1") (num "0")])
          ":"
          [(termℤ "ℤ")]
          ")")
         ":"
         [(Term.app `Zmod [`N])]
         ")")
        "="
        (num "0")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.typeAscription
        "("
        (Term.typeAscription
         "("
         (Term.app
          (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
          [(num "1") (num "0")])
         ":"
         [(termℤ "ℤ")]
         ")")
        ":"
        [(Term.app `Zmod [`N])]
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
       (Term.typeAscription
        "("
        (Term.app
         (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
         [(num "1") (num "0")])
        ":"
        [(termℤ "ℤ")]
        ")")
       ":"
       [(Term.app `Zmod [`N])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Zmod [`N])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `N
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Zmod
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.app
        (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
        [(num "1") (num "0")])
       ":"
       [(termℤ "ℤ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℤ "ℤ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
       [(num "1") (num "0")])
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
      (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_»', expected 'NumberTheory.ModularForms.CongruenceSubgroups.term↑ₘ_._@.NumberTheory.ModularForms.CongruenceSubgroups._hyg.836'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  Gamma1_to_Gamma0_mem
  ( N : ℕ ) ( A : gamma0 N )
    :
      A ∈ gamma1' N
        ↔
        ( ( ↑ₘ A 0 0 : ℤ ) : Zmod N ) = 1
          ∧
          ( ( ↑ₘ A 1 1 : ℤ ) : Zmod N ) = 1 ∧ ( ( ↑ₘ A 1 0 : ℤ ) : Zmod N ) = 0
  :=
    by
      constructor
        ·
          intro ha
            have hA := A.property
            rw [ Gamma0_mem ] at hA
            have adet := Gamma0_det N A
            rw [ Matrix.det_fin_two ] at adet
            simp
              only
              [
                gamma0Map
                  ,
                  coe_coe
                  ,
                  coe_matrix_coe
                  ,
                  Int.coe_castRingHom
                  ,
                  map_apply
                  ,
                  Gamma1_mem'
                  ,
                  MonoidHom.coe_mk
                  ,
                  Subtype.val_eq_coe
                  ,
                  Int.cast_sub
                  ,
                  Int.cast_mul
                ]
              at *
            rw [ hA , ha ] at adet
            simp only [ mul_one , mul_zero , sub_zero ] at adet
            simp only [ adet , hA , ha , eq_self_iff_true , and_self_iff ]
        ·
          intro ha
            simp
              only
              [
                Gamma1_mem'
                  ,
                  gamma0Map
                  ,
                  MonoidHom.coe_mk
                  ,
                  coe_coe
                  ,
                  coe_matrix_coe
                  ,
                  Int.coe_castRingHom
                  ,
                  map_apply
                ]
            exact ha . 2 . 1
#align Gamma1_to_Gamma0_mem Gamma1_to_Gamma0_mem

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The congruence subgroup `Gamma1` of `SL(2, ℤ)` consisting of matrices whose bottom\nrow is congruent to `(0,1)` modulo `N`. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `gamma1 [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`N] [":" (termℕ "ℕ")] [] ")")]
       [(Term.typeSpec
         ":"
         (Term.app
          `Subgroup
          [(NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»
            "SL("
            (num "2")
            ", "
            (termℤ "ℤ")
            ")")]))])
      (Command.declValSimple
       ":="
       (Term.app
        `Subgroup.map
        [(Term.app
          (Term.proj (Term.proj (Term.app `gamma0 [`N]) "." `Subtype) "." `comp)
          [(Term.proj (Term.app `gamma1' [`N]) "." `Subtype)])
         (Order.BoundedOrder.«term⊤» "⊤")])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Subgroup.map
       [(Term.app
         (Term.proj (Term.proj (Term.app `gamma0 [`N]) "." `Subtype) "." `comp)
         [(Term.proj (Term.app `gamma1' [`N]) "." `Subtype)])
        (Order.BoundedOrder.«term⊤» "⊤")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BoundedOrder.«term⊤»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BoundedOrder.«term⊤»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.BoundedOrder.«term⊤» "⊤")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app
       (Term.proj (Term.proj (Term.app `gamma0 [`N]) "." `Subtype) "." `comp)
       [(Term.proj (Term.app `gamma1' [`N]) "." `Subtype)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `gamma1' [`N]) "." `Subtype)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `gamma1' [`N])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `N
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `gamma1'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `gamma1' [`N]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj (Term.app `gamma0 [`N]) "." `Subtype) "." `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app `gamma0 [`N]) "." `Subtype)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `gamma0 [`N])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `N
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `gamma0
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `gamma0 [`N]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.proj (Term.paren "(" (Term.app `gamma0 [`N]) ")") "." `Subtype) "." `comp)
      [(Term.proj (Term.paren "(" (Term.app `gamma1' [`N]) ")") "." `Subtype)])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Subgroup.map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Subgroup
       [(NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»
         "SL("
         (num "2")
         ", "
         (termℤ "ℤ")
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»
       "SL("
       (num "2")
       ", "
       (termℤ "ℤ")
       ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»', expected 'NumberTheory.ModularForms.CongruenceSubgroups.termSL(_,_)._@.NumberTheory.ModularForms.CongruenceSubgroups._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The congruence subgroup `Gamma1` of `SL(2, ℤ)` consisting of matrices whose bottom
    row is congruent to `(0,1)` modulo `N`. -/
  def
    gamma1
    ( N : ℕ ) : Subgroup SL( 2 , ℤ )
    := Subgroup.map gamma0 N . Subtype . comp gamma1' N . Subtype ⊤
#align Gamma1 gamma1

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
      (Command.declId `Gamma1_mem [])
      (Command.declSig
       [(Term.explicitBinder "(" [`N] [":" (termℕ "ℕ")] [] ")")
        (Term.explicitBinder
         "("
         [`A]
         [":"
          (NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»
           "SL("
           (num "2")
           ", "
           (termℤ "ℤ")
           ")")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_∈_» `A "∈" (Term.app `gamma1 [`N]))
         "↔"
         («term_∧_»
          («term_=_»
           (Term.typeAscription
            "("
            (Term.typeAscription
             "("
             (Term.app
              (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
              [(num "0") (num "0")])
             ":"
             [(termℤ "ℤ")]
             ")")
            ":"
            [(Term.app `Zmod [`N])]
            ")")
           "="
           (num "1"))
          "∧"
          («term_∧_»
           («term_=_»
            (Term.typeAscription
             "("
             (Term.typeAscription
              "("
              (Term.app
               (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
               [(num "1") (num "1")])
              ":"
              [(termℤ "ℤ")]
              ")")
             ":"
             [(Term.app `Zmod [`N])]
             ")")
            "="
            (num "1"))
           "∧"
           («term_=_»
            (Term.typeAscription
             "("
             (Term.typeAscription
              "("
              (Term.app
               (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
               [(num "1") (num "0")])
              ":"
              [(termℤ "ℤ")]
              ")")
             ":"
             [(Term.app `Zmod [`N])]
             ")")
            "="
            (num "0")))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.constructor "constructor")
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.intro "intro" [`ha])
             []
             (Mathlib.Tactic.tacticSimp_rw__
              "simp_rw"
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `gamma1) "," (Tactic.rwRule [] `Subgroup.mem_map)]
               "]")
              [(Tactic.location "at" (Tactic.locationHyp [`ha] []))])
             []
             (Tactic.simp "simp" [] [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`ha] []))])
             []
             (Std.Tactic.obtain
              "obtain"
              [(Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                         [])]
                       "⟩")])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hxx)])
                    [])]
                  "⟩")])]
              []
              [":=" [`ha]])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Gamma1_to_Gamma0_mem)] "]")
              [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hxx)] "]")
              [])
             []
             (convert "convert" [] `hx [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.intro "intro" [`ha])
             []
             (Mathlib.Tactic.tacticSimp_rw__
              "simp_rw"
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `gamma1) "," (Tactic.rwRule [] `Subgroup.mem_map)]
               "]")
              [])
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`hA []]
                [(Term.typeSpec ":" («term_∈_» `A "∈" (Term.app `gamma0 [`N])))]
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
                     ["["
                      [(Tactic.simpLemma [] [] `ha.right.right)
                       ","
                       (Tactic.simpLemma [] [] `Gamma0_mem)
                       ","
                       (Tactic.simpLemma [] [] `Subtype.val_eq_coe)]
                      "]"]
                     [])]))))))
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`HA []]
                [(Term.typeSpec
                  ":"
                  («term_∈_»
                   (Term.typeAscription
                    "("
                    (Term.anonymousCtor "⟨" [`A "," `hA] "⟩")
                    ":"
                    [(Term.app `gamma0 [`N])]
                    ")")
                   "∈"
                   (Term.app `gamma1' [`N])))]
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
                      [(Tactic.simpLemma [] [] `Gamma1_to_Gamma0_mem)
                       ","
                       (Tactic.simpLemma [] [] `Subgroup.coe_mk)
                       ","
                       (Tactic.simpLemma [] [] `coe_coe)
                       ","
                       (Tactic.simpLemma [] [] `coe_matrix_coe)
                       ","
                       (Tactic.simpLemma [] [] `Int.coe_castRingHom)
                       ","
                       (Tactic.simpLemma [] [] `map_apply)]
                      "]"]
                     [])
                    []
                    (Tactic.exact "exact" `ha)]))))))
             []
             (Tactic.refine'
              "refine'"
              (Term.anonymousCtor
               "⟨"
               [(Term.typeAscription
                 "("
                 (Term.anonymousCtor
                  "⟨"
                  [(Term.typeAscription
                    "("
                    (Term.anonymousCtor "⟨" [`A "," `hA] "⟩")
                    ":"
                    [(Term.app `gamma0 [`N])]
                    ")")
                   ","
                   `HA]
                  "⟩")
                 ":"
                 [(Term.typeAscription
                   "("
                   (Term.app `gamma1' [`N])
                   ":"
                   [(Term.app `Subgroup [(Term.app `gamma0 [`N])])]
                   ")")]
                 ")")
                ","
                (Term.hole "_")]
               "⟩"))
             []
             (Tactic.simp "simp" [] [] [] [] [])])])))
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
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro "intro" [`ha])
            []
            (Mathlib.Tactic.tacticSimp_rw__
             "simp_rw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `gamma1) "," (Tactic.rwRule [] `Subgroup.mem_map)]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`ha] []))])
            []
            (Tactic.simp "simp" [] [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`ha] []))])
            []
            (Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                        [])]
                      "⟩")])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hxx)])
                   [])]
                 "⟩")])]
             []
             [":=" [`ha]])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Gamma1_to_Gamma0_mem)] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hxx)] "]")
             [])
            []
            (convert "convert" [] `hx [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro "intro" [`ha])
            []
            (Mathlib.Tactic.tacticSimp_rw__
             "simp_rw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `gamma1) "," (Tactic.rwRule [] `Subgroup.mem_map)]
              "]")
             [])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`hA []]
               [(Term.typeSpec ":" («term_∈_» `A "∈" (Term.app `gamma0 [`N])))]
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
                    ["["
                     [(Tactic.simpLemma [] [] `ha.right.right)
                      ","
                      (Tactic.simpLemma [] [] `Gamma0_mem)
                      ","
                      (Tactic.simpLemma [] [] `Subtype.val_eq_coe)]
                     "]"]
                    [])]))))))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`HA []]
               [(Term.typeSpec
                 ":"
                 («term_∈_»
                  (Term.typeAscription
                   "("
                   (Term.anonymousCtor "⟨" [`A "," `hA] "⟩")
                   ":"
                   [(Term.app `gamma0 [`N])]
                   ")")
                  "∈"
                  (Term.app `gamma1' [`N])))]
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
                     [(Tactic.simpLemma [] [] `Gamma1_to_Gamma0_mem)
                      ","
                      (Tactic.simpLemma [] [] `Subgroup.coe_mk)
                      ","
                      (Tactic.simpLemma [] [] `coe_coe)
                      ","
                      (Tactic.simpLemma [] [] `coe_matrix_coe)
                      ","
                      (Tactic.simpLemma [] [] `Int.coe_castRingHom)
                      ","
                      (Tactic.simpLemma [] [] `map_apply)]
                     "]"]
                    [])
                   []
                   (Tactic.exact "exact" `ha)]))))))
            []
            (Tactic.refine'
             "refine'"
             (Term.anonymousCtor
              "⟨"
              [(Term.typeAscription
                "("
                (Term.anonymousCtor
                 "⟨"
                 [(Term.typeAscription
                   "("
                   (Term.anonymousCtor "⟨" [`A "," `hA] "⟩")
                   ":"
                   [(Term.app `gamma0 [`N])]
                   ")")
                  ","
                  `HA]
                 "⟩")
                ":"
                [(Term.typeAscription
                  "("
                  (Term.app `gamma1' [`N])
                  ":"
                  [(Term.app `Subgroup [(Term.app `gamma0 [`N])])]
                  ")")]
                ")")
               ","
               (Term.hole "_")]
              "⟩"))
            []
            (Tactic.simp "simp" [] [] [] [] [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.intro "intro" [`ha])
        []
        (Mathlib.Tactic.tacticSimp_rw__
         "simp_rw"
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `gamma1) "," (Tactic.rwRule [] `Subgroup.mem_map)]
          "]")
         [])
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hA []]
           [(Term.typeSpec ":" («term_∈_» `A "∈" (Term.app `gamma0 [`N])))]
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
                ["["
                 [(Tactic.simpLemma [] [] `ha.right.right)
                  ","
                  (Tactic.simpLemma [] [] `Gamma0_mem)
                  ","
                  (Tactic.simpLemma [] [] `Subtype.val_eq_coe)]
                 "]"]
                [])]))))))
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`HA []]
           [(Term.typeSpec
             ":"
             («term_∈_»
              (Term.typeAscription
               "("
               (Term.anonymousCtor "⟨" [`A "," `hA] "⟩")
               ":"
               [(Term.app `gamma0 [`N])]
               ")")
              "∈"
              (Term.app `gamma1' [`N])))]
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
                 [(Tactic.simpLemma [] [] `Gamma1_to_Gamma0_mem)
                  ","
                  (Tactic.simpLemma [] [] `Subgroup.coe_mk)
                  ","
                  (Tactic.simpLemma [] [] `coe_coe)
                  ","
                  (Tactic.simpLemma [] [] `coe_matrix_coe)
                  ","
                  (Tactic.simpLemma [] [] `Int.coe_castRingHom)
                  ","
                  (Tactic.simpLemma [] [] `map_apply)]
                 "]"]
                [])
               []
               (Tactic.exact "exact" `ha)]))))))
        []
        (Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [(Term.typeAscription
            "("
            (Term.anonymousCtor
             "⟨"
             [(Term.typeAscription
               "("
               (Term.anonymousCtor "⟨" [`A "," `hA] "⟩")
               ":"
               [(Term.app `gamma0 [`N])]
               ")")
              ","
              `HA]
             "⟩")
            ":"
            [(Term.typeAscription
              "("
              (Term.app `gamma1' [`N])
              ":"
              [(Term.app `Subgroup [(Term.app `gamma0 [`N])])]
              ")")]
            ")")
           ","
           (Term.hole "_")]
          "⟩"))
        []
        (Tactic.simp "simp" [] [] [] [] [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [(Term.typeAscription
          "("
          (Term.anonymousCtor
           "⟨"
           [(Term.typeAscription
             "("
             (Term.anonymousCtor "⟨" [`A "," `hA] "⟩")
             ":"
             [(Term.app `gamma0 [`N])]
             ")")
            ","
            `HA]
           "⟩")
          ":"
          [(Term.typeAscription
            "("
            (Term.app `gamma1' [`N])
            ":"
            [(Term.app `Subgroup [(Term.app `gamma0 [`N])])]
            ")")]
          ")")
         ","
         (Term.hole "_")]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.typeAscription
         "("
         (Term.anonymousCtor
          "⟨"
          [(Term.typeAscription
            "("
            (Term.anonymousCtor "⟨" [`A "," `hA] "⟩")
            ":"
            [(Term.app `gamma0 [`N])]
            ")")
           ","
           `HA]
          "⟩")
         ":"
         [(Term.typeAscription
           "("
           (Term.app `gamma1' [`N])
           ":"
           [(Term.app `Subgroup [(Term.app `gamma0 [`N])])]
           ")")]
         ")")
        ","
        (Term.hole "_")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.anonymousCtor
        "⟨"
        [(Term.typeAscription
          "("
          (Term.anonymousCtor "⟨" [`A "," `hA] "⟩")
          ":"
          [(Term.app `gamma0 [`N])]
          ")")
         ","
         `HA]
        "⟩")
       ":"
       [(Term.typeAscription
         "("
         (Term.app `gamma1' [`N])
         ":"
         [(Term.app `Subgroup [(Term.app `gamma0 [`N])])]
         ")")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.app `gamma1' [`N])
       ":"
       [(Term.app `Subgroup [(Term.app `gamma0 [`N])])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Subgroup [(Term.app `gamma0 [`N])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `gamma0 [`N])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `N
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `gamma0
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `gamma0 [`N]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Subgroup
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `gamma1' [`N])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `N
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `gamma1'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.typeAscription
         "("
         (Term.anonymousCtor "⟨" [`A "," `hA] "⟩")
         ":"
         [(Term.app `gamma0 [`N])]
         ")")
        ","
        `HA]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `HA
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.anonymousCtor "⟨" [`A "," `hA] "⟩")
       ":"
       [(Term.app `gamma0 [`N])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `gamma0 [`N])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `N
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `gamma0
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`A "," `hA] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hA
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`HA []]
         [(Term.typeSpec
           ":"
           («term_∈_»
            (Term.typeAscription
             "("
             (Term.anonymousCtor "⟨" [`A "," `hA] "⟩")
             ":"
             [(Term.app `gamma0 [`N])]
             ")")
            "∈"
            (Term.app `gamma1' [`N])))]
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
               [(Tactic.simpLemma [] [] `Gamma1_to_Gamma0_mem)
                ","
                (Tactic.simpLemma [] [] `Subgroup.coe_mk)
                ","
                (Tactic.simpLemma [] [] `coe_coe)
                ","
                (Tactic.simpLemma [] [] `coe_matrix_coe)
                ","
                (Tactic.simpLemma [] [] `Int.coe_castRingHom)
                ","
                (Tactic.simpLemma [] [] `map_apply)]
               "]"]
              [])
             []
             (Tactic.exact "exact" `ha)]))))))
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
            [(Tactic.simpLemma [] [] `Gamma1_to_Gamma0_mem)
             ","
             (Tactic.simpLemma [] [] `Subgroup.coe_mk)
             ","
             (Tactic.simpLemma [] [] `coe_coe)
             ","
             (Tactic.simpLemma [] [] `coe_matrix_coe)
             ","
             (Tactic.simpLemma [] [] `Int.coe_castRingHom)
             ","
             (Tactic.simpLemma [] [] `map_apply)]
            "]"]
           [])
          []
          (Tactic.exact "exact" `ha)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `ha)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
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
        [(Tactic.simpLemma [] [] `Gamma1_to_Gamma0_mem)
         ","
         (Tactic.simpLemma [] [] `Subgroup.coe_mk)
         ","
         (Tactic.simpLemma [] [] `coe_coe)
         ","
         (Tactic.simpLemma [] [] `coe_matrix_coe)
         ","
         (Tactic.simpLemma [] [] `Int.coe_castRingHom)
         ","
         (Tactic.simpLemma [] [] `map_apply)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Int.coe_castRingHom
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_matrix_coe
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
      `Subgroup.coe_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Gamma1_to_Gamma0_mem
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_»
       (Term.typeAscription
        "("
        (Term.anonymousCtor "⟨" [`A "," `hA] "⟩")
        ":"
        [(Term.app `gamma0 [`N])]
        ")")
       "∈"
       (Term.app `gamma1' [`N]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `gamma1' [`N])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `N
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `gamma1'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription
       "("
       (Term.anonymousCtor "⟨" [`A "," `hA] "⟩")
       ":"
       [(Term.app `gamma0 [`N])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `gamma0 [`N])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `N
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `gamma0
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`A "," `hA] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hA
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hA []]
         [(Term.typeSpec ":" («term_∈_» `A "∈" (Term.app `gamma0 [`N])))]
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
              ["["
               [(Tactic.simpLemma [] [] `ha.right.right)
                ","
                (Tactic.simpLemma [] [] `Gamma0_mem)
                ","
                (Tactic.simpLemma [] [] `Subtype.val_eq_coe)]
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
           []
           ["["
            [(Tactic.simpLemma [] [] `ha.right.right)
             ","
             (Tactic.simpLemma [] [] `Gamma0_mem)
             ","
             (Tactic.simpLemma [] [] `Subtype.val_eq_coe)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpLemma [] [] `ha.right.right)
         ","
         (Tactic.simpLemma [] [] `Gamma0_mem)
         ","
         (Tactic.simpLemma [] [] `Subtype.val_eq_coe)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.val_eq_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Gamma0_mem
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha.right.right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_» `A "∈" (Term.app `gamma0 [`N]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `gamma0 [`N])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `N
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `gamma0
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `A
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `gamma1) "," (Tactic.rwRule [] `Subgroup.mem_map)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subgroup.mem_map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `gamma1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`ha])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.intro "intro" [`ha])
        []
        (Mathlib.Tactic.tacticSimp_rw__
         "simp_rw"
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `gamma1) "," (Tactic.rwRule [] `Subgroup.mem_map)]
          "]")
         [(Tactic.location "at" (Tactic.locationHyp [`ha] []))])
        []
        (Tactic.simp "simp" [] [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`ha] []))])
        []
        (Std.Tactic.obtain
         "obtain"
         [(Std.Tactic.RCases.rcasesPatMed
           [(Std.Tactic.RCases.rcasesPat.tuple
             "⟨"
             [(Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                    [])]
                  "⟩")])
               [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hxx)])
               [])]
             "⟩")])]
         []
         [":=" [`ha]])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Gamma1_to_Gamma0_mem)] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hxx)] "]")
         [])
        []
        (convert "convert" [] `hx [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert "convert" [] `hx [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hxx)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hxx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Gamma1_to_Gamma0_mem)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Gamma1_to_Gamma0_mem
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                  [])]
                "⟩")])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hxx)])
             [])]
           "⟩")])]
       []
       [":=" [`ha]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [(Tactic.location "at" (Tactic.locationHyp [`ha] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `gamma1) "," (Tactic.rwRule [] `Subgroup.mem_map)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`ha] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subgroup.mem_map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `gamma1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`ha])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.constructor "constructor")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_∈_» `A "∈" (Term.app `gamma1 [`N]))
       "↔"
       («term_∧_»
        («term_=_»
         (Term.typeAscription
          "("
          (Term.typeAscription
           "("
           (Term.app
            (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
            [(num "0") (num "0")])
           ":"
           [(termℤ "ℤ")]
           ")")
          ":"
          [(Term.app `Zmod [`N])]
          ")")
         "="
         (num "1"))
        "∧"
        («term_∧_»
         («term_=_»
          (Term.typeAscription
           "("
           (Term.typeAscription
            "("
            (Term.app
             (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
             [(num "1") (num "1")])
            ":"
            [(termℤ "ℤ")]
            ")")
           ":"
           [(Term.app `Zmod [`N])]
           ")")
          "="
          (num "1"))
         "∧"
         («term_=_»
          (Term.typeAscription
           "("
           (Term.typeAscription
            "("
            (Term.app
             (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
             [(num "1") (num "0")])
            ":"
            [(termℤ "ℤ")]
            ")")
           ":"
           [(Term.app `Zmod [`N])]
           ")")
          "="
          (num "0")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∧_»
       («term_=_»
        (Term.typeAscription
         "("
         (Term.typeAscription
          "("
          (Term.app
           (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
           [(num "0") (num "0")])
          ":"
          [(termℤ "ℤ")]
          ")")
         ":"
         [(Term.app `Zmod [`N])]
         ")")
        "="
        (num "1"))
       "∧"
       («term_∧_»
        («term_=_»
         (Term.typeAscription
          "("
          (Term.typeAscription
           "("
           (Term.app
            (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
            [(num "1") (num "1")])
           ":"
           [(termℤ "ℤ")]
           ")")
          ":"
          [(Term.app `Zmod [`N])]
          ")")
         "="
         (num "1"))
        "∧"
        («term_=_»
         (Term.typeAscription
          "("
          (Term.typeAscription
           "("
           (Term.app
            (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
            [(num "1") (num "0")])
           ":"
           [(termℤ "ℤ")]
           ")")
          ":"
          [(Term.app `Zmod [`N])]
          ")")
         "="
         (num "0"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∧_»
       («term_=_»
        (Term.typeAscription
         "("
         (Term.typeAscription
          "("
          (Term.app
           (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
           [(num "1") (num "1")])
          ":"
          [(termℤ "ℤ")]
          ")")
         ":"
         [(Term.app `Zmod [`N])]
         ")")
        "="
        (num "1"))
       "∧"
       («term_=_»
        (Term.typeAscription
         "("
         (Term.typeAscription
          "("
          (Term.app
           (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
           [(num "1") (num "0")])
          ":"
          [(termℤ "ℤ")]
          ")")
         ":"
         [(Term.app `Zmod [`N])]
         ")")
        "="
        (num "0")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.typeAscription
        "("
        (Term.typeAscription
         "("
         (Term.app
          (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
          [(num "1") (num "0")])
         ":"
         [(termℤ "ℤ")]
         ")")
        ":"
        [(Term.app `Zmod [`N])]
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
       (Term.typeAscription
        "("
        (Term.app
         (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
         [(num "1") (num "0")])
        ":"
        [(termℤ "ℤ")]
        ")")
       ":"
       [(Term.app `Zmod [`N])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Zmod [`N])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `N
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Zmod
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.app
        (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
        [(num "1") (num "0")])
       ":"
       [(termℤ "ℤ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℤ "ℤ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
       [(num "1") (num "0")])
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
      (NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_» "↑ₘ" `A)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.CongruenceSubgroups.«term↑ₘ_»', expected 'NumberTheory.ModularForms.CongruenceSubgroups.term↑ₘ_._@.NumberTheory.ModularForms.CongruenceSubgroups._hyg.836'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    Gamma1_mem
    ( N : ℕ ) ( A : SL( 2 , ℤ ) )
      :
        A ∈ gamma1 N
          ↔
          ( ( ↑ₘ A 0 0 : ℤ ) : Zmod N ) = 1
            ∧
            ( ( ↑ₘ A 1 1 : ℤ ) : Zmod N ) = 1 ∧ ( ( ↑ₘ A 1 0 : ℤ ) : Zmod N ) = 0
    :=
      by
        constructor
          ·
            intro ha
              simp_rw [ gamma1 , Subgroup.mem_map ] at ha
              simp at ha
              obtain ⟨ ⟨ x , hx ⟩ , hxx ⟩ := ha
              rw [ Gamma1_to_Gamma0_mem ] at hx
              rw [ ← hxx ]
              convert hx
          ·
            intro ha
              simp_rw [ gamma1 , Subgroup.mem_map ]
              have hA : A ∈ gamma0 N := by simp [ ha.right.right , Gamma0_mem , Subtype.val_eq_coe ]
              have
                HA
                  : ( ⟨ A , hA ⟩ : gamma0 N ) ∈ gamma1' N
                  :=
                  by
                    simp
                        only
                        [
                          Gamma1_to_Gamma0_mem
                            ,
                            Subgroup.coe_mk
                            ,
                            coe_coe
                            ,
                            coe_matrix_coe
                            ,
                            Int.coe_castRingHom
                            ,
                            map_apply
                          ]
                      exact ha
              refine'
                ⟨ ( ⟨ ( ⟨ A , hA ⟩ : gamma0 N ) , HA ⟩ : ( gamma1' N : Subgroup gamma0 N ) ) , _ ⟩
              simp
#align Gamma1_mem Gamma1_mem

theorem Gamma1_in_Gamma0 (N : ℕ) : gamma1 N ≤ gamma0 N :=
  by
  intro x HA
  simp only [Gamma0_mem, Gamma1_mem, coe_coe, coe_matrix_coe, Int.coe_castRingHom, map_apply] at *
  exact HA.2.2
#align Gamma1_in_Gamma0 Gamma1_in_Gamma0

section CongruenceSubgroup

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "A congruence subgroup is a subgroup of `SL(2, ℤ)` which contains some `Gamma N` for some\n`(N : ℕ+)`. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `IsCongruenceSubgroup [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`Γ]
         [":"
          (Term.app
           `Subgroup
           [(NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»
             "SL("
             (num "2")
             ", "
             (termℤ "ℤ")
             ")")])]
         []
         ")")]
       [(Term.typeSpec ":" (Term.prop "Prop"))])
      (Command.declValSimple
       ":="
       («term∃_,_»
        "∃"
        (Lean.explicitBinders
         (Lean.unbracketedExplicitBinders
          [(Lean.binderIdent `N)]
          [":" (Data.Pnat.Defs.«termℕ+» "ℕ+")]))
        ","
        («term_≤_» (Term.app `gamma [`N]) "≤" `Γ))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders
        (Lean.unbracketedExplicitBinders
         [(Lean.binderIdent `N)]
         [":" (Data.Pnat.Defs.«termℕ+» "ℕ+")]))
       ","
       («term_≤_» (Term.app `gamma [`N]) "≤" `Γ))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_» (Term.app `gamma [`N]) "≤" `Γ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Γ
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `gamma [`N])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `N
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `gamma
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'Lean.bracketedExplicitBinders'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Pnat.Defs.«termℕ+» "ℕ+")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.prop "Prop")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Subgroup
       [(NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»
         "SL("
         (num "2")
         ", "
         (termℤ "ℤ")
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»
       "SL("
       (num "2")
       ", "
       (termℤ "ℤ")
       ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»', expected 'NumberTheory.ModularForms.CongruenceSubgroups.termSL(_,_)._@.NumberTheory.ModularForms.CongruenceSubgroups._hyg.5'
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
/--
    A congruence subgroup is a subgroup of `SL(2, ℤ)` which contains some `Gamma N` for some
    `(N : ℕ+)`. -/
  def IsCongruenceSubgroup ( Γ : Subgroup SL( 2 , ℤ ) ) : Prop := ∃ N : ℕ+ , gamma N ≤ Γ
#align is_congruence_subgroup IsCongruenceSubgroup

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `is_congruence_subgroup_trans [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`H `K]
         [":"
          (Term.app
           `Subgroup
           [(NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»
             "SL("
             (num "2")
             ", "
             (termℤ "ℤ")
             ")")])]
         []
         ")")
        (Term.explicitBinder "(" [`h] [":" («term_≤_» `H "≤" `K)] [] ")")
        (Term.explicitBinder "(" [`h2] [":" (Term.app `IsCongruenceSubgroup [`H])] [] ")")]
       (Term.typeSpec ":" (Term.app `IsCongruenceSubgroup [`K])))
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
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `N)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hN)])
                  [])]
                "⟩")])]
            []
            [":=" [`h2]])
           []
           (Tactic.refine'
            "refine'"
            (Term.anonymousCtor "⟨" [`N "," (Term.app `le_trans [`hN `h])] "⟩"))])))
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
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `N)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hN)])
                 [])]
               "⟩")])]
           []
           [":=" [`h2]])
          []
          (Tactic.refine'
           "refine'"
           (Term.anonymousCtor "⟨" [`N "," (Term.app `le_trans [`hN `h])] "⟩"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine' "refine'" (Term.anonymousCtor "⟨" [`N "," (Term.app `le_trans [`hN `h])] "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`N "," (Term.app `le_trans [`hN `h])] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `le_trans [`hN `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hN
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `N
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `N)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hN)])
             [])]
           "⟩")])]
       []
       [":=" [`h2]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h2
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `IsCongruenceSubgroup [`K])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsCongruenceSubgroup
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsCongruenceSubgroup [`H])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsCongruenceSubgroup
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_» `H "≤" `K)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `H
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Subgroup
       [(NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»
         "SL("
         (num "2")
         ", "
         (termℤ "ℤ")
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»
       "SL("
       (num "2")
       ", "
       (termℤ "ℤ")
       ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»', expected 'NumberTheory.ModularForms.CongruenceSubgroups.termSL(_,_)._@.NumberTheory.ModularForms.CongruenceSubgroups._hyg.5'
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
  is_congruence_subgroup_trans
  ( H K : Subgroup SL( 2 , ℤ ) ) ( h : H ≤ K ) ( h2 : IsCongruenceSubgroup H )
    : IsCongruenceSubgroup K
  := by obtain ⟨ N , hN ⟩ := h2 refine' ⟨ N , le_trans hN h ⟩
#align is_congruence_subgroup_trans is_congruence_subgroup_trans

theorem Gamma_is_cong_sub (N : ℕ+) : IsCongruenceSubgroup (gamma N) :=
  ⟨N, by simp only [le_refl]⟩
#align Gamma_is_cong_sub Gamma_is_cong_sub

theorem Gamma1_is_congruence (N : ℕ+) : IsCongruenceSubgroup (gamma1 N) :=
  by
  refine' ⟨N, _⟩
  intro A hA
  simp only [Gamma1_mem, Gamma_mem] at *
  simp only [hA, eq_self_iff_true, and_self_iff]
#align Gamma1_is_congruence Gamma1_is_congruence

theorem Gamma0_is_congruence (N : ℕ+) : IsCongruenceSubgroup (gamma0 N) :=
  is_congruence_subgroup_trans _ _ (Gamma1_in_Gamma0 N) (Gamma1_is_congruence N)
#align Gamma0_is_congruence Gamma0_is_congruence

end CongruenceSubgroup

section Conjugation

open Pointwise

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `Gamma_cong_eq_self [])
      (Command.declSig
       [(Term.explicitBinder "(" [`N] [":" (termℕ "ℕ")] [] ")")
        (Term.explicitBinder
         "("
         [`g]
         [":"
          (Term.app
           `ConjAct
           [(NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»
             "SL("
             (num "2")
             ", "
             (termℤ "ℤ")
             ")")])]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Algebra.Group.Defs.«term_•_» `g " • " (Term.app `gamma [`N]))
         "="
         (Term.app `gamma [`N]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.apply
            "apply"
            (Term.app `Subgroup.Normal.conj_act [(Term.app `Gamma_normal [`N])]))])))
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
           (Term.app `Subgroup.Normal.conj_act [(Term.app `Gamma_normal [`N])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" (Term.app `Subgroup.Normal.conj_act [(Term.app `Gamma_normal [`N])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Subgroup.Normal.conj_act [(Term.app `Gamma_normal [`N])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Gamma_normal [`N])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `N
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Gamma_normal
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Gamma_normal [`N]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Subgroup.Normal.conj_act
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Algebra.Group.Defs.«term_•_» `g " • " (Term.app `gamma [`N]))
       "="
       (Term.app `gamma [`N]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `gamma [`N])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `N
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `gamma
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Algebra.Group.Defs.«term_•_» `g " • " (Term.app `gamma [`N]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `gamma [`N])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `N
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `gamma
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 73, (some 73, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `ConjAct
       [(NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»
         "SL("
         (num "2")
         ", "
         (termℤ "ℤ")
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»
       "SL("
       (num "2")
       ", "
       (termℤ "ℤ")
       ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»', expected 'NumberTheory.ModularForms.CongruenceSubgroups.termSL(_,_)._@.NumberTheory.ModularForms.CongruenceSubgroups._hyg.5'
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
  Gamma_cong_eq_self
  ( N : ℕ ) ( g : ConjAct SL( 2 , ℤ ) ) : g • gamma N = gamma N
  := by apply Subgroup.Normal.conj_act Gamma_normal N
#align Gamma_cong_eq_self Gamma_cong_eq_self

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `conj_cong_is_cong [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`g]
         [":"
          (Term.app
           `ConjAct
           [(NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»
             "SL("
             (num "2")
             ", "
             (termℤ "ℤ")
             ")")])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`Γ]
         [":"
          (Term.app
           `Subgroup
           [(NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»
             "SL("
             (num "2")
             ", "
             (termℤ "ℤ")
             ")")])]
         []
         ")")
        (Term.explicitBinder "(" [`h] [":" (Term.app `IsCongruenceSubgroup [`Γ])] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app `IsCongruenceSubgroup [(Algebra.Group.Defs.«term_•_» `g " • " `Γ)])))
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
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `N)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `HN)])
                  [])]
                "⟩")])]
            []
            [":=" [`h]])
           []
           (Tactic.refine' "refine'" (Term.anonymousCtor "⟨" [`N "," (Term.hole "_")] "⟩"))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app `Gamma_cong_eq_self [`N `g]))
              ","
              (Tactic.rwRule [] `Subgroup.pointwise_smul_le_pointwise_smul_iff)]
             "]")
            [])
           []
           (Tactic.exact "exact" `HN)])))
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
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `N)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `HN)])
                 [])]
               "⟩")])]
           []
           [":=" [`h]])
          []
          (Tactic.refine' "refine'" (Term.anonymousCtor "⟨" [`N "," (Term.hole "_")] "⟩"))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app `Gamma_cong_eq_self [`N `g]))
             ","
             (Tactic.rwRule [] `Subgroup.pointwise_smul_le_pointwise_smul_iff)]
            "]")
           [])
          []
          (Tactic.exact "exact" `HN)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `HN)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `HN
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `Gamma_cong_eq_self [`N `g]))
         ","
         (Tactic.rwRule [] `Subgroup.pointwise_smul_le_pointwise_smul_iff)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subgroup.pointwise_smul_le_pointwise_smul_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Gamma_cong_eq_self [`N `g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `N
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Gamma_cong_eq_self
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine' "refine'" (Term.anonymousCtor "⟨" [`N "," (Term.hole "_")] "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`N "," (Term.hole "_")] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `N
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `N)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `HN)])
             [])]
           "⟩")])]
       []
       [":=" [`h]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `IsCongruenceSubgroup [(Algebra.Group.Defs.«term_•_» `g " • " `Γ)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_» `g " • " `Γ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Γ
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Group.Defs.«term_•_» `g " • " `Γ)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsCongruenceSubgroup
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsCongruenceSubgroup [`Γ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Γ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsCongruenceSubgroup
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Subgroup
       [(NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»
         "SL("
         (num "2")
         ", "
         (termℤ "ℤ")
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»
       "SL("
       (num "2")
       ", "
       (termℤ "ℤ")
       ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.CongruenceSubgroups.«termSL(_,_)»', expected 'NumberTheory.ModularForms.CongruenceSubgroups.termSL(_,_)._@.NumberTheory.ModularForms.CongruenceSubgroups._hyg.5'
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
  conj_cong_is_cong
  ( g : ConjAct SL( 2 , ℤ ) ) ( Γ : Subgroup SL( 2 , ℤ ) ) ( h : IsCongruenceSubgroup Γ )
    : IsCongruenceSubgroup g • Γ
  :=
    by
      obtain ⟨ N , HN ⟩ := h
        refine' ⟨ N , _ ⟩
        rw [ ← Gamma_cong_eq_self N g , Subgroup.pointwise_smul_le_pointwise_smul_iff ]
        exact HN
#align conj_cong_is_cong conj_cong_is_cong

end Conjugation

