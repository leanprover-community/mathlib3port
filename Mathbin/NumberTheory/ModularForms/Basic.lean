/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck

! This file was ported from Lean 3 source module number_theory.modular_forms.basic
! leanprover-community/mathlib commit 26f081a2fb920140ed5bc5cc5344e84bcc7cb2b2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Geometry.Manifold.Mfderiv
import Mathbin.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathbin.Analysis.Complex.UpperHalfPlane.Topology
import Mathbin.NumberTheory.ModularForms.SlashInvariantForms

/-!
# Modular forms

This file defines modular forms and proves some basic properties about them.

We begin by defining modular forms and cusp forms as extension of `slash_invariant_forms` then we
define the space of modular forms, cusp forms and prove that the product of two modular forms is a
modular form.
-/


open Complex UpperHalfPlane

open TopologicalSpace Manifold UpperHalfPlane

noncomputable section

instance UpperHalfPlane.chartedSpace : ChartedSpace ℂ ℍ :=
  UpperHalfPlane.open_embedding_coe.singletonChartedSpace
#align upper_half_plane.charted_space UpperHalfPlane.chartedSpace

instance UpperHalfPlane.smooth_manifold_with_corners : SmoothManifoldWithCorners 𝓘(ℂ) ℍ :=
  UpperHalfPlane.open_embedding_coe.singleton_smooth_manifold_with_corners 𝓘(ℂ)
#align upper_half_plane.smooth_manifold_with_corners UpperHalfPlane.smooth_manifold_with_corners

-- mathport name: «expr↑ₘ »
local prefix:1024 "↑ₘ" => @coe _ (Matrix (Fin 2) (Fin 2) _) _

-- mathport name: «exprGL( , )⁺»
local notation "GL(" n ", " R ")" "⁺" => Matrix.gLPos (Fin n) R

-- mathport name: «exprSL( , )»
local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

section ModularForm

open ModularForm

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.variable
     "variable"
     [(Term.explicitBinder "(" [`F] [":" (Term.type "Type" [(Level.hole "_")])] [] ")")
      (Term.explicitBinder
       "("
       [`Γ]
       [":"
        (Term.app
         `Subgroup
         [(NumberTheory.ModularForms.Basic.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")])]
       []
       ")")
      (Term.explicitBinder "(" [`k] [":" (termℤ "ℤ")] [] ")")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℤ "ℤ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Subgroup
       [(NumberTheory.ModularForms.Basic.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.Basic.«termSL(_,_)»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.Basic.«termSL(_,_)»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.ModularForms.Basic.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.Basic.«termSL(_,_)»', expected 'NumberTheory.ModularForms.Basic.termSL(_,_)._@.NumberTheory.ModularForms.Basic._hyg.927'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'-/-- failed to format: format: uncaught backtrack exception
variable ( F : Type _ ) ( Γ : Subgroup SL( 2 , ℤ ) ) ( k : ℤ )

-- mathport name: «expr ∣[ , ]»
local notation:73 f "∣[" k:0 "," A "]" => SlashAction.map ℂ k A f

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "These are `slash_invariant_form`'s that are holomophic and bounded at infinity. -/")]
      []
      []
      []
      []
      [])
     (Command.structure
      (Command.structureTk "structure")
      (Command.declId `ModularForm [])
      []
      [(Command.extends "extends" [(Term.app `SlashInvariantForm [`Γ `k])])]
      []
      ["where"
       []
       (Command.structFields
        [(Command.structSimpleBinder
          (Command.declModifiers [] [] [] [] [] [])
          `holo'
          (Command.optDeclSig
           []
           [(Term.typeSpec
             ":"
             (Term.app
              `Mdifferentiable
              [(Manifold.Geometry.Manifold.SmoothManifoldWithCorners.model_with_corners_self.self
                "𝓘("
                (Data.Complex.Basic.termℂ "ℂ")
                ")")
               (Manifold.Geometry.Manifold.SmoothManifoldWithCorners.model_with_corners_self.self
                "𝓘("
                (Data.Complex.Basic.termℂ "ℂ")
                ")")
               (Term.typeAscription
                "("
                `to_fun
                ":"
                [(Term.arrow
                  (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
                  "→"
                  (Data.Complex.Basic.termℂ "ℂ"))]
                ")")]))])
          [])
         (Command.structSimpleBinder
          (Command.declModifiers [] [] [] [] [] [])
          `bdd_at_infty'
          (Command.optDeclSig
           []
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [`A]
              [(Term.typeSpec
                ":"
                (NumberTheory.ModularForms.Basic.«termSL(_,_)»
                 "SL("
                 (num "2")
                 ", "
                 (termℤ "ℤ")
                 ")"))]
              ","
              (Term.app
               `IsBoundedAtImInfty
               [(NumberTheory.ModularForms.Basic.«term_∣[_,_]» `to_fun "∣[" `k "," `A "]")])))])
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
       [`A]
       [(Term.typeSpec
         ":"
         (NumberTheory.ModularForms.Basic.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")"))]
       ","
       (Term.app
        `IsBoundedAtImInfty
        [(NumberTheory.ModularForms.Basic.«term_∣[_,_]» `to_fun "∣[" `k "," `A "]")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `IsBoundedAtImInfty
       [(NumberTheory.ModularForms.Basic.«term_∣[_,_]» `to_fun "∣[" `k "," `A "]")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.Basic.«term_∣[_,_]»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.Basic.«term_∣[_,_]»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.ModularForms.Basic.«term_∣[_,_]» `to_fun "∣[" `k "," `A "]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.Basic.«term_∣[_,_]»', expected 'NumberTheory.ModularForms.Basic.term_∣[_,_]._@.NumberTheory.ModularForms.Basic._hyg.1737'-/-- failed to format: format: uncaught backtrack exception
/-- These are `slash_invariant_form`'s that are holomophic and bounded at infinity. -/
  structure
    ModularForm
    extends SlashInvariantForm Γ k
    where
      holo' : Mdifferentiable 𝓘( ℂ ) 𝓘( ℂ ) ( to_fun : ℍ → ℂ )
        bdd_at_infty' : ∀ A : SL( 2 , ℤ ) , IsBoundedAtImInfty to_fun ∣[ k , A ]
#align modular_form ModularForm

/-- The `slash_invariant_form` associated to a `modular_form`. -/
add_decl_doc ModularForm.toSlashInvariantForm

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "These are `slash_invariant_form`s that are holomophic and zero at infinity. -/")]
      []
      []
      []
      []
      [])
     (Command.structure
      (Command.structureTk "structure")
      (Command.declId `CuspForm [])
      []
      [(Command.extends "extends" [(Term.app `SlashInvariantForm [`Γ `k])])]
      []
      ["where"
       []
       (Command.structFields
        [(Command.structSimpleBinder
          (Command.declModifiers [] [] [] [] [] [])
          `holo'
          (Command.optDeclSig
           []
           [(Term.typeSpec
             ":"
             (Term.app
              `Mdifferentiable
              [(Manifold.Geometry.Manifold.SmoothManifoldWithCorners.model_with_corners_self.self
                "𝓘("
                (Data.Complex.Basic.termℂ "ℂ")
                ")")
               (Manifold.Geometry.Manifold.SmoothManifoldWithCorners.model_with_corners_self.self
                "𝓘("
                (Data.Complex.Basic.termℂ "ℂ")
                ")")
               (Term.typeAscription
                "("
                `to_fun
                ":"
                [(Term.arrow
                  (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
                  "→"
                  (Data.Complex.Basic.termℂ "ℂ"))]
                ")")]))])
          [])
         (Command.structSimpleBinder
          (Command.declModifiers [] [] [] [] [] [])
          `zero_at_infty'
          (Command.optDeclSig
           []
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [`A]
              [(Term.typeSpec
                ":"
                (NumberTheory.ModularForms.Basic.«termSL(_,_)»
                 "SL("
                 (num "2")
                 ", "
                 (termℤ "ℤ")
                 ")"))]
              ","
              (Term.app
               `IsZeroAtImInfty
               [(NumberTheory.ModularForms.Basic.«term_∣[_,_]» `to_fun "∣[" `k "," `A "]")])))])
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
       [`A]
       [(Term.typeSpec
         ":"
         (NumberTheory.ModularForms.Basic.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")"))]
       ","
       (Term.app
        `IsZeroAtImInfty
        [(NumberTheory.ModularForms.Basic.«term_∣[_,_]» `to_fun "∣[" `k "," `A "]")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `IsZeroAtImInfty
       [(NumberTheory.ModularForms.Basic.«term_∣[_,_]» `to_fun "∣[" `k "," `A "]")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.Basic.«term_∣[_,_]»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.Basic.«term_∣[_,_]»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.ModularForms.Basic.«term_∣[_,_]» `to_fun "∣[" `k "," `A "]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.Basic.«term_∣[_,_]»', expected 'NumberTheory.ModularForms.Basic.term_∣[_,_]._@.NumberTheory.ModularForms.Basic._hyg.1737'-/-- failed to format: format: uncaught backtrack exception
/-- These are `slash_invariant_form`s that are holomophic and zero at infinity. -/
  structure
    CuspForm
    extends SlashInvariantForm Γ k
    where
      holo' : Mdifferentiable 𝓘( ℂ ) 𝓘( ℂ ) ( to_fun : ℍ → ℂ )
        zero_at_infty' : ∀ A : SL( 2 , ℤ ) , IsZeroAtImInfty to_fun ∣[ k , A ]
#align cusp_form CuspForm

/-- The `slash_invariant_form` associated to a `cusp_form`. -/
add_decl_doc CuspForm.toSlashInvariantForm

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`modular_form_class F Γ k` says that `F` is a type of bundled functions that extend\n`slash_invariant_forms_class` by requiring that the functions be holomorphic and bounded\nat infinity. -/")]
      []
      []
      []
      []
      [])
     (Command.structure
      (Command.classTk "class")
      (Command.declId `ModularFormClass [])
      []
      [(Command.extends "extends" [(Term.app `SlashInvariantFormClass [`F `Γ `k])])]
      []
      ["where"
       []
       (Command.structFields
        [(Command.structSimpleBinder
          (Command.declModifiers [] [] [] [] [] [])
          `holo
          (Command.optDeclSig
           []
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [`f]
              [(Term.typeSpec ":" `F)]
              ","
              (Term.app
               `Mdifferentiable
               [(Manifold.Geometry.Manifold.SmoothManifoldWithCorners.model_with_corners_self.self
                 "𝓘("
                 (Data.Complex.Basic.termℂ "ℂ")
                 ")")
                (Manifold.Geometry.Manifold.SmoothManifoldWithCorners.model_with_corners_self.self
                 "𝓘("
                 (Data.Complex.Basic.termℂ "ℂ")
                 ")")
                (Term.typeAscription
                 "("
                 `f
                 ":"
                 [(Term.arrow
                   (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
                   "→"
                   (Data.Complex.Basic.termℂ "ℂ"))]
                 ")")])))])
          [])
         (Command.structSimpleBinder
          (Command.declModifiers [] [] [] [] [] [])
          `bdd_at_infty
          (Command.optDeclSig
           []
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.explicitBinder "(" [`f] [":" `F] [] ")")
               (Term.explicitBinder
                "("
                [`A]
                [":"
                 (NumberTheory.ModularForms.Basic.«termSL(_,_)»
                  "SL("
                  (num "2")
                  ", "
                  (termℤ "ℤ")
                  ")")]
                []
                ")")]
              []
              ","
              (Term.app
               `IsBoundedAtImInfty
               [(NumberTheory.ModularForms.Basic.«term_∣[_,_]» `f "∣[" `k "," `A "]")])))])
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
       [(Term.explicitBinder "(" [`f] [":" `F] [] ")")
        (Term.explicitBinder
         "("
         [`A]
         [":" (NumberTheory.ModularForms.Basic.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")]
         []
         ")")]
       []
       ","
       (Term.app
        `IsBoundedAtImInfty
        [(NumberTheory.ModularForms.Basic.«term_∣[_,_]» `f "∣[" `k "," `A "]")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `IsBoundedAtImInfty
       [(NumberTheory.ModularForms.Basic.«term_∣[_,_]» `f "∣[" `k "," `A "]")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.Basic.«term_∣[_,_]»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.Basic.«term_∣[_,_]»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.ModularForms.Basic.«term_∣[_,_]» `f "∣[" `k "," `A "]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.Basic.«term_∣[_,_]»', expected 'NumberTheory.ModularForms.Basic.term_∣[_,_]._@.NumberTheory.ModularForms.Basic._hyg.1737'-/-- failed to format: format: uncaught backtrack exception
/--
    `modular_form_class F Γ k` says that `F` is a type of bundled functions that extend
    `slash_invariant_forms_class` by requiring that the functions be holomorphic and bounded
    at infinity. -/
  class
    ModularFormClass
    extends SlashInvariantFormClass F Γ k
    where
      holo : ∀ f : F , Mdifferentiable 𝓘( ℂ ) 𝓘( ℂ ) ( f : ℍ → ℂ )
        bdd_at_infty : ∀ ( f : F ) ( A : SL( 2 , ℤ ) ) , IsBoundedAtImInfty f ∣[ k , A ]
#align modular_form_class ModularFormClass

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`cusp_form_class F Γ k` says that `F` is a type of bundled functions that extend\n`slash_invariant_forms_class` by requiring that the functions be holomorphic and zero\nat infinity. -/")]
      []
      []
      []
      []
      [])
     (Command.structure
      (Command.classTk "class")
      (Command.declId `CuspFormClass [])
      []
      [(Command.extends "extends" [(Term.app `SlashInvariantFormClass [`F `Γ `k])])]
      []
      ["where"
       []
       (Command.structFields
        [(Command.structSimpleBinder
          (Command.declModifiers [] [] [] [] [] [])
          `holo
          (Command.optDeclSig
           []
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [`f]
              [(Term.typeSpec ":" `F)]
              ","
              (Term.app
               `Mdifferentiable
               [(Manifold.Geometry.Manifold.SmoothManifoldWithCorners.model_with_corners_self.self
                 "𝓘("
                 (Data.Complex.Basic.termℂ "ℂ")
                 ")")
                (Manifold.Geometry.Manifold.SmoothManifoldWithCorners.model_with_corners_self.self
                 "𝓘("
                 (Data.Complex.Basic.termℂ "ℂ")
                 ")")
                (Term.typeAscription
                 "("
                 `f
                 ":"
                 [(Term.arrow
                   (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
                   "→"
                   (Data.Complex.Basic.termℂ "ℂ"))]
                 ")")])))])
          [])
         (Command.structSimpleBinder
          (Command.declModifiers [] [] [] [] [] [])
          `zero_at_infty
          (Command.optDeclSig
           []
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.explicitBinder "(" [`f] [":" `F] [] ")")
               (Term.explicitBinder
                "("
                [`A]
                [":"
                 (NumberTheory.ModularForms.Basic.«termSL(_,_)»
                  "SL("
                  (num "2")
                  ", "
                  (termℤ "ℤ")
                  ")")]
                []
                ")")]
              []
              ","
              (Term.app
               `IsZeroAtImInfty
               [(NumberTheory.ModularForms.Basic.«term_∣[_,_]» `f "∣[" `k "," `A "]")])))])
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
       [(Term.explicitBinder "(" [`f] [":" `F] [] ")")
        (Term.explicitBinder
         "("
         [`A]
         [":" (NumberTheory.ModularForms.Basic.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")]
         []
         ")")]
       []
       ","
       (Term.app
        `IsZeroAtImInfty
        [(NumberTheory.ModularForms.Basic.«term_∣[_,_]» `f "∣[" `k "," `A "]")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `IsZeroAtImInfty
       [(NumberTheory.ModularForms.Basic.«term_∣[_,_]» `f "∣[" `k "," `A "]")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.Basic.«term_∣[_,_]»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.Basic.«term_∣[_,_]»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.ModularForms.Basic.«term_∣[_,_]» `f "∣[" `k "," `A "]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.Basic.«term_∣[_,_]»', expected 'NumberTheory.ModularForms.Basic.term_∣[_,_]._@.NumberTheory.ModularForms.Basic._hyg.1737'-/-- failed to format: format: uncaught backtrack exception
/--
    `cusp_form_class F Γ k` says that `F` is a type of bundled functions that extend
    `slash_invariant_forms_class` by requiring that the functions be holomorphic and zero
    at infinity. -/
  class
    CuspFormClass
    extends SlashInvariantFormClass F Γ k
    where
      holo : ∀ f : F , Mdifferentiable 𝓘( ℂ ) 𝓘( ℂ ) ( f : ℍ → ℂ )
        zero_at_infty : ∀ ( f : F ) ( A : SL( 2 , ℤ ) ) , IsZeroAtImInfty f ∣[ k , A ]
#align cusp_form_class CuspFormClass

instance (priority := 100) ModularFormClass.modularForm : ModularFormClass (ModularForm Γ k) Γ k
    where
  coe := ModularForm.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  slash_action_eq := ModularForm.slash_action_eq'
  holo := ModularForm.holo'
  bdd_at_infty := ModularForm.bdd_at_infty'
#align modular_form_class.modular_form ModularFormClass.modularForm

instance (priority := 100) CuspFormClass.cuspForm : CuspFormClass (CuspForm Γ k) Γ k
    where
  coe := CuspForm.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  slash_action_eq := CuspForm.slash_action_eq'
  holo := CuspForm.holo'
  zero_at_infty := CuspForm.zero_at_infty'
#align cusp_form_class.cusp_form CuspFormClass.cuspForm

variable {F Γ k}

@[simp]
theorem modular_form_to_fun_eq_coe {f : ModularForm Γ k} : f.toFun = (f : ℍ → ℂ) :=
  rfl
#align modular_form_to_fun_eq_coe modular_form_to_fun_eq_coe

@[simp]
theorem cusp_form_to_fun_eq_coe {f : CuspForm Γ k} : f.toFun = (f : ℍ → ℂ) :=
  rfl
#align cusp_form_to_fun_eq_coe cusp_form_to_fun_eq_coe

@[ext]
theorem ModularForm.ext {f g : ModularForm Γ k} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext f g h
#align modular_form.ext ModularForm.ext

@[ext]
theorem CuspForm.ext {f g : CuspForm Γ k} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext f g h
#align cusp_form.ext CuspForm.ext

/-- Copy of a `modular_form` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def ModularForm.copy (f : ModularForm Γ k) (f' : ℍ → ℂ) (h : f' = ⇑f) : ModularForm Γ k
    where
  toFun := f'
  slash_action_eq' := h.symm ▸ f.slash_action_eq'
  holo' := h.symm ▸ f.holo'
  bdd_at_infty' A := h.symm ▸ f.bdd_at_infty' A
#align modular_form.copy ModularForm.copy

/-- Copy of a `cusp_form` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def CuspForm.copy (f : CuspForm Γ k) (f' : ℍ → ℂ) (h : f' = ⇑f) : CuspForm Γ k
    where
  toFun := f'
  slash_action_eq' := h.symm ▸ f.slash_action_eq'
  holo' := h.symm ▸ f.holo'
  zero_at_infty' A := h.symm ▸ f.zero_at_infty' A
#align cusp_form.copy CuspForm.copy

end ModularForm

namespace ModularForm

open SlashInvariantForm

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.variable
     "variable"
     [(Term.implicitBinder "{" [`F] [":" (Term.type "Type" [(Level.hole "_")])] "}")
      (Term.implicitBinder
       "{"
       [`Γ]
       [":"
        (Term.app
         `Subgroup
         [(NumberTheory.ModularForms.Basic.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")])]
       "}")
      (Term.implicitBinder "{" [`k] [":" (termℤ "ℤ")] "}")])
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
       [(NumberTheory.ModularForms.Basic.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.Basic.«termSL(_,_)»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.Basic.«termSL(_,_)»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.ModularForms.Basic.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.Basic.«termSL(_,_)»', expected 'NumberTheory.ModularForms.Basic.termSL(_,_)._@.NumberTheory.ModularForms.Basic._hyg.927'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.instBinder'-/-- failed to format: format: uncaught backtrack exception
variable { F : Type _ } { Γ : Subgroup SL( 2 , ℤ ) } { k : ℤ }

instance hasAdd : Add (ModularForm Γ k) :=
  ⟨fun f g =>
    {
      (f : SlashInvariantForm Γ k) +
        g with
      holo' := f.holo'.add g.holo'
      bdd_at_infty' := fun A => by simpa using (f.bdd_at_infty' A).add (g.bdd_at_infty' A) }⟩
#align modular_form.has_add ModularForm.hasAdd

@[simp]
theorem coe_add (f g : ModularForm Γ k) : ⇑(f + g) = f + g :=
  rfl
#align modular_form.coe_add ModularForm.coe_add

@[simp]
theorem add_apply (f g : ModularForm Γ k) (z : ℍ) : (f + g) z = f z + g z :=
  rfl
#align modular_form.add_apply ModularForm.add_apply

instance hasZero : Zero (ModularForm Γ k) :=
  ⟨{
      (0 :
        SlashInvariantForm Γ
          k) with
      holo' := fun _ => mdifferentiable_at_const 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      bdd_at_infty' := fun A => by simpa using zero_form_is_bounded_at_im_infty }⟩
#align modular_form.has_zero ModularForm.hasZero

@[simp]
theorem coe_zero : ⇑(0 : ModularForm Γ k) = (0 : ℍ → ℂ) :=
  rfl
#align modular_form.coe_zero ModularForm.coe_zero

@[simp]
theorem zero_apply (z : ℍ) : (0 : ModularForm Γ k) z = 0 :=
  rfl
#align modular_form.zero_apply ModularForm.zero_apply

section

variable {α : Type _} [HasSmul α ℂ] [IsScalarTower α ℂ ℂ]

instance hasSmul : HasSmul α (ModularForm Γ k) :=
  ⟨fun c f =>
    { c • (f : SlashInvariantForm Γ k) with
      toFun := c • f
      holo' := by simpa using f.holo'.const_smul (c • (1 : ℂ))
      bdd_at_infty' := fun A => by simpa using (f.bdd_at_infty' A).const_smul_left (c • (1 : ℂ)) }⟩
#align modular_form.has_smul ModularForm.hasSmul

@[simp]
theorem coe_smul (f : ModularForm Γ k) (n : α) : ⇑(n • f) = n • f :=
  rfl
#align modular_form.coe_smul ModularForm.coe_smul

@[simp]
theorem smul_apply (f : ModularForm Γ k) (n : α) (z : ℍ) : (n • f) z = n • f z :=
  rfl
#align modular_form.smul_apply ModularForm.smul_apply

end

instance hasNeg : Neg (ModularForm Γ k) :=
  ⟨fun f =>
    { -(f : SlashInvariantForm Γ k) with
      toFun := -f
      holo' := f.holo'.neg
      bdd_at_infty' := fun A => by simpa using (f.bdd_at_infty' A).neg }⟩
#align modular_form.has_neg ModularForm.hasNeg

@[simp]
theorem coe_neg (f : ModularForm Γ k) : ⇑(-f) = -f :=
  rfl
#align modular_form.coe_neg ModularForm.coe_neg

@[simp]
theorem neg_apply (f : ModularForm Γ k) (z : ℍ) : (-f) z = -f z :=
  rfl
#align modular_form.neg_apply ModularForm.neg_apply

instance hasSub : Sub (ModularForm Γ k) :=
  ⟨fun f g => f + -g⟩
#align modular_form.has_sub ModularForm.hasSub

@[simp]
theorem coe_sub (f g : ModularForm Γ k) : ⇑(f - g) = f - g :=
  rfl
#align modular_form.coe_sub ModularForm.coe_sub

@[simp]
theorem sub_apply (f g : ModularForm Γ k) (z : ℍ) : (f - g) z = f z - g z :=
  rfl
#align modular_form.sub_apply ModularForm.sub_apply

instance : AddCommGroup (ModularForm Γ k) :=
  FunLike.coe_injective.AddCommGroup _ rfl coe_add coe_neg coe_sub coe_smul coe_smul

/-- Additive coercion from `modular_form` to `ℍ → ℂ`. -/
@[simps]
def coeHom : ModularForm Γ k →+ ℍ → ℂ where
  toFun f := f
  map_zero' := coe_zero
  map_add' _ _ := rfl
#align modular_form.coe_hom ModularForm.coeHom

instance : Module ℂ (ModularForm Γ k) :=
  Function.Injective.module ℂ coeHom FunLike.coe_injective fun _ _ => rfl

instance : Inhabited (ModularForm Γ k) :=
  ⟨0⟩

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The modular form of weight `k_1 + k_2` given by the product of two modular forms of weights\n`k_1` and `k_2`. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `mul [])
      (Command.optDeclSig
       [(Term.implicitBinder "{" [`k_1 `k_2] [":" (termℤ "ℤ")] "}")
        (Term.implicitBinder
         "{"
         [`Γ]
         [":"
          (Term.app
           `Subgroup
           [(NumberTheory.ModularForms.Basic.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")])]
         "}")
        (Term.explicitBinder "(" [`f] [":" (Term.app `ModularForm [`Γ `k_1])] [] ")")
        (Term.explicitBinder "(" [`g] [":" (Term.app `ModularForm [`Γ `k_2])] [] ")")]
       [(Term.typeSpec ":" (Term.app `ModularForm [`Γ («term_+_» `k_1 "+" `k_2)]))])
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl (Term.letIdDecl `toFun [] [] ":=" («term_*_» `f "*" `g))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `slash_action_eq'
           [`A]
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Mathlib.Tactic.tacticSimp_rw__
                "simp_rw"
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `mul_slash_subgroup)
                  ","
                  (Tactic.rwRule [] `ModularFormClass.slash_action_eq)]
                 "]")
                [])]))))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `holo'
           []
           []
           ":="
           (Term.app (Term.proj (Term.proj `f "." `holo') "." `mul) [(Term.proj `g "." `holo')]))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `bdd_at_infty'
           [`A]
           []
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
                 ["using"
                  (Term.app
                   (Term.proj (Term.app `f.bdd_at_infty' [`A]) "." `mul)
                   [(Term.app `g.bdd_at_infty' [`A])])]))]))))))]
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
         [(Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            []
            []
            ["using"
             (Term.app
              (Term.proj (Term.app `f.bdd_at_infty' [`A]) "." `mul)
              [(Term.app `g.bdd_at_infty' [`A])])]))])))
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
        ["using"
         (Term.app
          (Term.proj (Term.app `f.bdd_at_infty' [`A]) "." `mul)
          [(Term.app `g.bdd_at_infty' [`A])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `f.bdd_at_infty' [`A]) "." `mul)
       [(Term.app `g.bdd_at_infty' [`A])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `g.bdd_at_infty' [`A])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `g.bdd_at_infty'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `g.bdd_at_infty' [`A]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `f.bdd_at_infty' [`A]) "." `mul)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `f.bdd_at_infty' [`A])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f.bdd_at_infty'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `f.bdd_at_infty' [`A]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.proj `f "." `holo') "." `mul) [(Term.proj `g "." `holo')])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `g "." `holo')
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj `f "." `holo') "." `mul)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `f "." `holo')
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `mul_slash_subgroup)
             ","
             (Tactic.rwRule [] `ModularFormClass.slash_action_eq)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `mul_slash_subgroup)
         ","
         (Tactic.rwRule [] `ModularFormClass.slash_action_eq)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ModularFormClass.slash_action_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_slash_subgroup
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `f "*" `g)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `ModularForm [`Γ («term_+_» `k_1 "+" `k_2)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `k_1 "+" `k_2)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k_2
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `k_1
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `k_1 "+" `k_2) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Γ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ModularForm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ModularForm [`Γ `k_2])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k_2
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Γ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ModularForm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ModularForm [`Γ `k_1])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k_1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Γ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ModularForm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Subgroup
       [(NumberTheory.ModularForms.Basic.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.Basic.«termSL(_,_)»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.Basic.«termSL(_,_)»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.ModularForms.Basic.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.Basic.«termSL(_,_)»', expected 'NumberTheory.ModularForms.Basic.termSL(_,_)._@.NumberTheory.ModularForms.Basic._hyg.927'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The modular form of weight `k_1 + k_2` given by the product of two modular forms of weights
    `k_1` and `k_2`. -/
  def
    mul
    { k_1 k_2 : ℤ } { Γ : Subgroup SL( 2 , ℤ ) } ( f : ModularForm Γ k_1 ) ( g : ModularForm Γ k_2 )
      : ModularForm Γ k_1 + k_2
    where
      toFun := f * g
        slash_action_eq' A := by simp_rw [ mul_slash_subgroup , ModularFormClass.slash_action_eq ]
        holo' := f . holo' . mul g . holo'
        bdd_at_infty' A := by simpa using f.bdd_at_infty' A . mul g.bdd_at_infty' A
#align modular_form.mul ModularForm.mul

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
      (Command.declId `mul_coe [])
      (Command.declSig
       [(Term.implicitBinder "{" [`k_1 `k_2] [":" (termℤ "ℤ")] "}")
        (Term.implicitBinder
         "{"
         [`Γ]
         [":"
          (Term.app
           `Subgroup
           [(NumberTheory.ModularForms.Basic.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")])]
         "}")
        (Term.explicitBinder "(" [`f] [":" (Term.app `ModularForm [`Γ `k_1])] [] ")")
        (Term.explicitBinder "(" [`g] [":" (Term.app `ModularForm [`Γ `k_2])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.typeAscription
          "("
          (Term.app (Term.proj `f "." `mul) [`g])
          ":"
          [(Term.arrow
            (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
            "→"
            (Data.Complex.Basic.termℂ "ℂ"))]
          ")")
         "="
         («term_*_» `f "*" `g))))
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
       (Term.typeAscription
        "("
        (Term.app (Term.proj `f "." `mul) [`g])
        ":"
        [(Term.arrow
          (UpperHalfPlane.Analysis.Complex.UpperHalfPlane.Basic.upper_half_plane "ℍ")
          "→"
          (Data.Complex.Basic.termℂ "ℂ"))]
        ")")
       "="
       («term_*_» `f "*" `g))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `f "*" `g)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription
       "("
       (Term.app (Term.proj `f "." `mul) [`g])
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
      (Term.app (Term.proj `f "." `mul) [`g])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `f "." `mul)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ModularForm [`Γ `k_2])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k_2
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Γ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ModularForm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ModularForm [`Γ `k_1])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k_1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Γ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ModularForm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Subgroup
       [(NumberTheory.ModularForms.Basic.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.Basic.«termSL(_,_)»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.Basic.«termSL(_,_)»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.ModularForms.Basic.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.Basic.«termSL(_,_)»', expected 'NumberTheory.ModularForms.Basic.termSL(_,_)._@.NumberTheory.ModularForms.Basic._hyg.927'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    mul_coe
    { k_1 k_2 : ℤ } { Γ : Subgroup SL( 2 , ℤ ) } ( f : ModularForm Γ k_1 ) ( g : ModularForm Γ k_2 )
      : ( f . mul g : ℍ → ℂ ) = f * g
    := rfl
#align modular_form.mul_coe ModularForm.mul_coe

instance : One (ModularForm Γ 0) :=
  ⟨{
      (1 :
        SlashInvariantForm Γ
          0) with
      holo' := fun x => mdifferentiable_at_const 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      bdd_at_infty' := fun A => by simpa using at_im_infty.const_bounded_at_filter (1 : ℂ) }⟩

@[simp]
theorem one_coe_eq_one : ((1 : ModularForm Γ 0) : ℍ → ℂ) = 1 :=
  rfl
#align modular_form.one_coe_eq_one ModularForm.one_coe_eq_one

end ModularForm

namespace CuspForm

open ModularForm

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.variable
     "variable"
     [(Term.implicitBinder "{" [`F] [":" (Term.type "Type" [(Level.hole "_")])] "}")
      (Term.implicitBinder
       "{"
       [`Γ]
       [":"
        (Term.app
         `Subgroup
         [(NumberTheory.ModularForms.Basic.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")])]
       "}")
      (Term.implicitBinder "{" [`k] [":" (termℤ "ℤ")] "}")])
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
       [(NumberTheory.ModularForms.Basic.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.Basic.«termSL(_,_)»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.Basic.«termSL(_,_)»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (NumberTheory.ModularForms.Basic.«termSL(_,_)» "SL(" (num "2") ", " (termℤ "ℤ") ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'NumberTheory.ModularForms.Basic.«termSL(_,_)»', expected 'NumberTheory.ModularForms.Basic.termSL(_,_)._@.NumberTheory.ModularForms.Basic._hyg.927'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.instBinder'-/-- failed to format: format: uncaught backtrack exception
variable { F : Type _ } { Γ : Subgroup SL( 2 , ℤ ) } { k : ℤ }

instance hasAdd : Add (CuspForm Γ k) :=
  ⟨fun f g =>
    { (f : SlashInvariantForm Γ k) + g with
      toFun := f + g
      holo' := f.holo'.add g.holo'
      zero_at_infty' := fun A => by simpa using (f.zero_at_infty' A).add (g.zero_at_infty' A) }⟩
#align cusp_form.has_add CuspForm.hasAdd

@[simp]
theorem coe_add (f g : CuspForm Γ k) : ⇑(f + g) = f + g :=
  rfl
#align cusp_form.coe_add CuspForm.coe_add

@[simp]
theorem add_apply (f g : CuspForm Γ k) (z : ℍ) : (f + g) z = f z + g z :=
  rfl
#align cusp_form.add_apply CuspForm.add_apply

instance hasZero : Zero (CuspForm Γ k) :=
  ⟨{ (0 : SlashInvariantForm Γ k) with
      toFun := 0
      holo' := fun _ => mdifferentiable_at_const 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      zero_at_infty' := by simpa using Filter.zero_zero_at_filter _ }⟩
#align cusp_form.has_zero CuspForm.hasZero

@[simp]
theorem coe_zero : ⇑(0 : CuspForm Γ k) = (0 : ℍ → ℂ) :=
  rfl
#align cusp_form.coe_zero CuspForm.coe_zero

@[simp]
theorem zero_apply (z : ℍ) : (0 : CuspForm Γ k) z = 0 :=
  rfl
#align cusp_form.zero_apply CuspForm.zero_apply

section

variable {α : Type _} [HasSmul α ℂ] [IsScalarTower α ℂ ℂ]

instance hasSmul : HasSmul α (CuspForm Γ k) :=
  ⟨fun c f =>
    { c • (f : SlashInvariantForm Γ k) with
      toFun := c • f
      holo' := by simpa using f.holo'.const_smul (c • (1 : ℂ))
      zero_at_infty' := fun A => by simpa using (f.zero_at_infty' A).smul (c • (1 : ℂ)) }⟩
#align cusp_form.has_smul CuspForm.hasSmul

@[simp]
theorem coe_smul (f : CuspForm Γ k) (n : α) : ⇑(n • f) = n • f :=
  rfl
#align cusp_form.coe_smul CuspForm.coe_smul

@[simp]
theorem smul_apply (f : CuspForm Γ k) (n : α) {z : ℍ} : (n • f) z = n • f z :=
  rfl
#align cusp_form.smul_apply CuspForm.smul_apply

end

instance hasNeg : Neg (CuspForm Γ k) :=
  ⟨fun f =>
    { -(f : SlashInvariantForm Γ k) with
      toFun := -f
      holo' := f.holo'.neg
      zero_at_infty' := fun A => by simpa using (f.zero_at_infty' A).neg }⟩
#align cusp_form.has_neg CuspForm.hasNeg

@[simp]
theorem coe_neg (f : CuspForm Γ k) : ⇑(-f) = -f :=
  rfl
#align cusp_form.coe_neg CuspForm.coe_neg

@[simp]
theorem neg_apply (f : CuspForm Γ k) (z : ℍ) : (-f) z = -f z :=
  rfl
#align cusp_form.neg_apply CuspForm.neg_apply

instance hasSub : Sub (CuspForm Γ k) :=
  ⟨fun f g => f + -g⟩
#align cusp_form.has_sub CuspForm.hasSub

@[simp]
theorem coe_sub (f g : CuspForm Γ k) : ⇑(f - g) = f - g :=
  rfl
#align cusp_form.coe_sub CuspForm.coe_sub

@[simp]
theorem sub_apply (f g : CuspForm Γ k) (z : ℍ) : (f - g) z = f z - g z :=
  rfl
#align cusp_form.sub_apply CuspForm.sub_apply

instance : AddCommGroup (CuspForm Γ k) :=
  FunLike.coe_injective.AddCommGroup _ rfl coe_add coe_neg coe_sub coe_smul coe_smul

/-- Additive coercion from `cusp_form` to `ℍ → ℂ`. -/
@[simps]
def coeHom : CuspForm Γ k →+ ℍ → ℂ where
  toFun f := f
  map_zero' := CuspForm.coe_zero
  map_add' _ _ := rfl
#align cusp_form.coe_hom CuspForm.coeHom

instance : Module ℂ (CuspForm Γ k) :=
  Function.Injective.module ℂ coeHom FunLike.coe_injective fun _ _ => rfl

instance : Inhabited (CuspForm Γ k) :=
  ⟨0⟩

instance (priority := 99) [CuspFormClass F Γ k] : ModularFormClass F Γ k
    where
  coe := FunLike.coe
  coe_injective' := FunLike.coe_injective'
  slash_action_eq := CuspFormClass.slash_action_eq
  holo := CuspFormClass.holo
  bdd_at_infty _ _ := (CuspFormClass.zero_at_infty _ _).BoundedAtFilter

end CuspForm

