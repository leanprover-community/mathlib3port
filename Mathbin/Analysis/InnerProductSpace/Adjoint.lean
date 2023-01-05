/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis, Heather Macbeth

! This file was ported from Lean 3 source module analysis.inner_product_space.adjoint
! leanprover-community/mathlib commit 6d0adfa76594f304b4650d098273d4366edeb61b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.InnerProductSpace.Dual
import Mathbin.Analysis.InnerProductSpace.PiL2

/-!
# Adjoint of operators on Hilbert spaces

Given an operator `A : E →L[𝕜] F`, where `E` and `F` are Hilbert spaces, its adjoint
`adjoint A : F →L[𝕜] E` is the unique operator such that `⟪x, A y⟫ = ⟪adjoint A x, y⟫` for all
`x` and `y`.

We then use this to put a C⋆-algebra structure on `E →L[𝕜] E` with the adjoint as the star
operation.

This construction is used to define an adjoint for linear maps (i.e. not continuous) between
finite dimensional spaces.

## Main definitions

* `continuous_linear_map.adjoint : (E →L[𝕜] F) ≃ₗᵢ⋆[𝕜] (F →L[𝕜] E)`: the adjoint of a continuous
  linear map, bundled as a conjugate-linear isometric equivalence.
* `linear_map.adjoint : (E →ₗ[𝕜] F) ≃ₗ⋆[𝕜] (F →ₗ[𝕜] E)`: the adjoint of a linear map between
  finite-dimensional spaces, this time only as a conjugate-linear equivalence, since there is no
  norm defined on these maps.

## Implementation notes

* The continuous conjugate-linear version `adjoint_aux` is only an intermediate
  definition and is not meant to be used outside this file.

## Tags

adjoint

-/


noncomputable section

open IsROrC

open ComplexConjugate

variable {𝕜 E F G : Type _} [IsROrC 𝕜]

variable [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] [InnerProductSpace 𝕜 G]

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/-! ### Adjoint operator -/


open InnerProductSpace

namespace ContinuousLinearMap

variable [CompleteSpace E] [CompleteSpace G]

/-- The adjoint, as a continuous conjugate-linear map.  This is only meant as an auxiliary
definition for the main definition `adjoint`, where this is bundled as a conjugate-linear isometric
equivalence. -/
def adjointAux : (E →L[𝕜] F) →L⋆[𝕜] F →L[𝕜] E :=
  (ContinuousLinearMap.compSL _ _ _ _ _ ((toDual 𝕜 E).symm : NormedSpace.Dual 𝕜 E →L⋆[𝕜] E)).comp
    (toSesqForm : (E →L[𝕜] F) →L[𝕜] F →L⋆[𝕜] NormedSpace.Dual 𝕜 E)
#align continuous_linear_map.adjoint_aux ContinuousLinearMap.adjointAux

@[simp]
theorem adjoint_aux_apply (A : E →L[𝕜] F) (x : F) :
    adjointAux A x = ((toDual 𝕜 E).symm : NormedSpace.Dual 𝕜 E → E) ((toSesqForm A) x) :=
  rfl
#align continuous_linear_map.adjoint_aux_apply ContinuousLinearMap.adjoint_aux_apply

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `adjoint_aux_inner_left [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`A]
         [":" (Topology.Algebra.Module.Basic.«term_→L[_]_» `E " →L[" `𝕜 "] " `F)]
         []
         ")")
        (Term.explicitBinder "(" [`x] [":" `E] [] ")")
        (Term.explicitBinder "(" [`y] [":" `F] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
          "⟪"
          (Term.app `adjointAux [`A `y])
          ", "
          `x
          "⟫")
         "="
         (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" `y ", " (Term.app `A [`x]) "⟫"))))
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
             [(Tactic.simpLemma [] [] `adjoint_aux_apply)
              ","
              (Tactic.simpLemma [] [] `to_dual_symm_apply)
              ","
              (Tactic.simpLemma [] [] `to_sesq_form_apply_coe)
              ","
              (Tactic.simpLemma [] [] `coe_comp')
              ","
              (Tactic.simpLemma [] [] `innerSL_apply_coe)]
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
         [(Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `adjoint_aux_apply)
             ","
             (Tactic.simpLemma [] [] `to_dual_symm_apply)
             ","
             (Tactic.simpLemma [] [] `to_sesq_form_apply_coe)
             ","
             (Tactic.simpLemma [] [] `coe_comp')
             ","
             (Tactic.simpLemma [] [] `innerSL_apply_coe)]
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
        [(Tactic.simpLemma [] [] `adjoint_aux_apply)
         ","
         (Tactic.simpLemma [] [] `to_dual_symm_apply)
         ","
         (Tactic.simpLemma [] [] `to_sesq_form_apply_coe)
         ","
         (Tactic.simpLemma [] [] `coe_comp')
         ","
         (Tactic.simpLemma [] [] `innerSL_apply_coe)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `innerSL_apply_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_comp'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `to_sesq_form_apply_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `to_dual_symm_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `adjoint_aux_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
        "⟪"
        (Term.app `adjointAux [`A `y])
        ", "
        `x
        "⟫")
       "="
       (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" `y ", " (Term.app `A [`x]) "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" `y ", " (Term.app `A [`x]) "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Adjoint.term⟪_,_⟫._@.Analysis.InnerProductSpace.Adjoint._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  adjoint_aux_inner_left
  ( A : E →L[ 𝕜 ] F ) ( x : E ) ( y : F ) : ⟪ adjointAux A y , x ⟫ = ⟪ y , A x ⟫
  :=
    by
      simp
        only
        [
          adjoint_aux_apply
            ,
            to_dual_symm_apply
            ,
            to_sesq_form_apply_coe
            ,
            coe_comp'
            ,
            innerSL_apply_coe
          ]
#align continuous_linear_map.adjoint_aux_inner_left ContinuousLinearMap.adjoint_aux_inner_left

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `adjoint_aux_inner_right [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`A]
         [":" (Topology.Algebra.Module.Basic.«term_→L[_]_» `E " →L[" `𝕜 "] " `F)]
         []
         ")")
        (Term.explicitBinder "(" [`x] [":" `E] [] ")")
        (Term.explicitBinder "(" [`y] [":" `F] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
          "⟪"
          `x
          ", "
          (Term.app `adjointAux [`A `y])
          "⟫")
         "="
         (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" (Term.app `A [`x]) ", " `y "⟫"))))
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
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `inner_conj_sym)
              ","
              (Tactic.rwRule [] `adjoint_aux_inner_left)
              ","
              (Tactic.rwRule [] `inner_conj_sym)]
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
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `inner_conj_sym)
             ","
             (Tactic.rwRule [] `adjoint_aux_inner_left)
             ","
             (Tactic.rwRule [] `inner_conj_sym)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `inner_conj_sym)
         ","
         (Tactic.rwRule [] `adjoint_aux_inner_left)
         ","
         (Tactic.rwRule [] `inner_conj_sym)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner_conj_sym
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `adjoint_aux_inner_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner_conj_sym
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
        "⟪"
        `x
        ", "
        (Term.app `adjointAux [`A `y])
        "⟫")
       "="
       (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" (Term.app `A [`x]) ", " `y "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" (Term.app `A [`x]) ", " `y "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Adjoint.term⟪_,_⟫._@.Analysis.InnerProductSpace.Adjoint._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  adjoint_aux_inner_right
  ( A : E →L[ 𝕜 ] F ) ( x : E ) ( y : F ) : ⟪ x , adjointAux A y ⟫ = ⟪ A x , y ⟫
  := by rw [ ← inner_conj_sym , adjoint_aux_inner_left , inner_conj_sym ]
#align continuous_linear_map.adjoint_aux_inner_right ContinuousLinearMap.adjoint_aux_inner_right

variable [CompleteSpace F]

theorem adjoint_aux_adjoint_aux (A : E →L[𝕜] F) : adjointAux (adjointAux A) = A :=
  by
  ext v
  refine' ext_inner_left 𝕜 fun w => _
  rw [adjoint_aux_inner_right, adjoint_aux_inner_left]
#align continuous_linear_map.adjoint_aux_adjoint_aux ContinuousLinearMap.adjoint_aux_adjoint_aux

@[simp]
theorem adjoint_aux_norm (A : E →L[𝕜] F) : ‖adjointAux A‖ = ‖A‖ :=
  by
  refine' le_antisymm _ _
  · refine' ContinuousLinearMap.op_norm_le_bound _ (norm_nonneg _) fun x => _
    rw [adjoint_aux_apply, LinearIsometryEquiv.norm_map]
    exact to_sesq_form_apply_norm_le
  · nth_rw_lhs 1 [← adjoint_aux_adjoint_aux A]
    refine' ContinuousLinearMap.op_norm_le_bound _ (norm_nonneg _) fun x => _
    rw [adjoint_aux_apply, LinearIsometryEquiv.norm_map]
    exact to_sesq_form_apply_norm_le
#align continuous_linear_map.adjoint_aux_norm ContinuousLinearMap.adjoint_aux_norm

/-- The adjoint of a bounded operator from Hilbert space E to Hilbert space F. -/
def adjoint : (E →L[𝕜] F) ≃ₗᵢ⋆[𝕜] F →L[𝕜] E :=
  LinearIsometryEquiv.ofSurjective { adjointAux with norm_map' := adjoint_aux_norm } fun A =>
    ⟨adjointAux A, adjoint_aux_adjoint_aux A⟩
#align continuous_linear_map.adjoint ContinuousLinearMap.adjoint

-- mathport name: adjoint
scoped[InnerProduct] postfix:1000 "†" => ContinuousLinearMap.adjoint

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "The fundamental property of the adjoint. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `adjoint_inner_left [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`A]
         [":" (Topology.Algebra.Module.Basic.«term_→L[_]_» `E " →L[" `𝕜 "] " `F)]
         []
         ")")
        (Term.explicitBinder "(" [`x] [":" `E] [] ")")
        (Term.explicitBinder "(" [`y] [":" `F] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
          "⟪"
          (Term.app (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") [`y])
          ", "
          `x
          "⟫")
         "="
         (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" `y ", " (Term.app `A [`x]) "⟫"))))
      (Command.declValSimple ":=" (Term.app `adjoint_aux_inner_left [`A `x `y]) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `adjoint_aux_inner_left [`A `x `y])
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
      `A
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `adjoint_aux_inner_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
        "⟪"
        (Term.app (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") [`y])
        ", "
        `x
        "⟫")
       "="
       (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" `y ", " (Term.app `A [`x]) "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" `y ", " (Term.app `A [`x]) "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Adjoint.term⟪_,_⟫._@.Analysis.InnerProductSpace.Adjoint._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The fundamental property of the adjoint. -/
  theorem
    adjoint_inner_left
    ( A : E →L[ 𝕜 ] F ) ( x : E ) ( y : F ) : ⟪ A † y , x ⟫ = ⟪ y , A x ⟫
    := adjoint_aux_inner_left A x y
#align continuous_linear_map.adjoint_inner_left ContinuousLinearMap.adjoint_inner_left

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "The fundamental property of the adjoint. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `adjoint_inner_right [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`A]
         [":" (Topology.Algebra.Module.Basic.«term_→L[_]_» `E " →L[" `𝕜 "] " `F)]
         []
         ")")
        (Term.explicitBinder "(" [`x] [":" `E] [] ")")
        (Term.explicitBinder "(" [`y] [":" `F] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
          "⟪"
          `x
          ", "
          (Term.app (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") [`y])
          "⟫")
         "="
         (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" (Term.app `A [`x]) ", " `y "⟫"))))
      (Command.declValSimple ":=" (Term.app `adjoint_aux_inner_right [`A `x `y]) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `adjoint_aux_inner_right [`A `x `y])
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
      `A
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `adjoint_aux_inner_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
        "⟪"
        `x
        ", "
        (Term.app (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") [`y])
        "⟫")
       "="
       (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" (Term.app `A [`x]) ", " `y "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" (Term.app `A [`x]) ", " `y "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Adjoint.term⟪_,_⟫._@.Analysis.InnerProductSpace.Adjoint._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The fundamental property of the adjoint. -/
  theorem
    adjoint_inner_right
    ( A : E →L[ 𝕜 ] F ) ( x : E ) ( y : F ) : ⟪ x , A † y ⟫ = ⟪ A x , y ⟫
    := adjoint_aux_inner_right A x y
#align continuous_linear_map.adjoint_inner_right ContinuousLinearMap.adjoint_inner_right

/-- The adjoint is involutive -/
@[simp]
theorem adjoint_adjoint (A : E →L[𝕜] F) : A†† = A :=
  adjoint_aux_adjoint_aux A
#align continuous_linear_map.adjoint_adjoint ContinuousLinearMap.adjoint_adjoint

/-- The adjoint of the composition of two operators is the composition of the two adjoints
in reverse order. -/
@[simp]
theorem adjoint_comp (A : F →L[𝕜] G) (B : E →L[𝕜] F) : (A ∘L B)† = B† ∘L A† :=
  by
  ext v
  refine' ext_inner_left 𝕜 fun w => _
  simp only [adjoint_inner_right, ContinuousLinearMap.coe_comp', Function.comp_apply]
#align continuous_linear_map.adjoint_comp ContinuousLinearMap.adjoint_comp

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `apply_norm_sq_eq_inner_adjoint_left [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`A]
         [":" (Topology.Algebra.Module.Basic.«term_→L[_]_» `E " →L[" `𝕜 "] " `E)]
         []
         ")")
        (Term.explicitBinder "(" [`x] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_^_»
          (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `A [`x]) "‖")
          "^"
          (num "2"))
         "="
         (Term.app
          `re
          [(Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
            "⟪"
            (Term.app
             («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
             [`x])
            ", "
            `x
            "⟫")]))))
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
              [`h []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
                  "⟪"
                  (Term.app
                   («term_*_»
                    (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†")
                    "*"
                    `A)
                   [`x])
                  ", "
                  `x
                  "⟫")
                 "="
                 (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
                  "⟪"
                  (Term.app `A [`x])
                  ", "
                  (Term.app `A [`x])
                  "⟫")))]
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
                    [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `adjoint_inner_left)]
                    "]")
                   [])
                  []
                  (Tactic.tacticRfl "rfl")]))))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `h)
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app `inner_self_eq_norm_sq [(Term.hole "_")]))]
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
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
                 "⟪"
                 (Term.app
                  («term_*_»
                   (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†")
                   "*"
                   `A)
                  [`x])
                 ", "
                 `x
                 "⟫")
                "="
                (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
                 "⟪"
                 (Term.app `A [`x])
                 ", "
                 (Term.app `A [`x])
                 "⟫")))]
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
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `adjoint_inner_left)]
                   "]")
                  [])
                 []
                 (Tactic.tacticRfl "rfl")]))))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `h)
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app `inner_self_eq_norm_sq [(Term.hole "_")]))]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `h)
         ","
         (Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app `inner_self_eq_norm_sq [(Term.hole "_")]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `inner_self_eq_norm_sq [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `inner_self_eq_norm_sq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`h []]
         [(Term.typeSpec
           ":"
           («term_=_»
            (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
             "⟪"
             (Term.app
              («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
              [`x])
             ", "
             `x
             "⟫")
            "="
            (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
             "⟪"
             (Term.app `A [`x])
             ", "
             (Term.app `A [`x])
             "⟫")))]
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
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `adjoint_inner_left)]
               "]")
              [])
             []
             (Tactic.tacticRfl "rfl")]))))))
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
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `adjoint_inner_left)]
            "]")
           [])
          []
          (Tactic.tacticRfl "rfl")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `adjoint_inner_left)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `adjoint_inner_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
        "⟪"
        (Term.app
         («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
         [`x])
        ", "
        `x
        "⟫")
       "="
       (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
        "⟪"
        (Term.app `A [`x])
        ", "
        (Term.app `A [`x])
        "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
       "⟪"
       (Term.app `A [`x])
       ", "
       (Term.app `A [`x])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Adjoint.term⟪_,_⟫._@.Analysis.InnerProductSpace.Adjoint._hyg.6'
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
  apply_norm_sq_eq_inner_adjoint_left
  ( A : E →L[ 𝕜 ] E ) ( x : E ) : ‖ A x ‖ ^ 2 = re ⟪ A † * A x , x ⟫
  :=
    by
      have h : ⟪ A † * A x , x ⟫ = ⟪ A x , A x ⟫ := by rw [ ← adjoint_inner_left ] rfl
        rw [ h , ← inner_self_eq_norm_sq _ ]
#align
  continuous_linear_map.apply_norm_sq_eq_inner_adjoint_left ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `apply_norm_eq_sqrt_inner_adjoint_left [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`A]
         [":" (Topology.Algebra.Module.Basic.«term_→L[_]_» `E " →L[" `𝕜 "] " `E)]
         []
         ")")
        (Term.explicitBinder "(" [`x] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `A [`x]) "‖")
         "="
         (Term.app
          `Real.sqrt
          [(Term.app
            `re
            [(Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
              "⟪"
              (Term.app
               («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
               [`x])
              ", "
              `x
              "⟫")])]))))
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
               `apply_norm_sq_eq_inner_adjoint_left)
              ","
              (Tactic.rwRule
               []
               (Term.app `Real.sqrt_sq [(Term.app `norm_nonneg [(Term.hole "_")])]))]
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
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `apply_norm_sq_eq_inner_adjoint_left)
             ","
             (Tactic.rwRule
              []
              (Term.app `Real.sqrt_sq [(Term.app `norm_nonneg [(Term.hole "_")])]))]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `apply_norm_sq_eq_inner_adjoint_left)
         ","
         (Tactic.rwRule [] (Term.app `Real.sqrt_sq [(Term.app `norm_nonneg [(Term.hole "_")])]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Real.sqrt_sq [(Term.app `norm_nonneg [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `norm_nonneg [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `norm_nonneg [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Real.sqrt_sq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `apply_norm_sq_eq_inner_adjoint_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `A [`x]) "‖")
       "="
       (Term.app
        `Real.sqrt
        [(Term.app
          `re
          [(Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
            "⟪"
            (Term.app
             («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
             [`x])
            ", "
            `x
            "⟫")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Real.sqrt
       [(Term.app
         `re
         [(Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
           "⟪"
           (Term.app
            («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
            [`x])
           ", "
           `x
           "⟫")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `re
       [(Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
         "⟪"
         (Term.app
          («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
          [`x])
         ", "
         `x
         "⟫")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
       "⟪"
       (Term.app
        («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
        [`x])
       ", "
       `x
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Adjoint.term⟪_,_⟫._@.Analysis.InnerProductSpace.Adjoint._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  apply_norm_eq_sqrt_inner_adjoint_left
  ( A : E →L[ 𝕜 ] E ) ( x : E ) : ‖ A x ‖ = Real.sqrt re ⟪ A † * A x , x ⟫
  := by rw [ ← apply_norm_sq_eq_inner_adjoint_left , Real.sqrt_sq norm_nonneg _ ]
#align
  continuous_linear_map.apply_norm_eq_sqrt_inner_adjoint_left ContinuousLinearMap.apply_norm_eq_sqrt_inner_adjoint_left

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `apply_norm_sq_eq_inner_adjoint_right [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`A]
         [":" (Topology.Algebra.Module.Basic.«term_→L[_]_» `E " →L[" `𝕜 "] " `E)]
         []
         ")")
        (Term.explicitBinder "(" [`x] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_^_»
          (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `A [`x]) "‖")
          "^"
          (num "2"))
         "="
         (Term.app
          `re
          [(Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
            "⟪"
            `x
            ", "
            (Term.app
             («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
             [`x])
            "⟫")]))))
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
              [`h []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
                  "⟪"
                  `x
                  ", "
                  (Term.app
                   («term_*_»
                    (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†")
                    "*"
                    `A)
                   [`x])
                  "⟫")
                 "="
                 (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
                  "⟪"
                  (Term.app `A [`x])
                  ", "
                  (Term.app `A [`x])
                  "⟫")))]
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
                    [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `adjoint_inner_right)]
                    "]")
                   [])
                  []
                  (Tactic.tacticRfl "rfl")]))))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `h)
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app `inner_self_eq_norm_sq [(Term.hole "_")]))]
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
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
                 "⟪"
                 `x
                 ", "
                 (Term.app
                  («term_*_»
                   (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†")
                   "*"
                   `A)
                  [`x])
                 "⟫")
                "="
                (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
                 "⟪"
                 (Term.app `A [`x])
                 ", "
                 (Term.app `A [`x])
                 "⟫")))]
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
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `adjoint_inner_right)]
                   "]")
                  [])
                 []
                 (Tactic.tacticRfl "rfl")]))))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `h)
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app `inner_self_eq_norm_sq [(Term.hole "_")]))]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `h)
         ","
         (Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app `inner_self_eq_norm_sq [(Term.hole "_")]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `inner_self_eq_norm_sq [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `inner_self_eq_norm_sq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`h []]
         [(Term.typeSpec
           ":"
           («term_=_»
            (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
             "⟪"
             `x
             ", "
             (Term.app
              («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
              [`x])
             "⟫")
            "="
            (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
             "⟪"
             (Term.app `A [`x])
             ", "
             (Term.app `A [`x])
             "⟫")))]
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
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `adjoint_inner_right)]
               "]")
              [])
             []
             (Tactic.tacticRfl "rfl")]))))))
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
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `adjoint_inner_right)]
            "]")
           [])
          []
          (Tactic.tacticRfl "rfl")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `adjoint_inner_right)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `adjoint_inner_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
        "⟪"
        `x
        ", "
        (Term.app
         («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
         [`x])
        "⟫")
       "="
       (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
        "⟪"
        (Term.app `A [`x])
        ", "
        (Term.app `A [`x])
        "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
       "⟪"
       (Term.app `A [`x])
       ", "
       (Term.app `A [`x])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Adjoint.term⟪_,_⟫._@.Analysis.InnerProductSpace.Adjoint._hyg.6'
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
  apply_norm_sq_eq_inner_adjoint_right
  ( A : E →L[ 𝕜 ] E ) ( x : E ) : ‖ A x ‖ ^ 2 = re ⟪ x , A † * A x ⟫
  :=
    by
      have h : ⟪ x , A † * A x ⟫ = ⟪ A x , A x ⟫ := by rw [ ← adjoint_inner_right ] rfl
        rw [ h , ← inner_self_eq_norm_sq _ ]
#align
  continuous_linear_map.apply_norm_sq_eq_inner_adjoint_right ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `apply_norm_eq_sqrt_inner_adjoint_right [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`A]
         [":" (Topology.Algebra.Module.Basic.«term_→L[_]_» `E " →L[" `𝕜 "] " `E)]
         []
         ")")
        (Term.explicitBinder "(" [`x] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `A [`x]) "‖")
         "="
         (Term.app
          `Real.sqrt
          [(Term.app
            `re
            [(Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
              "⟪"
              `x
              ", "
              (Term.app
               («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
               [`x])
              "⟫")])]))))
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
               `apply_norm_sq_eq_inner_adjoint_right)
              ","
              (Tactic.rwRule
               []
               (Term.app `Real.sqrt_sq [(Term.app `norm_nonneg [(Term.hole "_")])]))]
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
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              `apply_norm_sq_eq_inner_adjoint_right)
             ","
             (Tactic.rwRule
              []
              (Term.app `Real.sqrt_sq [(Term.app `norm_nonneg [(Term.hole "_")])]))]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `apply_norm_sq_eq_inner_adjoint_right)
         ","
         (Tactic.rwRule [] (Term.app `Real.sqrt_sq [(Term.app `norm_nonneg [(Term.hole "_")])]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Real.sqrt_sq [(Term.app `norm_nonneg [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `norm_nonneg [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `norm_nonneg [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Real.sqrt_sq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `apply_norm_sq_eq_inner_adjoint_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `A [`x]) "‖")
       "="
       (Term.app
        `Real.sqrt
        [(Term.app
          `re
          [(Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
            "⟪"
            `x
            ", "
            (Term.app
             («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
             [`x])
            "⟫")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Real.sqrt
       [(Term.app
         `re
         [(Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
           "⟪"
           `x
           ", "
           (Term.app
            («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
            [`x])
           "⟫")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `re
       [(Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
         "⟪"
         `x
         ", "
         (Term.app
          («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
          [`x])
         "⟫")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
       "⟪"
       `x
       ", "
       (Term.app
        («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
        [`x])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Adjoint.term⟪_,_⟫._@.Analysis.InnerProductSpace.Adjoint._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  apply_norm_eq_sqrt_inner_adjoint_right
  ( A : E →L[ 𝕜 ] E ) ( x : E ) : ‖ A x ‖ = Real.sqrt re ⟪ x , A † * A x ⟫
  := by rw [ ← apply_norm_sq_eq_inner_adjoint_right , Real.sqrt_sq norm_nonneg _ ]
#align
  continuous_linear_map.apply_norm_eq_sqrt_inner_adjoint_right ContinuousLinearMap.apply_norm_eq_sqrt_inner_adjoint_right

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The adjoint is unique: a map `A` is the adjoint of `B` iff it satisfies `⟪A x, y⟫ = ⟪x, B y⟫`\nfor all `x` and `y`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `eq_adjoint_iff [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`A]
         [":" (Topology.Algebra.Module.Basic.«term_→L[_]_» `E " →L[" `𝕜 "] " `F)]
         []
         ")")
        (Term.explicitBinder
         "("
         [`B]
         [":" (Topology.Algebra.Module.Basic.«term_→L[_]_» `F " →L[" `𝕜 "] " `E)]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_=_» `A "=" (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `B "†"))
         "↔"
         (Term.forall
          "∀"
          [`x `y]
          []
          ","
          («term_=_»
           (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" (Term.app `A [`x]) ", " `y "⟫")
           "="
           (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" `x ", " (Term.app `B [`y]) "⟫"))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.anonymousCtor
             "⟨"
             [(Term.fun
               "fun"
               (Term.basicFun
                [`h `x `y]
                []
                "=>"
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `adjoint_inner_left)]
                      "]")
                     [])])))))
              ","
              (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))]
             "⟩"))
           []
           (Std.Tactic.Ext.«tacticExt___:_»
            "ext"
            [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))]
            [])
           []
           (Tactic.exact
            "exact"
            (Term.app
             `ext_inner_right
             [`𝕜
              (Term.fun
               "fun"
               (Term.basicFun
                [`y]
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
                      [(Tactic.simpLemma [] [] `adjoint_inner_left)
                       ","
                       (Tactic.simpLemma [] [] (Term.app `h [`x `y]))]
                      "]"]
                     [])])))))]))])))
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
           (Term.anonymousCtor
            "⟨"
            [(Term.fun
              "fun"
              (Term.basicFun
               [`h `x `y]
               []
               "=>"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `adjoint_inner_left)]
                     "]")
                    [])])))))
             ","
             (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))]
            "⟩"))
          []
          (Std.Tactic.Ext.«tacticExt___:_»
           "ext"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))]
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            `ext_inner_right
            [`𝕜
             (Term.fun
              "fun"
              (Term.basicFun
               [`y]
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
                     [(Tactic.simpLemma [] [] `adjoint_inner_left)
                      ","
                      (Tactic.simpLemma [] [] (Term.app `h [`x `y]))]
                     "]"]
                    [])])))))]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `ext_inner_right
        [`𝕜
         (Term.fun
          "fun"
          (Term.basicFun
           [`y]
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
                 [(Tactic.simpLemma [] [] `adjoint_inner_left)
                  ","
                  (Tactic.simpLemma [] [] (Term.app `h [`x `y]))]
                 "]"]
                [])])))))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `ext_inner_right
       [`𝕜
        (Term.fun
         "fun"
         (Term.basicFun
          [`y]
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
                [(Tactic.simpLemma [] [] `adjoint_inner_left)
                 ","
                 (Tactic.simpLemma [] [] (Term.app `h [`x `y]))]
                "]"]
               [])])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`y]
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
              [(Tactic.simpLemma [] [] `adjoint_inner_left)
               ","
               (Tactic.simpLemma [] [] (Term.app `h [`x `y]))]
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
            [(Tactic.simpLemma [] [] `adjoint_inner_left)
             ","
             (Tactic.simpLemma [] [] (Term.app `h [`x `y]))]
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
        [(Tactic.simpLemma [] [] `adjoint_inner_left)
         ","
         (Tactic.simpLemma [] [] (Term.app `h [`x `y]))]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h [`x `y])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `adjoint_inner_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `𝕜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ext_inner_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_»
       "ext"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [(Term.fun
          "fun"
          (Term.basicFun
           [`h `x `y]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `adjoint_inner_left)]
                 "]")
                [])])))))
         ","
         (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [`h `x `y]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `adjoint_inner_left)]
                "]")
               [])])))))
        ","
        (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`h `x `y]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `adjoint_inner_left)]
              "]")
             [])])))))
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
            [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `adjoint_inner_left)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `adjoint_inner_left)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `adjoint_inner_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_=_» `A "=" (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `B "†"))
       "↔"
       (Term.forall
        "∀"
        [`x `y]
        []
        ","
        («term_=_»
         (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" (Term.app `A [`x]) ", " `y "⟫")
         "="
         (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" `x ", " (Term.app `B [`y]) "⟫"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`x `y]
       []
       ","
       («term_=_»
        (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" (Term.app `A [`x]) ", " `y "⟫")
        "="
        (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" `x ", " (Term.app `B [`y]) "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" (Term.app `A [`x]) ", " `y "⟫")
       "="
       (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" `x ", " (Term.app `B [`y]) "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" `x ", " (Term.app `B [`y]) "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Adjoint.term⟪_,_⟫._@.Analysis.InnerProductSpace.Adjoint._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The adjoint is unique: a map `A` is the adjoint of `B` iff it satisfies `⟪A x, y⟫ = ⟪x, B y⟫`
    for all `x` and `y`. -/
  theorem
    eq_adjoint_iff
    ( A : E →L[ 𝕜 ] F ) ( B : F →L[ 𝕜 ] E ) : A = B † ↔ ∀ x y , ⟪ A x , y ⟫ = ⟪ x , B y ⟫
    :=
      by
        refine' ⟨ fun h x y => by rw [ h , adjoint_inner_left ] , fun h => _ ⟩
          ext x
          exact ext_inner_right 𝕜 fun y => by simp only [ adjoint_inner_left , h x y ]
#align continuous_linear_map.eq_adjoint_iff ContinuousLinearMap.eq_adjoint_iff

@[simp]
theorem adjoint_id : (ContinuousLinearMap.id 𝕜 E).adjoint = ContinuousLinearMap.id 𝕜 E :=
  by
  refine' Eq.symm _
  rw [eq_adjoint_iff]
  simp
#align continuous_linear_map.adjoint_id ContinuousLinearMap.adjoint_id

theorem Submodule.adjoint_subtypeL (U : Submodule 𝕜 E) [CompleteSpace U] :
    U.subtypeL† = orthogonalProjection U := by
  symm
  rw [eq_adjoint_iff]
  intro x u
  rw [U.coe_inner, inner_orthogonal_projection_left_eq_right,
    orthogonal_projection_mem_subspace_eq_self]
  rfl
#align submodule.adjoint_subtypeL Submodule.adjoint_subtypeL

theorem Submodule.adjoint_orthogonal_projection (U : Submodule 𝕜 E) [CompleteSpace U] :
    (orthogonalProjection U : E →L[𝕜] U)† = U.subtypeL := by
  rw [← U.adjoint_subtypeL, adjoint_adjoint]
#align submodule.adjoint_orthogonal_projection Submodule.adjoint_orthogonal_projection

/-- `E →L[𝕜] E` is a star algebra with the adjoint as the star operation. -/
instance : HasStar (E →L[𝕜] E) :=
  ⟨adjoint⟩

instance : HasInvolutiveStar (E →L[𝕜] E) :=
  ⟨adjoint_adjoint⟩

instance : StarSemigroup (E →L[𝕜] E) :=
  ⟨adjoint_comp⟩

instance : StarRing (E →L[𝕜] E) :=
  ⟨LinearIsometryEquiv.map_add adjoint⟩

instance : StarModule 𝕜 (E →L[𝕜] E) :=
  ⟨LinearIsometryEquiv.map_smulₛₗ adjoint⟩

theorem star_eq_adjoint (A : E →L[𝕜] E) : star A = A† :=
  rfl
#align continuous_linear_map.star_eq_adjoint ContinuousLinearMap.star_eq_adjoint

/-- A continuous linear operator is self-adjoint iff it is equal to its adjoint. -/
theorem is_self_adjoint_iff' {A : E →L[𝕜] E} : IsSelfAdjoint A ↔ A.adjoint = A :=
  Iff.rfl
#align continuous_linear_map.is_self_adjoint_iff' ContinuousLinearMap.is_self_adjoint_iff'

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
        (Term.app `CstarRing [(Topology.Algebra.Module.Basic.«term_→L[_]_» `E " →L[" `𝕜 "] " `E)])))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [(Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.intro "intro" [`A])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `star_eq_adjoint)] "]")
              [])
             []
             (Tactic.refine' "refine'" (Term.app `le_antisymm [(Term.hole "_") (Term.hole "_")]))
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(calcTactic
                "calc"
                (calcStep
                 («term_≤_»
                  (Analysis.Normed.Group.Basic.«term‖_‖»
                   "‖"
                   («term_*_»
                    (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†")
                    "*"
                    `A)
                   "‖")
                  "≤"
                  («term_*_»
                   (Analysis.Normed.Group.Basic.«term‖_‖»
                    "‖"
                    (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†")
                    "‖")
                   "*"
                   (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `A "‖")))
                 ":="
                 (Term.app `op_norm_comp_le [(Term.hole "_") (Term.hole "_")]))
                [(calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   («term_*_»
                    (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `A "‖")
                    "*"
                    (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `A "‖")))
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `LinearIsometryEquiv.norm_map)] "]")
                       [])]))))])])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sq)
                  ","
                  (Tactic.rwRule
                   [(patternIgnore (token.«← » "←"))]
                   (Term.app `Real.sqrt_le_sqrt_iff [(Term.app `norm_nonneg [(Term.hole "_")])]))
                  ","
                  (Tactic.rwRule
                   []
                   (Term.app `Real.sqrt_sq [(Term.app `norm_nonneg [(Term.hole "_")])]))]
                 "]")
                [])
               []
               (Tactic.refine'
                "refine'"
                (Term.app
                 `op_norm_le_bound
                 [(Term.hole "_")
                  (Term.app `Real.sqrt_nonneg [(Term.hole "_")])
                  (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))]))
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  []
                  []
                  ":="
                  (calc
                   "calc"
                   (calcStep
                    («term_≤_»
                     (Term.app
                      `re
                      [(Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
                        "⟪"
                        (Term.app
                         («term_*_»
                          (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†")
                          "*"
                          `A)
                         [`x])
                        ", "
                        `x
                        "⟫")])
                     "≤"
                     («term_*_»
                      (Analysis.Normed.Group.Basic.«term‖_‖»
                       "‖"
                       (Term.app
                        («term_*_»
                         (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†")
                         "*"
                         `A)
                        [`x])
                       "‖")
                      "*"
                      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))
                    ":="
                    (Term.app `re_inner_le_norm [(Term.hole "_") (Term.hole "_")]))
                   [(calcStep
                     («term_≤_»
                      (Term.hole "_")
                      "≤"
                      («term_*_»
                       («term_*_»
                        (Analysis.Normed.Group.Basic.«term‖_‖»
                         "‖"
                         («term_*_»
                          (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†")
                          "*"
                          `A)
                         "‖")
                        "*"
                        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))
                       "*"
                       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))
                     ":="
                     (Term.app
                      `mul_le_mul_of_nonneg_right
                      [(Term.app `le_op_norm [(Term.hole "_") (Term.hole "_")])
                       (Term.app `norm_nonneg [(Term.hole "_")])]))]))))
               []
               (calcTactic
                "calc"
                (calcStep
                 («term_=_»
                  (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `A [`x]) "‖")
                  "="
                  (Term.app
                   `Real.sqrt
                   [(Term.app
                     `re
                     [(Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
                       "⟪"
                       (Term.app
                        («term_*_»
                         (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†")
                         "*"
                         `A)
                        [`x])
                       ", "
                       `x
                       "⟫")])]))
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
                       [(Tactic.rwRule [] `apply_norm_eq_sqrt_inner_adjoint_left)]
                       "]")
                      [])]))))
                [(calcStep
                  («term_≤_»
                   (Term.hole "_")
                   "≤"
                   (Term.app
                    `Real.sqrt
                    [(«term_*_»
                      («term_*_»
                       (Analysis.Normed.Group.Basic.«term‖_‖»
                        "‖"
                        («term_*_»
                         (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†")
                         "*"
                         `A)
                        "‖")
                       "*"
                       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))
                      "*"
                      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))]))
                  ":="
                  (Term.app `Real.sqrt_le_sqrt [`this]))
                 (calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   («term_*_»
                    (Term.app
                     `Real.sqrt
                     [(Analysis.Normed.Group.Basic.«term‖_‖»
                       "‖"
                       («term_*_»
                        (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†")
                        "*"
                        `A)
                       "‖")])
                    "*"
                    (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))
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
                        [(Tactic.rwRule [] `mul_assoc)
                         ","
                         (Tactic.rwRule
                          []
                          (Term.app `Real.sqrt_mul [(Term.app `norm_nonneg [(Term.hole "_")])]))
                         ","
                         (Tactic.rwRule
                          []
                          (Term.app
                           `Real.sqrt_mul_self
                           [(Term.app `norm_nonneg [(Term.hole "_")])]))]
                        "]")
                       [])]))))])])])))]
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
           [(Tactic.intro "intro" [`A])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `star_eq_adjoint)] "]")
             [])
            []
            (Tactic.refine' "refine'" (Term.app `le_antisymm [(Term.hole "_") (Term.hole "_")]))
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(calcTactic
               "calc"
               (calcStep
                («term_≤_»
                 (Analysis.Normed.Group.Basic.«term‖_‖»
                  "‖"
                  («term_*_»
                   (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†")
                   "*"
                   `A)
                  "‖")
                 "≤"
                 («term_*_»
                  (Analysis.Normed.Group.Basic.«term‖_‖»
                   "‖"
                   (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†")
                   "‖")
                  "*"
                  (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `A "‖")))
                ":="
                (Term.app `op_norm_comp_le [(Term.hole "_") (Term.hole "_")]))
               [(calcStep
                 («term_=_»
                  (Term.hole "_")
                  "="
                  («term_*_»
                   (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `A "‖")
                   "*"
                   (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `A "‖")))
                 ":="
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `LinearIsometryEquiv.norm_map)] "]")
                      [])]))))])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sq)
                 ","
                 (Tactic.rwRule
                  [(patternIgnore (token.«← » "←"))]
                  (Term.app `Real.sqrt_le_sqrt_iff [(Term.app `norm_nonneg [(Term.hole "_")])]))
                 ","
                 (Tactic.rwRule
                  []
                  (Term.app `Real.sqrt_sq [(Term.app `norm_nonneg [(Term.hole "_")])]))]
                "]")
               [])
              []
              (Tactic.refine'
               "refine'"
               (Term.app
                `op_norm_le_bound
                [(Term.hole "_")
                 (Term.app `Real.sqrt_nonneg [(Term.hole "_")])
                 (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))]))
              []
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 []
                 []
                 ":="
                 (calc
                  "calc"
                  (calcStep
                   («term_≤_»
                    (Term.app
                     `re
                     [(Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
                       "⟪"
                       (Term.app
                        («term_*_»
                         (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†")
                         "*"
                         `A)
                        [`x])
                       ", "
                       `x
                       "⟫")])
                    "≤"
                    («term_*_»
                     (Analysis.Normed.Group.Basic.«term‖_‖»
                      "‖"
                      (Term.app
                       («term_*_»
                        (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†")
                        "*"
                        `A)
                       [`x])
                      "‖")
                     "*"
                     (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))
                   ":="
                   (Term.app `re_inner_le_norm [(Term.hole "_") (Term.hole "_")]))
                  [(calcStep
                    («term_≤_»
                     (Term.hole "_")
                     "≤"
                     («term_*_»
                      («term_*_»
                       (Analysis.Normed.Group.Basic.«term‖_‖»
                        "‖"
                        («term_*_»
                         (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†")
                         "*"
                         `A)
                        "‖")
                       "*"
                       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))
                      "*"
                      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))
                    ":="
                    (Term.app
                     `mul_le_mul_of_nonneg_right
                     [(Term.app `le_op_norm [(Term.hole "_") (Term.hole "_")])
                      (Term.app `norm_nonneg [(Term.hole "_")])]))]))))
              []
              (calcTactic
               "calc"
               (calcStep
                («term_=_»
                 (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `A [`x]) "‖")
                 "="
                 (Term.app
                  `Real.sqrt
                  [(Term.app
                    `re
                    [(Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
                      "⟪"
                      (Term.app
                       («term_*_»
                        (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†")
                        "*"
                        `A)
                       [`x])
                      ", "
                      `x
                      "⟫")])]))
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
                      [(Tactic.rwRule [] `apply_norm_eq_sqrt_inner_adjoint_left)]
                      "]")
                     [])]))))
               [(calcStep
                 («term_≤_»
                  (Term.hole "_")
                  "≤"
                  (Term.app
                   `Real.sqrt
                   [(«term_*_»
                     («term_*_»
                      (Analysis.Normed.Group.Basic.«term‖_‖»
                       "‖"
                       («term_*_»
                        (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†")
                        "*"
                        `A)
                       "‖")
                      "*"
                      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))
                     "*"
                     (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))]))
                 ":="
                 (Term.app `Real.sqrt_le_sqrt [`this]))
                (calcStep
                 («term_=_»
                  (Term.hole "_")
                  "="
                  («term_*_»
                   (Term.app
                    `Real.sqrt
                    [(Analysis.Normed.Group.Basic.«term‖_‖»
                      "‖"
                      («term_*_»
                       (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†")
                       "*"
                       `A)
                      "‖")])
                   "*"
                   (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))
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
                       [(Tactic.rwRule [] `mul_assoc)
                        ","
                        (Tactic.rwRule
                         []
                         (Term.app `Real.sqrt_mul [(Term.app `norm_nonneg [(Term.hole "_")])]))
                        ","
                        (Tactic.rwRule
                         []
                         (Term.app
                          `Real.sqrt_mul_self
                          [(Term.app `norm_nonneg [(Term.hole "_")])]))]
                       "]")
                      [])]))))])])])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intro "intro" [`A])
          []
          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `star_eq_adjoint)] "]") [])
          []
          (Tactic.refine' "refine'" (Term.app `le_antisymm [(Term.hole "_") (Term.hole "_")]))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(calcTactic
             "calc"
             (calcStep
              («term_≤_»
               (Analysis.Normed.Group.Basic.«term‖_‖»
                "‖"
                («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
                "‖")
               "≤"
               («term_*_»
                (Analysis.Normed.Group.Basic.«term‖_‖»
                 "‖"
                 (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†")
                 "‖")
                "*"
                (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `A "‖")))
              ":="
              (Term.app `op_norm_comp_le [(Term.hole "_") (Term.hole "_")]))
             [(calcStep
               («term_=_»
                (Term.hole "_")
                "="
                («term_*_»
                 (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `A "‖")
                 "*"
                 (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `A "‖")))
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `LinearIsometryEquiv.norm_map)] "]")
                    [])]))))])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sq)
               ","
               (Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.app `Real.sqrt_le_sqrt_iff [(Term.app `norm_nonneg [(Term.hole "_")])]))
               ","
               (Tactic.rwRule
                []
                (Term.app `Real.sqrt_sq [(Term.app `norm_nonneg [(Term.hole "_")])]))]
              "]")
             [])
            []
            (Tactic.refine'
             "refine'"
             (Term.app
              `op_norm_le_bound
              [(Term.hole "_")
               (Term.app `Real.sqrt_nonneg [(Term.hole "_")])
               (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))]))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               []
               ":="
               (calc
                "calc"
                (calcStep
                 («term_≤_»
                  (Term.app
                   `re
                   [(Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
                     "⟪"
                     (Term.app
                      («term_*_»
                       (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†")
                       "*"
                       `A)
                      [`x])
                     ", "
                     `x
                     "⟫")])
                  "≤"
                  («term_*_»
                   (Analysis.Normed.Group.Basic.«term‖_‖»
                    "‖"
                    (Term.app
                     («term_*_»
                      (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†")
                      "*"
                      `A)
                     [`x])
                    "‖")
                   "*"
                   (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))
                 ":="
                 (Term.app `re_inner_le_norm [(Term.hole "_") (Term.hole "_")]))
                [(calcStep
                  («term_≤_»
                   (Term.hole "_")
                   "≤"
                   («term_*_»
                    («term_*_»
                     (Analysis.Normed.Group.Basic.«term‖_‖»
                      "‖"
                      («term_*_»
                       (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†")
                       "*"
                       `A)
                      "‖")
                     "*"
                     (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))
                    "*"
                    (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))
                  ":="
                  (Term.app
                   `mul_le_mul_of_nonneg_right
                   [(Term.app `le_op_norm [(Term.hole "_") (Term.hole "_")])
                    (Term.app `norm_nonneg [(Term.hole "_")])]))]))))
            []
            (calcTactic
             "calc"
             (calcStep
              («term_=_»
               (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `A [`x]) "‖")
               "="
               (Term.app
                `Real.sqrt
                [(Term.app
                  `re
                  [(Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
                    "⟪"
                    (Term.app
                     («term_*_»
                      (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†")
                      "*"
                      `A)
                     [`x])
                    ", "
                    `x
                    "⟫")])]))
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
                    [(Tactic.rwRule [] `apply_norm_eq_sqrt_inner_adjoint_left)]
                    "]")
                   [])]))))
             [(calcStep
               («term_≤_»
                (Term.hole "_")
                "≤"
                (Term.app
                 `Real.sqrt
                 [(«term_*_»
                   («term_*_»
                    (Analysis.Normed.Group.Basic.«term‖_‖»
                     "‖"
                     («term_*_»
                      (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†")
                      "*"
                      `A)
                     "‖")
                    "*"
                    (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))
                   "*"
                   (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))]))
               ":="
               (Term.app `Real.sqrt_le_sqrt [`this]))
              (calcStep
               («term_=_»
                (Term.hole "_")
                "="
                («term_*_»
                 (Term.app
                  `Real.sqrt
                  [(Analysis.Normed.Group.Basic.«term‖_‖»
                    "‖"
                    («term_*_»
                     (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†")
                     "*"
                     `A)
                    "‖")])
                 "*"
                 (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))
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
                     [(Tactic.rwRule [] `mul_assoc)
                      ","
                      (Tactic.rwRule
                       []
                       (Term.app `Real.sqrt_mul [(Term.app `norm_nonneg [(Term.hole "_")])]))
                      ","
                      (Tactic.rwRule
                       []
                       (Term.app `Real.sqrt_mul_self [(Term.app `norm_nonneg [(Term.hole "_")])]))]
                     "]")
                    [])]))))])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sq)
           ","
           (Tactic.rwRule
            [(patternIgnore (token.«← » "←"))]
            (Term.app `Real.sqrt_le_sqrt_iff [(Term.app `norm_nonneg [(Term.hole "_")])]))
           ","
           (Tactic.rwRule [] (Term.app `Real.sqrt_sq [(Term.app `norm_nonneg [(Term.hole "_")])]))]
          "]")
         [])
        []
        (Tactic.refine'
         "refine'"
         (Term.app
          `op_norm_le_bound
          [(Term.hole "_")
           (Term.app `Real.sqrt_nonneg [(Term.hole "_")])
           (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))]))
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           []
           ":="
           (calc
            "calc"
            (calcStep
             («term_≤_»
              (Term.app
               `re
               [(Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
                 "⟪"
                 (Term.app
                  («term_*_»
                   (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†")
                   "*"
                   `A)
                  [`x])
                 ", "
                 `x
                 "⟫")])
              "≤"
              («term_*_»
               (Analysis.Normed.Group.Basic.«term‖_‖»
                "‖"
                (Term.app
                 («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
                 [`x])
                "‖")
               "*"
               (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))
             ":="
             (Term.app `re_inner_le_norm [(Term.hole "_") (Term.hole "_")]))
            [(calcStep
              («term_≤_»
               (Term.hole "_")
               "≤"
               («term_*_»
                («term_*_»
                 (Analysis.Normed.Group.Basic.«term‖_‖»
                  "‖"
                  («term_*_»
                   (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†")
                   "*"
                   `A)
                  "‖")
                 "*"
                 (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))
                "*"
                (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))
              ":="
              (Term.app
               `mul_le_mul_of_nonneg_right
               [(Term.app `le_op_norm [(Term.hole "_") (Term.hole "_")])
                (Term.app `norm_nonneg [(Term.hole "_")])]))]))))
        []
        (calcTactic
         "calc"
         (calcStep
          («term_=_»
           (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `A [`x]) "‖")
           "="
           (Term.app
            `Real.sqrt
            [(Term.app
              `re
              [(Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
                "⟪"
                (Term.app
                 («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
                 [`x])
                ", "
                `x
                "⟫")])]))
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
                [(Tactic.rwRule [] `apply_norm_eq_sqrt_inner_adjoint_left)]
                "]")
               [])]))))
         [(calcStep
           («term_≤_»
            (Term.hole "_")
            "≤"
            (Term.app
             `Real.sqrt
             [(«term_*_»
               («term_*_»
                (Analysis.Normed.Group.Basic.«term‖_‖»
                 "‖"
                 («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
                 "‖")
                "*"
                (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))
               "*"
               (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))]))
           ":="
           (Term.app `Real.sqrt_le_sqrt [`this]))
          (calcStep
           («term_=_»
            (Term.hole "_")
            "="
            («term_*_»
             (Term.app
              `Real.sqrt
              [(Analysis.Normed.Group.Basic.«term‖_‖»
                "‖"
                («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
                "‖")])
             "*"
             (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))
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
                 [(Tactic.rwRule [] `mul_assoc)
                  ","
                  (Tactic.rwRule
                   []
                   (Term.app `Real.sqrt_mul [(Term.app `norm_nonneg [(Term.hole "_")])]))
                  ","
                  (Tactic.rwRule
                   []
                   (Term.app `Real.sqrt_mul_self [(Term.app `norm_nonneg [(Term.hole "_")])]))]
                 "]")
                [])]))))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_=_»
         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `A [`x]) "‖")
         "="
         (Term.app
          `Real.sqrt
          [(Term.app
            `re
            [(Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
              "⟪"
              (Term.app
               («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
               [`x])
              ", "
              `x
              "⟫")])]))
        ":="
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `apply_norm_eq_sqrt_inner_adjoint_left)] "]")
             [])]))))
       [(calcStep
         («term_≤_»
          (Term.hole "_")
          "≤"
          (Term.app
           `Real.sqrt
           [(«term_*_»
             («term_*_»
              (Analysis.Normed.Group.Basic.«term‖_‖»
               "‖"
               («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
               "‖")
              "*"
              (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))
             "*"
             (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))]))
         ":="
         (Term.app `Real.sqrt_le_sqrt [`this]))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          («term_*_»
           (Term.app
            `Real.sqrt
            [(Analysis.Normed.Group.Basic.«term‖_‖»
              "‖"
              («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
              "‖")])
           "*"
           (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))
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
               [(Tactic.rwRule [] `mul_assoc)
                ","
                (Tactic.rwRule
                 []
                 (Term.app `Real.sqrt_mul [(Term.app `norm_nonneg [(Term.hole "_")])]))
                ","
                (Tactic.rwRule
                 []
                 (Term.app `Real.sqrt_mul_self [(Term.app `norm_nonneg [(Term.hole "_")])]))]
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
            [(Tactic.rwRule [] `mul_assoc)
             ","
             (Tactic.rwRule
              []
              (Term.app `Real.sqrt_mul [(Term.app `norm_nonneg [(Term.hole "_")])]))
             ","
             (Tactic.rwRule
              []
              (Term.app `Real.sqrt_mul_self [(Term.app `norm_nonneg [(Term.hole "_")])]))]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `mul_assoc)
         ","
         (Tactic.rwRule [] (Term.app `Real.sqrt_mul [(Term.app `norm_nonneg [(Term.hole "_")])]))
         ","
         (Tactic.rwRule
          []
          (Term.app `Real.sqrt_mul_self [(Term.app `norm_nonneg [(Term.hole "_")])]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Real.sqrt_mul_self [(Term.app `norm_nonneg [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `norm_nonneg [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `norm_nonneg [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Real.sqrt_mul_self
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Real.sqrt_mul [(Term.app `norm_nonneg [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `norm_nonneg [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `norm_nonneg [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Real.sqrt_mul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       («term_*_»
        (Term.app
         `Real.sqrt
         [(Analysis.Normed.Group.Basic.«term‖_‖»
           "‖"
           («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
           "‖")])
        "*"
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.app
        `Real.sqrt
        [(Analysis.Normed.Group.Basic.«term‖_‖»
          "‖"
          («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
          "‖")])
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
      (Term.app
       `Real.sqrt
       [(Analysis.Normed.Group.Basic.«term‖_‖»
         "‖"
         («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
         "‖")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term‖_‖»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term‖_‖»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖»
       "‖"
       («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
       "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1000, term))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1000 >? 1024, (none,
     [anonymous]) <=? (some 1000, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1000, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Real.sqrt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.app `Real.sqrt_le_sqrt [`this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Real.sqrt_le_sqrt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Term.hole "_")
       "≤"
       (Term.app
        `Real.sqrt
        [(«term_*_»
          («term_*_»
           (Analysis.Normed.Group.Basic.«term‖_‖»
            "‖"
            («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
            "‖")
           "*"
           (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))
          "*"
          (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Real.sqrt
       [(«term_*_»
         («term_*_»
          (Analysis.Normed.Group.Basic.«term‖_‖»
           "‖"
           («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
           "‖")
          "*"
          (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))
         "*"
         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_*_»
        (Analysis.Normed.Group.Basic.«term‖_‖»
         "‖"
         («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
         "‖")
        "*"
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))
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
      («term_*_»
       (Analysis.Normed.Group.Basic.«term‖_‖»
        "‖"
        («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
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
       («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
       "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1000, term))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1000 >? 1024, (none,
     [anonymous]) <=? (some 1000, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1000, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_*_»
      («term_*_»
       (Analysis.Normed.Group.Basic.«term‖_‖»
        "‖"
        («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
        "‖")
       "*"
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))
      "*"
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `x "‖"))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Real.sqrt
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
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `apply_norm_eq_sqrt_inner_adjoint_left)] "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `apply_norm_eq_sqrt_inner_adjoint_left)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `apply_norm_eq_sqrt_inner_adjoint_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" (Term.app `A [`x]) "‖")
       "="
       (Term.app
        `Real.sqrt
        [(Term.app
          `re
          [(Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
            "⟪"
            (Term.app
             («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
             [`x])
            ", "
            `x
            "⟫")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Real.sqrt
       [(Term.app
         `re
         [(Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
           "⟪"
           (Term.app
            («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
            [`x])
           ", "
           `x
           "⟫")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `re
       [(Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
         "⟪"
         (Term.app
          («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
          [`x])
         ", "
         `x
         "⟫")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
       "⟪"
       (Term.app
        («term_*_» (InnerProduct.Analysis.InnerProductSpace.Adjoint.adjoint `A "†") "*" `A)
        [`x])
       ", "
       `x
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Adjoint.term⟪_,_⟫._@.Analysis.InnerProductSpace.Adjoint._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
instance
  : CstarRing E →L[ 𝕜 ] E
  :=
    ⟨
      by
        intro A
          rw [ star_eq_adjoint ]
          refine' le_antisymm _ _
          ·
            calc
              ‖ A † * A ‖ ≤ ‖ A † ‖ * ‖ A ‖ := op_norm_comp_le _ _
              _ = ‖ A ‖ * ‖ A ‖ := by rw [ LinearIsometryEquiv.norm_map ]
          ·
            rw [ ← sq , ← Real.sqrt_le_sqrt_iff norm_nonneg _ , Real.sqrt_sq norm_nonneg _ ]
              refine' op_norm_le_bound _ Real.sqrt_nonneg _ fun x => _
              have
                :=
                  calc
                    re ⟪ A † * A x , x ⟫ ≤ ‖ A † * A x ‖ * ‖ x ‖ := re_inner_le_norm _ _
                    _ ≤ ‖ A † * A ‖ * ‖ x ‖ * ‖ x ‖
                      :=
                      mul_le_mul_of_nonneg_right le_op_norm _ _ norm_nonneg _
              calc
                ‖ A x ‖ = Real.sqrt re ⟪ A † * A x , x ⟫
                  :=
                  by rw [ apply_norm_eq_sqrt_inner_adjoint_left ]
                _ ≤ Real.sqrt ‖ A † * A ‖ * ‖ x ‖ * ‖ x ‖ := Real.sqrt_le_sqrt this
                  _ = Real.sqrt ‖ A † * A ‖ * ‖ x ‖
                    :=
                    by
                      rw
                        [
                          mul_assoc , Real.sqrt_mul norm_nonneg _ , Real.sqrt_mul_self norm_nonneg _
                          ]
      ⟩

section Real

variable {E' : Type _} {F' : Type _} [InnerProductSpace ℝ E'] [InnerProductSpace ℝ F']

variable [CompleteSpace E'] [CompleteSpace F']

-- Todo: Generalize this to `is_R_or_C`.
theorem isAdjointPairInner (A : E' →L[ℝ] F') :
    LinearMap.IsAdjointPair (sesqFormOfInner : E' →ₗ[ℝ] E' →ₗ[ℝ] ℝ)
      (sesqFormOfInner : F' →ₗ[ℝ] F' →ₗ[ℝ] ℝ) A (A†) :=
  fun x y => by
  simp only [sesq_form_of_inner_apply_apply, adjoint_inner_left, to_linear_map_eq_coe, coe_coe]
#align continuous_linear_map.is_adjoint_pair_inner ContinuousLinearMap.isAdjointPairInner

end Real

end ContinuousLinearMap

/-! ### Self-adjoint operators -/


namespace IsSelfAdjoint

open ContinuousLinearMap

variable [CompleteSpace E] [CompleteSpace F]

theorem adjoint_eq {A : E →L[𝕜] E} (hA : IsSelfAdjoint A) : A.adjoint = A :=
  hA
#align is_self_adjoint.adjoint_eq IsSelfAdjoint.adjoint_eq

/-- Every self-adjoint operator on an inner product space is symmetric. -/
theorem isSymmetric {A : E →L[𝕜] E} (hA : IsSelfAdjoint A) : (A : E →ₗ[𝕜] E).IsSymmetric :=
  fun x y => by rw_mod_cast [← A.adjoint_inner_right, hA.adjoint_eq]
#align is_self_adjoint.is_symmetric IsSelfAdjoint.isSymmetric

/-- Conjugating preserves self-adjointness -/
theorem conj_adjoint {T : E →L[𝕜] E} (hT : IsSelfAdjoint T) (S : E →L[𝕜] F) :
    IsSelfAdjoint (S ∘L T ∘L S.adjoint) :=
  by
  rw [is_self_adjoint_iff'] at hT⊢
  simp only [hT, adjoint_comp, adjoint_adjoint]
  exact ContinuousLinearMap.comp_assoc _ _ _
#align is_self_adjoint.conj_adjoint IsSelfAdjoint.conj_adjoint

/-- Conjugating preserves self-adjointness -/
theorem adjoint_conj {T : E →L[𝕜] E} (hT : IsSelfAdjoint T) (S : F →L[𝕜] E) :
    IsSelfAdjoint (S.adjoint ∘L T ∘L S) :=
  by
  rw [is_self_adjoint_iff'] at hT⊢
  simp only [hT, adjoint_comp, adjoint_adjoint]
  exact ContinuousLinearMap.comp_assoc _ _ _
#align is_self_adjoint.adjoint_conj IsSelfAdjoint.adjoint_conj

theorem ContinuousLinearMap.is_self_adjoint_iff_is_symmetric {A : E →L[𝕜] E} :
    IsSelfAdjoint A ↔ (A : E →ₗ[𝕜] E).IsSymmetric :=
  ⟨fun hA => hA.IsSymmetric, fun hA =>
    ext fun x => (ext_inner_right 𝕜) fun y => (A.adjoint_inner_left y x).symm ▸ (hA x y).symm⟩
#align
  continuous_linear_map.is_self_adjoint_iff_is_symmetric ContinuousLinearMap.is_self_adjoint_iff_is_symmetric

theorem LinearMap.IsSymmetric.is_self_adjoint {A : E →L[𝕜] E} (hA : (A : E →ₗ[𝕜] E).IsSymmetric) :
    IsSelfAdjoint A := by rwa [← ContinuousLinearMap.is_self_adjoint_iff_is_symmetric] at hA
#align linear_map.is_symmetric.is_self_adjoint LinearMap.IsSymmetric.is_self_adjoint

/-- The orthogonal projection is self-adjoint. -/
theorem orthogonal_projection_is_self_adjoint (U : Submodule 𝕜 E) [CompleteSpace U] :
    IsSelfAdjoint (U.subtypeL ∘L orthogonalProjection U) :=
  (orthogonalProjectionIsSymmetric U).IsSelfAdjoint
#align orthogonal_projection_is_self_adjoint orthogonal_projection_is_self_adjoint

theorem conj_orthogonal_projection {T : E →L[𝕜] E} (hT : IsSelfAdjoint T) (U : Submodule 𝕜 E)
    [CompleteSpace U] :
    IsSelfAdjoint
      (U.subtypeL ∘L orthogonalProjection U ∘L T ∘L U.subtypeL ∘L orthogonalProjection U) :=
  by
  rw [← ContinuousLinearMap.comp_assoc]
  nth_rw 1 [← (orthogonal_projection_is_self_adjoint U).adjoint_eq]
  refine' hT.adjoint_conj _
#align is_self_adjoint.conj_orthogonal_projection IsSelfAdjoint.conj_orthogonal_projection

end IsSelfAdjoint

namespace LinearMap

variable [CompleteSpace E]

variable {T : E →ₗ[𝕜] E}

/-- The **Hellinger--Toeplitz theorem**: Construct a self-adjoint operator from an everywhere
  defined symmetric operator.-/
def IsSymmetric.toSelfAdjoint (hT : IsSymmetric T) : selfAdjoint (E →L[𝕜] E) :=
  ⟨⟨T, hT.Continuous⟩, ContinuousLinearMap.is_self_adjoint_iff_is_symmetric.mpr hT⟩
#align linear_map.is_symmetric.to_self_adjoint LinearMap.IsSymmetric.toSelfAdjoint

theorem IsSymmetric.coe_to_self_adjoint (hT : IsSymmetric T) : (hT.toSelfAdjoint : E →ₗ[𝕜] E) = T :=
  rfl
#align linear_map.is_symmetric.coe_to_self_adjoint LinearMap.IsSymmetric.coe_to_self_adjoint

theorem IsSymmetric.to_self_adjoint_apply (hT : IsSymmetric T) {x : E} : hT.toSelfAdjoint x = T x :=
  rfl
#align linear_map.is_symmetric.to_self_adjoint_apply LinearMap.IsSymmetric.to_self_adjoint_apply

end LinearMap

namespace LinearMap

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]

attribute [local instance] FiniteDimensional.complete

/-- The adjoint of an operator from the finite-dimensional inner product space E to the finite-
dimensional inner product space F. -/
def adjoint : (E →ₗ[𝕜] F) ≃ₗ⋆[𝕜] F →ₗ[𝕜] E :=
  ((LinearMap.toContinuousLinearMap : (E →ₗ[𝕜] F) ≃ₗ[𝕜] E →L[𝕜] F).trans
        ContinuousLinearMap.adjoint.toLinearEquiv).trans
    LinearMap.toContinuousLinearMap.symm
#align linear_map.adjoint LinearMap.adjoint

theorem adjoint_to_continuous_linear_map (A : E →ₗ[𝕜] F) :
    A.adjoint.toContinuousLinearMap = A.toContinuousLinearMap.adjoint :=
  rfl
#align linear_map.adjoint_to_continuous_linear_map LinearMap.adjoint_to_continuous_linear_map

theorem adjoint_eq_to_clm_adjoint (A : E →ₗ[𝕜] F) : A.adjoint = A.toContinuousLinearMap.adjoint :=
  rfl
#align linear_map.adjoint_eq_to_clm_adjoint LinearMap.adjoint_eq_to_clm_adjoint

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "The fundamental property of the adjoint. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `adjoint_inner_left [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`A]
         [":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `E " →ₗ[" `𝕜 "] " `F)]
         []
         ")")
        (Term.explicitBinder "(" [`x] [":" `E] [] ")")
        (Term.explicitBinder "(" [`y] [":" `F] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
          "⟪"
          (Term.app `adjoint [`A `y])
          ", "
          `x
          "⟫")
         "="
         (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" `y ", " (Term.app `A [`x]) "⟫"))))
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
               (Term.app `coe_to_continuous_linear_map [`A]))
              ","
              (Tactic.rwRule [] `adjoint_eq_to_clm_adjoint)]
             "]")
            [])
           []
           (Tactic.exact
            "exact"
            (Term.app `ContinuousLinearMap.adjoint_inner_left [(Term.hole "_") `x `y]))])))
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
              (Term.app `coe_to_continuous_linear_map [`A]))
             ","
             (Tactic.rwRule [] `adjoint_eq_to_clm_adjoint)]
            "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app `ContinuousLinearMap.adjoint_inner_left [(Term.hole "_") `x `y]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app `ContinuousLinearMap.adjoint_inner_left [(Term.hole "_") `x `y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ContinuousLinearMap.adjoint_inner_left [(Term.hole "_") `x `y])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ContinuousLinearMap.adjoint_inner_left
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
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app `coe_to_continuous_linear_map [`A]))
         ","
         (Tactic.rwRule [] `adjoint_eq_to_clm_adjoint)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `adjoint_eq_to_clm_adjoint
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `coe_to_continuous_linear_map [`A])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `coe_to_continuous_linear_map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" (Term.app `adjoint [`A `y]) ", " `x "⟫")
       "="
       (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" `y ", " (Term.app `A [`x]) "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" `y ", " (Term.app `A [`x]) "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Adjoint.term⟪_,_⟫._@.Analysis.InnerProductSpace.Adjoint._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The fundamental property of the adjoint. -/
  theorem
    adjoint_inner_left
    ( A : E →ₗ[ 𝕜 ] F ) ( x : E ) ( y : F ) : ⟪ adjoint A y , x ⟫ = ⟪ y , A x ⟫
    :=
      by
        rw [ ← coe_to_continuous_linear_map A , adjoint_eq_to_clm_adjoint ]
          exact ContinuousLinearMap.adjoint_inner_left _ x y
#align linear_map.adjoint_inner_left LinearMap.adjoint_inner_left

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "The fundamental property of the adjoint. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `adjoint_inner_right [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`A]
         [":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `E " →ₗ[" `𝕜 "] " `F)]
         []
         ")")
        (Term.explicitBinder "(" [`x] [":" `E] [] ")")
        (Term.explicitBinder "(" [`y] [":" `F] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
          "⟪"
          `x
          ", "
          (Term.app `adjoint [`A `y])
          "⟫")
         "="
         (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" (Term.app `A [`x]) ", " `y "⟫"))))
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
               (Term.app `coe_to_continuous_linear_map [`A]))
              ","
              (Tactic.rwRule [] `adjoint_eq_to_clm_adjoint)]
             "]")
            [])
           []
           (Tactic.exact
            "exact"
            (Term.app `ContinuousLinearMap.adjoint_inner_right [(Term.hole "_") `x `y]))])))
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
              (Term.app `coe_to_continuous_linear_map [`A]))
             ","
             (Tactic.rwRule [] `adjoint_eq_to_clm_adjoint)]
            "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app `ContinuousLinearMap.adjoint_inner_right [(Term.hole "_") `x `y]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app `ContinuousLinearMap.adjoint_inner_right [(Term.hole "_") `x `y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ContinuousLinearMap.adjoint_inner_right [(Term.hole "_") `x `y])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ContinuousLinearMap.adjoint_inner_right
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
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app `coe_to_continuous_linear_map [`A]))
         ","
         (Tactic.rwRule [] `adjoint_eq_to_clm_adjoint)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `adjoint_eq_to_clm_adjoint
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `coe_to_continuous_linear_map [`A])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `coe_to_continuous_linear_map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" `x ", " (Term.app `adjoint [`A `y]) "⟫")
       "="
       (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" (Term.app `A [`x]) ", " `y "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" (Term.app `A [`x]) ", " `y "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Adjoint.term⟪_,_⟫._@.Analysis.InnerProductSpace.Adjoint._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The fundamental property of the adjoint. -/
  theorem
    adjoint_inner_right
    ( A : E →ₗ[ 𝕜 ] F ) ( x : E ) ( y : F ) : ⟪ x , adjoint A y ⟫ = ⟪ A x , y ⟫
    :=
      by
        rw [ ← coe_to_continuous_linear_map A , adjoint_eq_to_clm_adjoint ]
          exact ContinuousLinearMap.adjoint_inner_right _ x y
#align linear_map.adjoint_inner_right LinearMap.adjoint_inner_right

/-- The adjoint is involutive -/
@[simp]
theorem adjoint_adjoint (A : E →ₗ[𝕜] F) : A.adjoint.adjoint = A :=
  by
  ext v
  refine' ext_inner_left 𝕜 fun w => _
  rw [adjoint_inner_right, adjoint_inner_left]
#align linear_map.adjoint_adjoint LinearMap.adjoint_adjoint

/-- The adjoint of the composition of two operators is the composition of the two adjoints
in reverse order. -/
@[simp]
theorem adjoint_comp (A : F →ₗ[𝕜] G) (B : E →ₗ[𝕜] F) : (A ∘ₗ B).adjoint = B.adjoint ∘ₗ A.adjoint :=
  by
  ext v
  refine' ext_inner_left 𝕜 fun w => _
  simp only [adjoint_inner_right, LinearMap.coe_comp, Function.comp_apply]
#align linear_map.adjoint_comp LinearMap.adjoint_comp

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The adjoint is unique: a map `A` is the adjoint of `B` iff it satisfies `⟪A x, y⟫ = ⟪x, B y⟫`\nfor all `x` and `y`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `eq_adjoint_iff [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`A]
         [":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `E " →ₗ[" `𝕜 "] " `F)]
         []
         ")")
        (Term.explicitBinder
         "("
         [`B]
         [":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `F " →ₗ[" `𝕜 "] " `E)]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_=_» `A "=" (Term.proj `B "." `adjoint))
         "↔"
         (Term.forall
          "∀"
          [`x `y]
          []
          ","
          («term_=_»
           (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" (Term.app `A [`x]) ", " `y "⟫")
           "="
           (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" `x ", " (Term.app `B [`y]) "⟫"))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.anonymousCtor
             "⟨"
             [(Term.fun
               "fun"
               (Term.basicFun
                [`h `x `y]
                []
                "=>"
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `adjoint_inner_left)]
                      "]")
                     [])])))))
              ","
              (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))]
             "⟩"))
           []
           (Std.Tactic.Ext.«tacticExt___:_»
            "ext"
            [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))]
            [])
           []
           (Tactic.exact
            "exact"
            (Term.app
             `ext_inner_right
             [`𝕜
              (Term.fun
               "fun"
               (Term.basicFun
                [`y]
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
                      [(Tactic.simpLemma [] [] `adjoint_inner_left)
                       ","
                       (Tactic.simpLemma [] [] (Term.app `h [`x `y]))]
                      "]"]
                     [])])))))]))])))
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
           (Term.anonymousCtor
            "⟨"
            [(Term.fun
              "fun"
              (Term.basicFun
               [`h `x `y]
               []
               "=>"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `adjoint_inner_left)]
                     "]")
                    [])])))))
             ","
             (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))]
            "⟩"))
          []
          (Std.Tactic.Ext.«tacticExt___:_»
           "ext"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))]
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            `ext_inner_right
            [`𝕜
             (Term.fun
              "fun"
              (Term.basicFun
               [`y]
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
                     [(Tactic.simpLemma [] [] `adjoint_inner_left)
                      ","
                      (Tactic.simpLemma [] [] (Term.app `h [`x `y]))]
                     "]"]
                    [])])))))]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `ext_inner_right
        [`𝕜
         (Term.fun
          "fun"
          (Term.basicFun
           [`y]
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
                 [(Tactic.simpLemma [] [] `adjoint_inner_left)
                  ","
                  (Tactic.simpLemma [] [] (Term.app `h [`x `y]))]
                 "]"]
                [])])))))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `ext_inner_right
       [`𝕜
        (Term.fun
         "fun"
         (Term.basicFun
          [`y]
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
                [(Tactic.simpLemma [] [] `adjoint_inner_left)
                 ","
                 (Tactic.simpLemma [] [] (Term.app `h [`x `y]))]
                "]"]
               [])])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`y]
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
              [(Tactic.simpLemma [] [] `adjoint_inner_left)
               ","
               (Tactic.simpLemma [] [] (Term.app `h [`x `y]))]
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
            [(Tactic.simpLemma [] [] `adjoint_inner_left)
             ","
             (Tactic.simpLemma [] [] (Term.app `h [`x `y]))]
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
        [(Tactic.simpLemma [] [] `adjoint_inner_left)
         ","
         (Tactic.simpLemma [] [] (Term.app `h [`x `y]))]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h [`x `y])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `adjoint_inner_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `𝕜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ext_inner_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_»
       "ext"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [(Term.fun
          "fun"
          (Term.basicFun
           [`h `x `y]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `adjoint_inner_left)]
                 "]")
                [])])))))
         ","
         (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [`h `x `y]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `adjoint_inner_left)]
                "]")
               [])])))))
        ","
        (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`h `x `y]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `adjoint_inner_left)]
              "]")
             [])])))))
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
            [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `adjoint_inner_left)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `adjoint_inner_left)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `adjoint_inner_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_=_» `A "=" (Term.proj `B "." `adjoint))
       "↔"
       (Term.forall
        "∀"
        [`x `y]
        []
        ","
        («term_=_»
         (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" (Term.app `A [`x]) ", " `y "⟫")
         "="
         (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" `x ", " (Term.app `B [`y]) "⟫"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`x `y]
       []
       ","
       («term_=_»
        (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" (Term.app `A [`x]) ", " `y "⟫")
        "="
        (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" `x ", " (Term.app `B [`y]) "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" (Term.app `A [`x]) ", " `y "⟫")
       "="
       (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" `x ", " (Term.app `B [`y]) "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫» "⟪" `x ", " (Term.app `B [`y]) "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Adjoint.term⟪_,_⟫._@.Analysis.InnerProductSpace.Adjoint._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The adjoint is unique: a map `A` is the adjoint of `B` iff it satisfies `⟪A x, y⟫ = ⟪x, B y⟫`
    for all `x` and `y`. -/
  theorem
    eq_adjoint_iff
    ( A : E →ₗ[ 𝕜 ] F ) ( B : F →ₗ[ 𝕜 ] E ) : A = B . adjoint ↔ ∀ x y , ⟪ A x , y ⟫ = ⟪ x , B y ⟫
    :=
      by
        refine' ⟨ fun h x y => by rw [ h , adjoint_inner_left ] , fun h => _ ⟩
          ext x
          exact ext_inner_right 𝕜 fun y => by simp only [ adjoint_inner_left , h x y ]
#align linear_map.eq_adjoint_iff LinearMap.eq_adjoint_iff

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The adjoint is unique: a map `A` is the adjoint of `B` iff it satisfies `⟪A x, y⟫ = ⟪x, B y⟫`\nfor all basis vectors `x` and `y`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `eq_adjoint_iff_basis [])
      (Command.declSig
       [(Term.implicitBinder "{" [`ι₁] [":" (Term.type "Type" [(Level.hole "_")])] "}")
        (Term.implicitBinder "{" [`ι₂] [":" (Term.type "Type" [(Level.hole "_")])] "}")
        (Term.explicitBinder "(" [`b₁] [":" (Term.app `Basis [`ι₁ `𝕜 `E])] [] ")")
        (Term.explicitBinder "(" [`b₂] [":" (Term.app `Basis [`ι₂ `𝕜 `F])] [] ")")
        (Term.explicitBinder
         "("
         [`A]
         [":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `E " →ₗ[" `𝕜 "] " `F)]
         []
         ")")
        (Term.explicitBinder
         "("
         [`B]
         [":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `F " →ₗ[" `𝕜 "] " `E)]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_=_» `A "=" (Term.proj `B "." `adjoint))
         "↔"
         (Term.forall
          "∀"
          [(Term.explicitBinder "(" [`i₁] [":" `ι₁] [] ")")
           (Term.explicitBinder "(" [`i₂] [":" `ι₂] [] ")")]
          []
          ","
          («term_=_»
           (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
            "⟪"
            (Term.app `A [(Term.app `b₁ [`i₁])])
            ", "
            (Term.app `b₂ [`i₂])
            "⟫")
           "="
           (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
            "⟪"
            (Term.app `b₁ [`i₁])
            ", "
            (Term.app `B [(Term.app `b₂ [`i₂])])
            "⟫"))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.anonymousCtor
             "⟨"
             [(Term.fun
               "fun"
               (Term.basicFun
                [`h `x `y]
                []
                "=>"
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `adjoint_inner_left)]
                      "]")
                     [])])))))
              ","
              (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))]
             "⟩"))
           []
           (Tactic.refine'
            "refine'"
            (Term.app
             `Basis.ext
             [`b₁ (Term.fun "fun" (Term.basicFun [`i₁] [] "=>" (Term.hole "_")))]))
           []
           (Tactic.exact
            "exact"
            (Term.app
             `ext_inner_right_basis
             [`b₂
              (Term.fun
               "fun"
               (Term.basicFun
                [`i₂]
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
                      [(Tactic.simpLemma [] [] `adjoint_inner_left)
                       ","
                       (Tactic.simpLemma [] [] (Term.app `h [`i₁ `i₂]))]
                      "]"]
                     [])])))))]))])))
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
           (Term.anonymousCtor
            "⟨"
            [(Term.fun
              "fun"
              (Term.basicFun
               [`h `x `y]
               []
               "=>"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `adjoint_inner_left)]
                     "]")
                    [])])))))
             ","
             (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))]
            "⟩"))
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            `Basis.ext
            [`b₁ (Term.fun "fun" (Term.basicFun [`i₁] [] "=>" (Term.hole "_")))]))
          []
          (Tactic.exact
           "exact"
           (Term.app
            `ext_inner_right_basis
            [`b₂
             (Term.fun
              "fun"
              (Term.basicFun
               [`i₂]
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
                     [(Tactic.simpLemma [] [] `adjoint_inner_left)
                      ","
                      (Tactic.simpLemma [] [] (Term.app `h [`i₁ `i₂]))]
                     "]"]
                    [])])))))]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `ext_inner_right_basis
        [`b₂
         (Term.fun
          "fun"
          (Term.basicFun
           [`i₂]
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
                 [(Tactic.simpLemma [] [] `adjoint_inner_left)
                  ","
                  (Tactic.simpLemma [] [] (Term.app `h [`i₁ `i₂]))]
                 "]"]
                [])])))))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `ext_inner_right_basis
       [`b₂
        (Term.fun
         "fun"
         (Term.basicFun
          [`i₂]
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
                [(Tactic.simpLemma [] [] `adjoint_inner_left)
                 ","
                 (Tactic.simpLemma [] [] (Term.app `h [`i₁ `i₂]))]
                "]"]
               [])])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`i₂]
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
              [(Tactic.simpLemma [] [] `adjoint_inner_left)
               ","
               (Tactic.simpLemma [] [] (Term.app `h [`i₁ `i₂]))]
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
            [(Tactic.simpLemma [] [] `adjoint_inner_left)
             ","
             (Tactic.simpLemma [] [] (Term.app `h [`i₁ `i₂]))]
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
        [(Tactic.simpLemma [] [] `adjoint_inner_left)
         ","
         (Tactic.simpLemma [] [] (Term.app `h [`i₁ `i₂]))]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h [`i₁ `i₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `adjoint_inner_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `b₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ext_inner_right_basis
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app `Basis.ext [`b₁ (Term.fun "fun" (Term.basicFun [`i₁] [] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Basis.ext [`b₁ (Term.fun "fun" (Term.basicFun [`i₁] [] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`i₁] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `b₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Basis.ext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [(Term.fun
          "fun"
          (Term.basicFun
           [`h `x `y]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `adjoint_inner_left)]
                 "]")
                [])])))))
         ","
         (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [`h `x `y]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `adjoint_inner_left)]
                "]")
               [])])))))
        ","
        (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`h `x `y]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `adjoint_inner_left)]
              "]")
             [])])))))
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
            [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `adjoint_inner_left)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `adjoint_inner_left)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `adjoint_inner_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_=_» `A "=" (Term.proj `B "." `adjoint))
       "↔"
       (Term.forall
        "∀"
        [(Term.explicitBinder "(" [`i₁] [":" `ι₁] [] ")")
         (Term.explicitBinder "(" [`i₂] [":" `ι₂] [] ")")]
        []
        ","
        («term_=_»
         (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
          "⟪"
          (Term.app `A [(Term.app `b₁ [`i₁])])
          ", "
          (Term.app `b₂ [`i₂])
          "⟫")
         "="
         (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
          "⟪"
          (Term.app `b₁ [`i₁])
          ", "
          (Term.app `B [(Term.app `b₂ [`i₂])])
          "⟫"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [(Term.explicitBinder "(" [`i₁] [":" `ι₁] [] ")")
        (Term.explicitBinder "(" [`i₂] [":" `ι₂] [] ")")]
       []
       ","
       («term_=_»
        (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
         "⟪"
         (Term.app `A [(Term.app `b₁ [`i₁])])
         ", "
         (Term.app `b₂ [`i₂])
         "⟫")
        "="
        (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
         "⟪"
         (Term.app `b₁ [`i₁])
         ", "
         (Term.app `B [(Term.app `b₂ [`i₂])])
         "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
        "⟪"
        (Term.app `A [(Term.app `b₁ [`i₁])])
        ", "
        (Term.app `b₂ [`i₂])
        "⟫")
       "="
       (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
        "⟪"
        (Term.app `b₁ [`i₁])
        ", "
        (Term.app `B [(Term.app `b₂ [`i₂])])
        "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
       "⟪"
       (Term.app `b₁ [`i₁])
       ", "
       (Term.app `B [(Term.app `b₂ [`i₂])])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Adjoint.term⟪_,_⟫._@.Analysis.InnerProductSpace.Adjoint._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The adjoint is unique: a map `A` is the adjoint of `B` iff it satisfies `⟪A x, y⟫ = ⟪x, B y⟫`
    for all basis vectors `x` and `y`. -/
  theorem
    eq_adjoint_iff_basis
    { ι₁ : Type _ }
        { ι₂ : Type _ }
        ( b₁ : Basis ι₁ 𝕜 E )
        ( b₂ : Basis ι₂ 𝕜 F )
        ( A : E →ₗ[ 𝕜 ] F )
        ( B : F →ₗ[ 𝕜 ] E )
      : A = B . adjoint ↔ ∀ ( i₁ : ι₁ ) ( i₂ : ι₂ ) , ⟪ A b₁ i₁ , b₂ i₂ ⟫ = ⟪ b₁ i₁ , B b₂ i₂ ⟫
    :=
      by
        refine' ⟨ fun h x y => by rw [ h , adjoint_inner_left ] , fun h => _ ⟩
          refine' Basis.ext b₁ fun i₁ => _
          exact ext_inner_right_basis b₂ fun i₂ => by simp only [ adjoint_inner_left , h i₁ i₂ ]
#align linear_map.eq_adjoint_iff_basis LinearMap.eq_adjoint_iff_basis

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `eq_adjoint_iff_basis_left [])
      (Command.declSig
       [(Term.implicitBinder "{" [`ι] [":" (Term.type "Type" [(Level.hole "_")])] "}")
        (Term.explicitBinder "(" [`b] [":" (Term.app `Basis [`ι `𝕜 `E])] [] ")")
        (Term.explicitBinder
         "("
         [`A]
         [":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `E " →ₗ[" `𝕜 "] " `F)]
         []
         ")")
        (Term.explicitBinder
         "("
         [`B]
         [":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `F " →ₗ[" `𝕜 "] " `E)]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_=_» `A "=" (Term.proj `B "." `adjoint))
         "↔"
         (Term.forall
          "∀"
          [`i `y]
          []
          ","
          («term_=_»
           (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
            "⟪"
            (Term.app `A [(Term.app `b [`i])])
            ", "
            `y
            "⟫")
           "="
           (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
            "⟪"
            (Term.app `b [`i])
            ", "
            (Term.app `B [`y])
            "⟫"))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.anonymousCtor
             "⟨"
             [(Term.fun
               "fun"
               (Term.basicFun
                [`h `x `y]
                []
                "=>"
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `adjoint_inner_left)]
                      "]")
                     [])])))))
              ","
              (Term.fun
               "fun"
               (Term.basicFun
                [`h]
                []
                "=>"
                (Term.app
                 `Basis.ext
                 [`b (Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.hole "_")))])))]
             "⟩"))
           []
           (Tactic.exact
            "exact"
            (Term.app
             `ext_inner_right
             [`𝕜
              (Term.fun
               "fun"
               (Term.basicFun
                [`y]
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
                      [(Tactic.simpLemma [] [] (Term.app `h [`i]))
                       ","
                       (Tactic.simpLemma [] [] `adjoint_inner_left)]
                      "]"]
                     [])])))))]))])))
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
           (Term.anonymousCtor
            "⟨"
            [(Term.fun
              "fun"
              (Term.basicFun
               [`h `x `y]
               []
               "=>"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `adjoint_inner_left)]
                     "]")
                    [])])))))
             ","
             (Term.fun
              "fun"
              (Term.basicFun
               [`h]
               []
               "=>"
               (Term.app
                `Basis.ext
                [`b (Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.hole "_")))])))]
            "⟩"))
          []
          (Tactic.exact
           "exact"
           (Term.app
            `ext_inner_right
            [`𝕜
             (Term.fun
              "fun"
              (Term.basicFun
               [`y]
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
                     [(Tactic.simpLemma [] [] (Term.app `h [`i]))
                      ","
                      (Tactic.simpLemma [] [] `adjoint_inner_left)]
                     "]"]
                    [])])))))]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `ext_inner_right
        [`𝕜
         (Term.fun
          "fun"
          (Term.basicFun
           [`y]
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
                 [(Tactic.simpLemma [] [] (Term.app `h [`i]))
                  ","
                  (Tactic.simpLemma [] [] `adjoint_inner_left)]
                 "]"]
                [])])))))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `ext_inner_right
       [`𝕜
        (Term.fun
         "fun"
         (Term.basicFun
          [`y]
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
                [(Tactic.simpLemma [] [] (Term.app `h [`i]))
                 ","
                 (Tactic.simpLemma [] [] `adjoint_inner_left)]
                "]"]
               [])])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`y]
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
              [(Tactic.simpLemma [] [] (Term.app `h [`i]))
               ","
               (Tactic.simpLemma [] [] `adjoint_inner_left)]
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
            [(Tactic.simpLemma [] [] (Term.app `h [`i]))
             ","
             (Tactic.simpLemma [] [] `adjoint_inner_left)]
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
        [(Tactic.simpLemma [] [] (Term.app `h [`i]))
         ","
         (Tactic.simpLemma [] [] `adjoint_inner_left)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `adjoint_inner_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `𝕜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ext_inner_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [(Term.fun
          "fun"
          (Term.basicFun
           [`h `x `y]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `adjoint_inner_left)]
                 "]")
                [])])))))
         ","
         (Term.fun
          "fun"
          (Term.basicFun
           [`h]
           []
           "=>"
           (Term.app
            `Basis.ext
            [`b (Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.hole "_")))])))]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [`h `x `y]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `adjoint_inner_left)]
                "]")
               [])])))))
        ","
        (Term.fun
         "fun"
         (Term.basicFun
          [`h]
          []
          "=>"
          (Term.app
           `Basis.ext
           [`b (Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.hole "_")))])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`h]
        []
        "=>"
        (Term.app `Basis.ext [`b (Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.hole "_")))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Basis.ext [`b (Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Basis.ext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`h `x `y]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `adjoint_inner_left)]
              "]")
             [])])))))
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
            [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `adjoint_inner_left)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `adjoint_inner_left)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `adjoint_inner_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_=_» `A "=" (Term.proj `B "." `adjoint))
       "↔"
       (Term.forall
        "∀"
        [`i `y]
        []
        ","
        («term_=_»
         (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
          "⟪"
          (Term.app `A [(Term.app `b [`i])])
          ", "
          `y
          "⟫")
         "="
         (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
          "⟪"
          (Term.app `b [`i])
          ", "
          (Term.app `B [`y])
          "⟫"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`i `y]
       []
       ","
       («term_=_»
        (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
         "⟪"
         (Term.app `A [(Term.app `b [`i])])
         ", "
         `y
         "⟫")
        "="
        (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
         "⟪"
         (Term.app `b [`i])
         ", "
         (Term.app `B [`y])
         "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
        "⟪"
        (Term.app `A [(Term.app `b [`i])])
        ", "
        `y
        "⟫")
       "="
       (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
        "⟪"
        (Term.app `b [`i])
        ", "
        (Term.app `B [`y])
        "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
       "⟪"
       (Term.app `b [`i])
       ", "
       (Term.app `B [`y])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Adjoint.term⟪_,_⟫._@.Analysis.InnerProductSpace.Adjoint._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  eq_adjoint_iff_basis_left
  { ι : Type _ } ( b : Basis ι 𝕜 E ) ( A : E →ₗ[ 𝕜 ] F ) ( B : F →ₗ[ 𝕜 ] E )
    : A = B . adjoint ↔ ∀ i y , ⟪ A b i , y ⟫ = ⟪ b i , B y ⟫
  :=
    by
      refine' ⟨ fun h x y => by rw [ h , adjoint_inner_left ] , fun h => Basis.ext b fun i => _ ⟩
        exact ext_inner_right 𝕜 fun y => by simp only [ h i , adjoint_inner_left ]
#align linear_map.eq_adjoint_iff_basis_left LinearMap.eq_adjoint_iff_basis_left

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `eq_adjoint_iff_basis_right [])
      (Command.declSig
       [(Term.implicitBinder "{" [`ι] [":" (Term.type "Type" [(Level.hole "_")])] "}")
        (Term.explicitBinder "(" [`b] [":" (Term.app `Basis [`ι `𝕜 `F])] [] ")")
        (Term.explicitBinder
         "("
         [`A]
         [":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `E " →ₗ[" `𝕜 "] " `F)]
         []
         ")")
        (Term.explicitBinder
         "("
         [`B]
         [":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `F " →ₗ[" `𝕜 "] " `E)]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_=_» `A "=" (Term.proj `B "." `adjoint))
         "↔"
         (Term.forall
          "∀"
          [`i `x]
          []
          ","
          («term_=_»
           (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
            "⟪"
            (Term.app `A [`x])
            ", "
            (Term.app `b [`i])
            "⟫")
           "="
           (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
            "⟪"
            `x
            ", "
            (Term.app `B [(Term.app `b [`i])])
            "⟫"))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.anonymousCtor
             "⟨"
             [(Term.fun
               "fun"
               (Term.basicFun
                [`h `x `y]
                []
                "=>"
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `adjoint_inner_left)]
                      "]")
                     [])])))))
              ","
              (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))]
             "⟩"))
           []
           (Std.Tactic.Ext.«tacticExt___:_»
            "ext"
            [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))]
            [])
           []
           (Tactic.refine'
            "refine'"
            (Term.app
             `ext_inner_right_basis
             [`b
              (Term.fun
               "fun"
               (Term.basicFun
                [`i]
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
                      [(Tactic.simpLemma [] [] (Term.app `h [`i]))
                       ","
                       (Tactic.simpLemma [] [] `adjoint_inner_left)]
                      "]"]
                     [])])))))]))])))
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
           (Term.anonymousCtor
            "⟨"
            [(Term.fun
              "fun"
              (Term.basicFun
               [`h `x `y]
               []
               "=>"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `adjoint_inner_left)]
                     "]")
                    [])])))))
             ","
             (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))]
            "⟩"))
          []
          (Std.Tactic.Ext.«tacticExt___:_»
           "ext"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))]
           [])
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            `ext_inner_right_basis
            [`b
             (Term.fun
              "fun"
              (Term.basicFun
               [`i]
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
                     [(Tactic.simpLemma [] [] (Term.app `h [`i]))
                      ","
                      (Tactic.simpLemma [] [] `adjoint_inner_left)]
                     "]"]
                    [])])))))]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `ext_inner_right_basis
        [`b
         (Term.fun
          "fun"
          (Term.basicFun
           [`i]
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
                 [(Tactic.simpLemma [] [] (Term.app `h [`i]))
                  ","
                  (Tactic.simpLemma [] [] `adjoint_inner_left)]
                 "]"]
                [])])))))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `ext_inner_right_basis
       [`b
        (Term.fun
         "fun"
         (Term.basicFun
          [`i]
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
                [(Tactic.simpLemma [] [] (Term.app `h [`i]))
                 ","
                 (Tactic.simpLemma [] [] `adjoint_inner_left)]
                "]"]
               [])])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`i]
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
              [(Tactic.simpLemma [] [] (Term.app `h [`i]))
               ","
               (Tactic.simpLemma [] [] `adjoint_inner_left)]
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
            [(Tactic.simpLemma [] [] (Term.app `h [`i]))
             ","
             (Tactic.simpLemma [] [] `adjoint_inner_left)]
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
        [(Tactic.simpLemma [] [] (Term.app `h [`i]))
         ","
         (Tactic.simpLemma [] [] `adjoint_inner_left)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `adjoint_inner_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ext_inner_right_basis
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_»
       "ext"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [(Term.fun
          "fun"
          (Term.basicFun
           [`h `x `y]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `adjoint_inner_left)]
                 "]")
                [])])))))
         ","
         (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [`h `x `y]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `adjoint_inner_left)]
                "]")
               [])])))))
        ","
        (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`h `x `y]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `adjoint_inner_left)]
              "]")
             [])])))))
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
            [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `adjoint_inner_left)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `adjoint_inner_left)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `adjoint_inner_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_=_» `A "=" (Term.proj `B "." `adjoint))
       "↔"
       (Term.forall
        "∀"
        [`i `x]
        []
        ","
        («term_=_»
         (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
          "⟪"
          (Term.app `A [`x])
          ", "
          (Term.app `b [`i])
          "⟫")
         "="
         (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
          "⟪"
          `x
          ", "
          (Term.app `B [(Term.app `b [`i])])
          "⟫"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`i `x]
       []
       ","
       («term_=_»
        (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
         "⟪"
         (Term.app `A [`x])
         ", "
         (Term.app `b [`i])
         "⟫")
        "="
        (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
         "⟪"
         `x
         ", "
         (Term.app `B [(Term.app `b [`i])])
         "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
        "⟪"
        (Term.app `A [`x])
        ", "
        (Term.app `b [`i])
        "⟫")
       "="
       (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
        "⟪"
        `x
        ", "
        (Term.app `B [(Term.app `b [`i])])
        "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
       "⟪"
       `x
       ", "
       (Term.app `B [(Term.app `b [`i])])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Adjoint.term⟪_,_⟫._@.Analysis.InnerProductSpace.Adjoint._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  eq_adjoint_iff_basis_right
  { ι : Type _ } ( b : Basis ι 𝕜 F ) ( A : E →ₗ[ 𝕜 ] F ) ( B : F →ₗ[ 𝕜 ] E )
    : A = B . adjoint ↔ ∀ i x , ⟪ A x , b i ⟫ = ⟪ x , B b i ⟫
  :=
    by
      refine' ⟨ fun h x y => by rw [ h , adjoint_inner_left ] , fun h => _ ⟩
        ext x
        refine' ext_inner_right_basis b fun i => by simp only [ h i , adjoint_inner_left ]
#align linear_map.eq_adjoint_iff_basis_right LinearMap.eq_adjoint_iff_basis_right

/-- `E →ₗ[𝕜] E` is a star algebra with the adjoint as the star operation. -/
instance : HasStar (E →ₗ[𝕜] E) :=
  ⟨adjoint⟩

instance : HasInvolutiveStar (E →ₗ[𝕜] E) :=
  ⟨adjoint_adjoint⟩

instance : StarSemigroup (E →ₗ[𝕜] E) :=
  ⟨adjoint_comp⟩

instance : StarRing (E →ₗ[𝕜] E) :=
  ⟨LinearEquiv.map_add adjoint⟩

instance : StarModule 𝕜 (E →ₗ[𝕜] E) :=
  ⟨LinearEquiv.map_smulₛₗ adjoint⟩

theorem star_eq_adjoint (A : E →ₗ[𝕜] E) : star A = A.adjoint :=
  rfl
#align linear_map.star_eq_adjoint LinearMap.star_eq_adjoint

/-- A continuous linear operator is self-adjoint iff it is equal to its adjoint. -/
theorem is_self_adjoint_iff' {A : E →ₗ[𝕜] E} : IsSelfAdjoint A ↔ A.adjoint = A :=
  Iff.rfl
#align linear_map.is_self_adjoint_iff' LinearMap.is_self_adjoint_iff'

theorem is_symmetric_iff_is_self_adjoint (A : E →ₗ[𝕜] E) : IsSymmetric A ↔ IsSelfAdjoint A :=
  by
  rw [is_self_adjoint_iff', is_symmetric, ← LinearMap.eq_adjoint_iff]
  exact eq_comm
#align linear_map.is_symmetric_iff_is_self_adjoint LinearMap.is_symmetric_iff_is_self_adjoint

section Real

variable {E' : Type _} {F' : Type _} [InnerProductSpace ℝ E'] [InnerProductSpace ℝ F']

variable [FiniteDimensional ℝ E'] [FiniteDimensional ℝ F']

-- Todo: Generalize this to `is_R_or_C`.
theorem isAdjointPairInner (A : E' →ₗ[ℝ] F') :
    IsAdjointPair (sesqFormOfInner : E' →ₗ[ℝ] E' →ₗ[ℝ] ℝ) (sesqFormOfInner : F' →ₗ[ℝ] F' →ₗ[ℝ] ℝ) A
      A.adjoint :=
  fun x y => by simp only [sesq_form_of_inner_apply_apply, adjoint_inner_left]
#align linear_map.is_adjoint_pair_inner LinearMap.isAdjointPairInner

end Real

/-- The Gram operator T†T is symmetric. -/
theorem isSymmetricAdjointMulSelf (T : E →ₗ[𝕜] E) : IsSymmetric (T.adjoint * T) := fun x y => by
  simp only [mul_apply, adjoint_inner_left, adjoint_inner_right]
#align linear_map.is_symmetric_adjoint_mul_self LinearMap.isSymmetricAdjointMulSelf

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "The Gram operator T†T is a positive operator. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `re_inner_adjoint_mul_self_nonneg [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`T]
         [":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `E " →ₗ[" `𝕜 "] " `E)]
         []
         ")")
        (Term.explicitBinder "(" [`x] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         (num "0")
         "≤"
         (Term.app
          `re
          [(Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
            "⟪"
            `x
            ", "
            (Term.app («term_*_» (Term.proj `T "." `adjoint) "*" `T) [`x])
            "⟫")]))))
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
             [(Tactic.simpLemma [] [] `mul_apply)
              ","
              (Tactic.simpLemma [] [] `adjoint_inner_right)
              ","
              (Tactic.simpLemma [] [] `inner_self_eq_norm_sq_to_K)]
             "]"]
            [])
           []
           (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
           []
           (Tactic.exact "exact" (Term.app `sq_nonneg [(Term.hole "_")]))])))
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
            [(Tactic.simpLemma [] [] `mul_apply)
             ","
             (Tactic.simpLemma [] [] `adjoint_inner_right)
             ","
             (Tactic.simpLemma [] [] `inner_self_eq_norm_sq_to_K)]
            "]"]
           [])
          []
          (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
          []
          (Tactic.exact "exact" (Term.app `sq_nonneg [(Term.hole "_")]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `sq_nonneg [(Term.hole "_")]))
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `mul_apply)
         ","
         (Tactic.simpLemma [] [] `adjoint_inner_right)
         ","
         (Tactic.simpLemma [] [] `inner_self_eq_norm_sq_to_K)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner_self_eq_norm_sq_to_K
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `adjoint_inner_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≤_»
       (num "0")
       "≤"
       (Term.app
        `re
        [(Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
          "⟪"
          `x
          ", "
          (Term.app («term_*_» (Term.proj `T "." `adjoint) "*" `T) [`x])
          "⟫")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `re
       [(Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
         "⟪"
         `x
         ", "
         (Term.app («term_*_» (Term.proj `T "." `adjoint) "*" `T) [`x])
         "⟫")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
       "⟪"
       `x
       ", "
       (Term.app («term_*_» (Term.proj `T "." `adjoint) "*" `T) [`x])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Adjoint.term⟪_,_⟫._@.Analysis.InnerProductSpace.Adjoint._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The Gram operator T†T is a positive operator. -/
  theorem
    re_inner_adjoint_mul_self_nonneg
    ( T : E →ₗ[ 𝕜 ] E ) ( x : E ) : 0 ≤ re ⟪ x , T . adjoint * T x ⟫
    :=
      by
        simp only [ mul_apply , adjoint_inner_right , inner_self_eq_norm_sq_to_K ]
          norm_cast
          exact sq_nonneg _
#align linear_map.re_inner_adjoint_mul_self_nonneg LinearMap.re_inner_adjoint_mul_self_nonneg

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
      (Command.declId `im_inner_adjoint_mul_self_eq_zero [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`T]
         [":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `E " →ₗ[" `𝕜 "] " `E)]
         []
         ")")
        (Term.explicitBinder "(" [`x] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          `im
          [(Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
            "⟪"
            `x
            ", "
            (Term.app `LinearMap.adjoint [`T (Term.app `T [`x])])
            "⟫")])
         "="
         (num "0"))))
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
             [(Tactic.simpLemma [] [] `mul_apply)
              ","
              (Tactic.simpLemma [] [] `adjoint_inner_right)
              ","
              (Tactic.simpLemma [] [] `inner_self_eq_norm_sq_to_K)]
             "]"]
            [])
           []
           (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])])))
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
            [(Tactic.simpLemma [] [] `mul_apply)
             ","
             (Tactic.simpLemma [] [] `adjoint_inner_right)
             ","
             (Tactic.simpLemma [] [] `inner_self_eq_norm_sq_to_K)]
            "]"]
           [])
          []
          (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `mul_apply)
         ","
         (Tactic.simpLemma [] [] `adjoint_inner_right)
         ","
         (Tactic.simpLemma [] [] `inner_self_eq_norm_sq_to_K)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner_self_eq_norm_sq_to_K
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `adjoint_inner_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        `im
        [(Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
          "⟪"
          `x
          ", "
          (Term.app `LinearMap.adjoint [`T (Term.app `T [`x])])
          "⟫")])
       "="
       (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       `im
       [(Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
         "⟪"
         `x
         ", "
         (Term.app `LinearMap.adjoint [`T (Term.app `T [`x])])
         "⟫")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»
       "⟪"
       `x
       ", "
       (Term.app `LinearMap.adjoint [`T (Term.app `T [`x])])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Adjoint.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Adjoint.term⟪_,_⟫._@.Analysis.InnerProductSpace.Adjoint._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    im_inner_adjoint_mul_self_eq_zero
    ( T : E →ₗ[ 𝕜 ] E ) ( x : E ) : im ⟪ x , LinearMap.adjoint T T x ⟫ = 0
    := by simp only [ mul_apply , adjoint_inner_right , inner_self_eq_norm_sq_to_K ] norm_cast
#align linear_map.im_inner_adjoint_mul_self_eq_zero LinearMap.im_inner_adjoint_mul_self_eq_zero

end LinearMap

namespace Matrix

variable {m n : Type _} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

open ComplexConjugate

/-- The adjoint of the linear map associated to a matrix is the linear map associated to the
conjugate transpose of that matrix. -/
theorem conj_transpose_eq_adjoint (A : Matrix m n 𝕜) :
    toLin' A.conjTranspose =
      @LinearMap.adjoint _ (EuclideanSpace 𝕜 n) (EuclideanSpace 𝕜 m) _ _ _ _ _ (toLin' A) :=
  by
  rw [@LinearMap.eq_adjoint_iff _ (EuclideanSpace 𝕜 m) (EuclideanSpace 𝕜 n)]
  intro x y
  convert dot_product_assoc (conj ∘ (id x : m → 𝕜)) y A using 1
  simp [dot_product, mul_vec, RingHom.map_sum, ← star_ring_end_apply, mul_comm]
#align matrix.conj_transpose_eq_adjoint Matrix.conj_transpose_eq_adjoint

end Matrix

