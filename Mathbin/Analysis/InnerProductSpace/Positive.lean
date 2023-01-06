/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker

! This file was ported from Lean 3 source module analysis.inner_product_space.positive
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.InnerProductSpace.Adjoint

/-!
# Positive operators

In this file we define positive operators in a Hilbert space. We follow Bourbaki's choice
of requiring self adjointness in the definition.

## Main definitions

* `is_positive` : a continuous linear map is positive if it is self adjoint and
  `∀ x, 0 ≤ re ⟪T x, x⟫`

## Main statements

* `continuous_linear_map.is_positive.conj_adjoint` : if `T : E →L[𝕜] E` is positive,
  then for any `S : E →L[𝕜] F`, `S ∘L T ∘L S†` is also positive.
* `continuous_linear_map.is_positive_iff_complex` : in a ***complex*** hilbert space,
  checking that `⟪T x, x⟫` is a nonnegative real number for all `x` suffices to prove that
  `T` is positive

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

Positive operator
-/


open InnerProductSpace IsROrC ContinuousLinearMap

open InnerProduct ComplexConjugate

namespace ContinuousLinearMap

variable {𝕜 E F : Type _} [IsROrC 𝕜] [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]
  [CompleteSpace E] [CompleteSpace F]

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/-- A continuous linear endomorphism `T` of a Hilbert space is **positive** if it is self adjoint
  and `∀ x, 0 ≤ re ⟪T x, x⟫`. -/
def IsPositive (T : E →L[𝕜] E) : Prop :=
  IsSelfAdjoint T ∧ ∀ x, 0 ≤ T.reApplyInnerSelf x
#align continuous_linear_map.is_positive ContinuousLinearMap.IsPositive

theorem IsPositive.is_self_adjoint {T : E →L[𝕜] E} (hT : IsPositive T) : IsSelfAdjoint T :=
  hT.1
#align
  continuous_linear_map.is_positive.is_self_adjoint ContinuousLinearMap.IsPositive.is_self_adjoint

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `IsPositive.inner_nonneg_left [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`T]
         [":" (Topology.Algebra.Module.Basic.«term_→L[_]_» `E " →L[" `𝕜 "] " `E)]
         "}")
        (Term.explicitBinder "(" [`hT] [":" (Term.app `IsPositive [`T])] [] ")")
        (Term.explicitBinder "(" [`x] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         (num "0")
         "≤"
         (Term.app
          `re
          [(ContinuousLinearMap.Analysis.InnerProductSpace.Positive.«term⟪_,_⟫»
            "⟪"
            (Term.app `T [`x])
            ", "
            `x
            "⟫")]))))
      (Command.declValSimple ":=" (Term.app (Term.proj `hT "." (fieldIdx "2")) [`x]) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `hT "." (fieldIdx "2")) [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `hT "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hT
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≤_»
       (num "0")
       "≤"
       (Term.app
        `re
        [(ContinuousLinearMap.Analysis.InnerProductSpace.Positive.«term⟪_,_⟫»
          "⟪"
          (Term.app `T [`x])
          ", "
          `x
          "⟫")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `re
       [(ContinuousLinearMap.Analysis.InnerProductSpace.Positive.«term⟪_,_⟫»
         "⟪"
         (Term.app `T [`x])
         ", "
         `x
         "⟫")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ContinuousLinearMap.Analysis.InnerProductSpace.Positive.«term⟪_,_⟫»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ContinuousLinearMap.Analysis.InnerProductSpace.Positive.«term⟪_,_⟫»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (ContinuousLinearMap.Analysis.InnerProductSpace.Positive.«term⟪_,_⟫»
       "⟪"
       (Term.app `T [`x])
       ", "
       `x
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ContinuousLinearMap.Analysis.InnerProductSpace.Positive.«term⟪_,_⟫»', expected 'ContinuousLinearMap.Analysis.InnerProductSpace.Positive.term⟪_,_⟫._@.Analysis.InnerProductSpace.Positive._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  IsPositive.inner_nonneg_left
  { T : E →L[ 𝕜 ] E } ( hT : IsPositive T ) ( x : E ) : 0 ≤ re ⟪ T x , x ⟫
  := hT . 2 x
#align
  continuous_linear_map.is_positive.inner_nonneg_left ContinuousLinearMap.IsPositive.inner_nonneg_left

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `IsPositive.inner_nonneg_right [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`T]
         [":" (Topology.Algebra.Module.Basic.«term_→L[_]_» `E " →L[" `𝕜 "] " `E)]
         "}")
        (Term.explicitBinder "(" [`hT] [":" (Term.app `IsPositive [`T])] [] ")")
        (Term.explicitBinder "(" [`x] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         (num "0")
         "≤"
         (Term.app
          `re
          [(ContinuousLinearMap.Analysis.InnerProductSpace.Positive.«term⟪_,_⟫»
            "⟪"
            `x
            ", "
            (Term.app `T [`x])
            "⟫")]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `inner_re_symm)] "]") [])
            "<;>"
            (Tactic.exact "exact" (Term.app `hT.inner_nonneg_left [`x])))])))
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
         [(Tactic.«tactic_<;>_»
           (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `inner_re_symm)] "]") [])
           "<;>"
           (Tactic.exact "exact" (Term.app `hT.inner_nonneg_left [`x])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `inner_re_symm)] "]") [])
       "<;>"
       (Tactic.exact "exact" (Term.app `hT.inner_nonneg_left [`x])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `hT.inner_nonneg_left [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hT.inner_nonneg_left [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hT.inner_nonneg_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `inner_re_symm)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner_re_symm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≤_»
       (num "0")
       "≤"
       (Term.app
        `re
        [(ContinuousLinearMap.Analysis.InnerProductSpace.Positive.«term⟪_,_⟫»
          "⟪"
          `x
          ", "
          (Term.app `T [`x])
          "⟫")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `re
       [(ContinuousLinearMap.Analysis.InnerProductSpace.Positive.«term⟪_,_⟫»
         "⟪"
         `x
         ", "
         (Term.app `T [`x])
         "⟫")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ContinuousLinearMap.Analysis.InnerProductSpace.Positive.«term⟪_,_⟫»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ContinuousLinearMap.Analysis.InnerProductSpace.Positive.«term⟪_,_⟫»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (ContinuousLinearMap.Analysis.InnerProductSpace.Positive.«term⟪_,_⟫»
       "⟪"
       `x
       ", "
       (Term.app `T [`x])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ContinuousLinearMap.Analysis.InnerProductSpace.Positive.«term⟪_,_⟫»', expected 'ContinuousLinearMap.Analysis.InnerProductSpace.Positive.term⟪_,_⟫._@.Analysis.InnerProductSpace.Positive._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  IsPositive.inner_nonneg_right
  { T : E →L[ 𝕜 ] E } ( hT : IsPositive T ) ( x : E ) : 0 ≤ re ⟪ x , T x ⟫
  := by rw [ inner_re_symm ] <;> exact hT.inner_nonneg_left x
#align
  continuous_linear_map.is_positive.inner_nonneg_right ContinuousLinearMap.IsPositive.inner_nonneg_right

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `isPositiveZero [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `IsPositive
         [(Term.typeAscription
           "("
           (num "0")
           ":"
           [(Topology.Algebra.Module.Basic.«term_→L[_]_» `E " →L[" `𝕜 "] " `E)]
           ")")])))
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
             [(Term.app `is_self_adjoint_zero [(Term.hole "_")])
              ","
              (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))]
             "⟩"))
           []
           (Tactic.change
            "change"
            («term_≤_»
             (num "0")
             "≤"
             (Term.app
              `re
              [(ContinuousLinearMap.Analysis.InnerProductSpace.Positive.«term⟪_,_⟫»
                "⟪"
                (Term.hole "_")
                ", "
                (Term.hole "_")
                "⟫")]))
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `zero_apply)
              ","
              (Tactic.rwRule [] `inner_zero_left)
              ","
              (Tactic.rwRule [] `ZeroHomClass.map_zero)]
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
           (Term.anonymousCtor
            "⟨"
            [(Term.app `is_self_adjoint_zero [(Term.hole "_")])
             ","
             (Term.fun "fun" (Term.basicFun [`x] [] "=>" (Term.hole "_")))]
            "⟩"))
          []
          (Tactic.change
           "change"
           («term_≤_»
            (num "0")
            "≤"
            (Term.app
             `re
             [(ContinuousLinearMap.Analysis.InnerProductSpace.Positive.«term⟪_,_⟫»
               "⟪"
               (Term.hole "_")
               ", "
               (Term.hole "_")
               "⟫")]))
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `zero_apply)
             ","
             (Tactic.rwRule [] `inner_zero_left)
             ","
             (Tactic.rwRule [] `ZeroHomClass.map_zero)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `zero_apply)
         ","
         (Tactic.rwRule [] `inner_zero_left)
         ","
         (Tactic.rwRule [] `ZeroHomClass.map_zero)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ZeroHomClass.map_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner_zero_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       («term_≤_»
        (num "0")
        "≤"
        (Term.app
         `re
         [(ContinuousLinearMap.Analysis.InnerProductSpace.Positive.«term⟪_,_⟫»
           "⟪"
           (Term.hole "_")
           ", "
           (Term.hole "_")
           "⟫")]))
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (num "0")
       "≤"
       (Term.app
        `re
        [(ContinuousLinearMap.Analysis.InnerProductSpace.Positive.«term⟪_,_⟫»
          "⟪"
          (Term.hole "_")
          ", "
          (Term.hole "_")
          "⟫")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `re
       [(ContinuousLinearMap.Analysis.InnerProductSpace.Positive.«term⟪_,_⟫»
         "⟪"
         (Term.hole "_")
         ", "
         (Term.hole "_")
         "⟫")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ContinuousLinearMap.Analysis.InnerProductSpace.Positive.«term⟪_,_⟫»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ContinuousLinearMap.Analysis.InnerProductSpace.Positive.«term⟪_,_⟫»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (ContinuousLinearMap.Analysis.InnerProductSpace.Positive.«term⟪_,_⟫»
       "⟪"
       (Term.hole "_")
       ", "
       (Term.hole "_")
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ContinuousLinearMap.Analysis.InnerProductSpace.Positive.«term⟪_,_⟫»', expected 'ContinuousLinearMap.Analysis.InnerProductSpace.Positive.term⟪_,_⟫._@.Analysis.InnerProductSpace.Positive._hyg.7'
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
  isPositiveZero
  : IsPositive ( 0 : E →L[ 𝕜 ] E )
  :=
    by
      refine' ⟨ is_self_adjoint_zero _ , fun x => _ ⟩
        change 0 ≤ re ⟪ _ , _ ⟫
        rw [ zero_apply , inner_zero_left , ZeroHomClass.map_zero ]
#align continuous_linear_map.is_positive_zero ContinuousLinearMap.isPositiveZero

theorem isPositiveOne : IsPositive (1 : E →L[𝕜] E) :=
  ⟨is_self_adjoint_one _, fun x => inner_self_nonneg⟩
#align continuous_linear_map.is_positive_one ContinuousLinearMap.isPositiveOne

theorem IsPositive.add {T S : E →L[𝕜] E} (hT : T.IsPositive) (hS : S.IsPositive) :
    (T + S).IsPositive :=
  by
  refine' ⟨hT.is_self_adjoint.add hS.is_self_adjoint, fun x => _⟩
  rw [re_apply_inner_self, add_apply, inner_add_left, map_add]
  exact add_nonneg (hT.inner_nonneg_left x) (hS.inner_nonneg_left x)
#align continuous_linear_map.is_positive.add ContinuousLinearMap.IsPositive.add

theorem IsPositive.conjAdjoint {T : E →L[𝕜] E} (hT : T.IsPositive) (S : E →L[𝕜] F) :
    (S ∘L T ∘L S†).IsPositive :=
  by
  refine' ⟨hT.is_self_adjoint.conj_adjoint S, fun x => _⟩
  rw [re_apply_inner_self, comp_apply, ← adjoint_inner_right]
  exact hT.inner_nonneg_left _
#align continuous_linear_map.is_positive.conj_adjoint ContinuousLinearMap.IsPositive.conjAdjoint

theorem IsPositive.adjointConj {T : E →L[𝕜] E} (hT : T.IsPositive) (S : F →L[𝕜] E) :
    (S† ∘L T ∘L S).IsPositive := by
  convert hT.conj_adjoint (S†)
  rw [adjoint_adjoint]
#align continuous_linear_map.is_positive.adjoint_conj ContinuousLinearMap.IsPositive.adjointConj

theorem IsPositive.conjOrthogonalProjection (U : Submodule 𝕜 E) {T : E →L[𝕜] E} (hT : T.IsPositive)
    [CompleteSpace U] :
    (U.subtypeL ∘L
        orthogonalProjection U ∘L T ∘L U.subtypeL ∘L orthogonalProjection U).IsPositive :=
  by
  have := hT.conj_adjoint (U.subtypeL ∘L orthogonalProjection U)
  rwa [(orthogonal_projection_is_self_adjoint U).adjoint_eq] at this
#align
  continuous_linear_map.is_positive.conj_orthogonal_projection ContinuousLinearMap.IsPositive.conjOrthogonalProjection

theorem IsPositive.orthogonalProjectionComp {T : E →L[𝕜] E} (hT : T.IsPositive) (U : Submodule 𝕜 E)
    [CompleteSpace U] : (orthogonalProjection U ∘L T ∘L U.subtypeL).IsPositive :=
  by
  have := hT.conj_adjoint (orthogonalProjection U : E →L[𝕜] U)
  rwa [U.adjoint_orthogonal_projection] at this
#align
  continuous_linear_map.is_positive.orthogonal_projection_comp ContinuousLinearMap.IsPositive.orthogonalProjectionComp

section Complex

variable {E' : Type _} [InnerProductSpace ℂ E'] [CompleteSpace E']

theorem is_positive_iff_complex (T : E' →L[ℂ] E') :
    IsPositive T ↔ ∀ x, (re ⟪T x, x⟫_ℂ : ℂ) = ⟪T x, x⟫_ℂ ∧ 0 ≤ re ⟪T x, x⟫_ℂ :=
  by
  simp_rw [is_positive, forall_and, is_self_adjoint_iff_is_symmetric,
    LinearMap.is_symmetric_iff_inner_map_self_real, eq_conj_iff_re]
  rfl
#align continuous_linear_map.is_positive_iff_complex ContinuousLinearMap.is_positive_iff_complex

end Complex

end ContinuousLinearMap

