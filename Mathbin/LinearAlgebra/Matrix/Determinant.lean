/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Tim Baanen

! This file was ported from Lean 3 source module linear_algebra.matrix.determinant
! leanprover-community/mathlib commit 6afc9b06856ad973f6a2619e3e8a0a8d537a58f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Matrix.Pequiv
import Mathbin.Data.Matrix.Block
import Mathbin.Data.Matrix.Notation
import Mathbin.Data.Fintype.BigOperators
import Mathbin.GroupTheory.Perm.Fin
import Mathbin.GroupTheory.Perm.Sign
import Mathbin.Algebra.Algebra.Basic
import Mathbin.Tactic.Ring
import Mathbin.LinearAlgebra.Alternating
import Mathbin.LinearAlgebra.Pi

/-!
# Determinant of a matrix

This file defines the determinant of a matrix, `matrix.det`, and its essential properties.

## Main definitions

 - `matrix.det`: the determinant of a square matrix, as a sum over permutations
 - `matrix.det_row_alternating`: the determinant, as an `alternating_map` in the rows of the matrix

## Main results

 - `det_mul`: the determinant of `A ⬝ B` is the product of determinants
 - `det_zero_of_row_eq`: the determinant is zero if there is a repeated row
 - `det_block_diagonal`: the determinant of a block diagonal matrix is a product
   of the blocks' determinants

## Implementation notes

It is possible to configure `simp` to compute determinants. See the file
`test/matrix.lean` for some examples.

-/


universe u v w z

open Equiv Equiv.Perm Finset Function

namespace Matrix

open Matrix BigOperators

variable {m n : Type _} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

-- mathport name: «exprε »
local notation "ε " σ:arg => ((sign σ : ℤ) : R)

/-- `det` is an `alternating_map` in the rows of the matrix. -/
def detRowAlternating : AlternatingMap R (n → R) R n :=
  ((MultilinearMap.mkPiAlgebra R n R).compLinearMap LinearMap.proj).alternatization
#align matrix.det_row_alternating Matrix.detRowAlternating

/-- The determinant of a matrix given by the Leibniz formula. -/
abbrev det (M : Matrix n n R) : R :=
  detRowAlternating M
#align matrix.det Matrix.det

theorem det_apply (M : Matrix n n R) : M.det = ∑ σ : Perm n, σ.sign • ∏ i, M (σ i) i :=
  MultilinearMap.alternatization_apply _ M
#align matrix.det_apply Matrix.det_apply

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `det_apply' [])
      (Command.declSig
       [(Term.explicitBinder "(" [`M] [":" (Term.app `Matrix [`n `n `R])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.proj `M "." `det)
         "="
         (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
          "∑"
          (Std.ExtendedBinder.extBinders
           (Std.ExtendedBinder.extBinder (Lean.binderIdent `σ) [(group ":" (Term.app `Perm [`n]))]))
          ", "
          («term_*_»
           (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `σ)
           "*"
           (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
            "∏"
            (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
            ", "
            (Term.app `M [(Term.app `σ [`i]) `i])))))))
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
            []
            ["["
             [(Tactic.simpLemma [] [] `det_apply) "," (Tactic.simpLemma [] [] `Units.smul_def)]
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
           []
           ["["
            [(Tactic.simpLemma [] [] `det_apply) "," (Tactic.simpLemma [] [] `Units.smul_def)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["[" [(Tactic.simpLemma [] [] `det_apply) "," (Tactic.simpLemma [] [] `Units.smul_def)] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Units.smul_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `det_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.proj `M "." `det)
       "="
       (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
        "∑"
        (Std.ExtendedBinder.extBinders
         (Std.ExtendedBinder.extBinder (Lean.binderIdent `σ) [(group ":" (Term.app `Perm [`n]))]))
        ", "
        («term_*_»
         (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `σ)
         "*"
         (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
          "∏"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
          ", "
          (Term.app `M [(Term.app `σ [`i]) `i])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
       "∑"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder (Lean.binderIdent `σ) [(group ":" (Term.app `Perm [`n]))]))
       ", "
       («term_*_»
        (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `σ)
        "*"
        (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
         "∏"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
         ", "
         (Term.app `M [(Term.app `σ [`i]) `i]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `σ)
       "*"
       (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
        "∏"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
        ", "
        (Term.app `M [(Term.app `σ [`i]) `i])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
       "∏"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
       ", "
       (Term.app `M [(Term.app `σ [`i]) `i]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `M [(Term.app `σ [`i]) `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `σ [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `σ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `σ [`i]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `M
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `σ)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.LinearAlgebra.Matrix.Determinant.termε_', expected 'Matrix.LinearAlgebra.Matrix.Determinant.termε_._@.LinearAlgebra.Matrix.Determinant._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  det_apply'
  ( M : Matrix n n R ) : M . det = ∑ σ : Perm n , ε σ * ∏ i , M σ i i
  := by simp [ det_apply , Units.smul_def ]
#align matrix.det_apply' Matrix.det_apply'

@[simp]
theorem det_diagonal {d : n → R} : det (diagonal d) = ∏ i, d i :=
  by
  rw [det_apply']
  refine' (Finset.sum_eq_single 1 _ _).trans _
  · intro σ h1 h2
    cases' not_forall.1 (mt Equiv.ext h2) with x h3
    convert mul_zero _
    apply Finset.prod_eq_zero
    · change x ∈ _
      simp
    exact if_neg h3
  · simp
  · simp
#align matrix.det_diagonal Matrix.det_diagonal

@[simp]
theorem det_zero (h : Nonempty n) : det (0 : Matrix n n R) = 0 :=
  (detRowAlternating : AlternatingMap R (n → R) R n).map_zero
#align matrix.det_zero Matrix.det_zero

@[simp]
theorem det_one : det (1 : Matrix n n R) = 1 := by rw [← diagonal_one] <;> simp [-diagonal_one]
#align matrix.det_one Matrix.det_one

theorem det_is_empty [IsEmpty n] {A : Matrix n n R} : det A = 1 := by simp [det_apply]
#align matrix.det_is_empty Matrix.det_is_empty

@[simp]
theorem coe_det_is_empty [IsEmpty n] : (det : Matrix n n R → R) = Function.const _ 1 :=
  by
  ext
  exact det_is_empty
#align matrix.coe_det_is_empty Matrix.coe_det_is_empty

theorem det_eq_one_of_card_eq_zero {A : Matrix n n R} (h : Fintype.card n = 0) : det A = 1 :=
  haveI : IsEmpty n := fintype.card_eq_zero_iff.mp h
  det_is_empty
#align matrix.det_eq_one_of_card_eq_zero Matrix.det_eq_one_of_card_eq_zero

/-- If `n` has only one element, the determinant of an `n` by `n` matrix is just that element.
Although `unique` implies `decidable_eq` and `fintype`, the instances might
not be syntactically equal. Thus, we need to fill in the args explicitly. -/
@[simp]
theorem det_unique {n : Type _} [Unique n] [DecidableEq n] [Fintype n] (A : Matrix n n R) :
    det A = A default default := by simp [det_apply, univ_unique]
#align matrix.det_unique Matrix.det_unique

theorem det_eq_elem_of_subsingleton [Subsingleton n] (A : Matrix n n R) (k : n) : det A = A k k :=
  by
  convert det_unique _
  exact uniqueOfSubsingleton k
#align matrix.det_eq_elem_of_subsingleton Matrix.det_eq_elem_of_subsingleton

theorem det_eq_elem_of_card_eq_one {A : Matrix n n R} (h : Fintype.card n = 1) (k : n) :
    det A = A k k :=
  haveI : Subsingleton n := fintype.card_le_one_iff_subsingleton.mp h.le
  det_eq_elem_of_subsingleton _ _
#align matrix.det_eq_elem_of_card_eq_one Matrix.det_eq_elem_of_card_eq_one

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `det_mul_aux [])
      (Command.declSig
       [(Term.implicitBinder "{" [`M `N] [":" (Term.app `Matrix [`n `n `R])] "}")
        (Term.implicitBinder "{" [`p] [":" (Term.arrow `n "→" `n)] "}")
        (Term.explicitBinder "(" [`H] [":" («term¬_» "¬" (Term.app `Bijective [`p]))] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
          "∑"
          (Std.ExtendedBinder.extBinders
           (Std.ExtendedBinder.extBinder (Lean.binderIdent `σ) [(group ":" (Term.app `Perm [`n]))]))
          ", "
          («term_*_»
           (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `σ)
           "*"
           (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
            "∏"
            (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
            ", "
            («term_*_»
             (Term.app `M [(Term.app `σ [`x]) (Term.app `p [`x])])
             "*"
             (Term.app `N [(Term.app `p [`x]) `x])))))
         "="
         (num "0"))))
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
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hpij)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hij)])
                  [])]
                "⟩")])]
            [":"
             («term∃_,_»
              "∃"
              (Lean.explicitBinders
               (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i) (Lean.binderIdent `j)] []))
              ","
              («term_∧_»
               («term_=_» (Term.app `p [`i]) "=" (Term.app `p [`j]))
               "∧"
               («term_≠_» `i "≠" `j)))]
            [":="
             [(Term.byTactic
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
                      `Finite.injective_iff_bijective)
                     ","
                     (Tactic.rwRule [] `injective)]
                    "]")
                   [(Tactic.location "at" (Tactic.locationHyp [`H] []))])
                  []
                  (Mathlib.Tactic.PushNeg.tacticPush_neg__
                   "push_neg"
                   [(Tactic.location "at" (Tactic.locationHyp [`H] []))])
                  []
                  (Tactic.exact "exact" `H)])))]])
           []
           (Tactic.exact
            "exact"
            (Term.app
             `sum_involution
             [(Term.fun
               "fun"
               (Term.basicFun
                [`σ (Term.hole "_")]
                []
                "=>"
                («term_*_» `σ "*" (Term.app `swap [`i `j]))))
              (Term.fun
               "fun"
               (Term.basicFun
                [`σ (Term.hole "_")]
                []
                "=>"
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
                          (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                           "∏"
                           (Std.ExtendedBinder.extBinders
                            (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                           ", "
                           (Term.app `M [(Term.app `σ [`x]) (Term.app `p [`x])]))
                          "="
                          (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                           "∏"
                           (Std.ExtendedBinder.extBinders
                            (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                           ", "
                           (Term.app
                            `M
                            [(Term.app («term_*_» `σ "*" (Term.app `swap [`i `j])) [`x])
                             (Term.app `p [`x])]))))]
                       ":="
                       (Term.app
                        `Fintype.prod_equiv
                        [(Term.app `swap [`i `j])
                         (Term.hole "_")
                         (Term.hole "_")
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
                               [(Tactic.simpLemma [] [] (Term.app `apply_swap_eq_self [`hpij]))]
                               "]"]
                              [])])))]))))
                    []
                    (Tactic.simp
                     "simp"
                     []
                     []
                     []
                     ["["
                      [(Tactic.simpLemma [] [] `this)
                       ","
                       (Tactic.simpLemma [] [] (Term.app `sign_swap [`hij]))
                       ","
                       (Tactic.simpLemma [] [] `prod_mul_distrib)]
                      "]"]
                     [])])))))
              (Term.fun
               "fun"
               (Term.basicFun
                [`σ (Term.hole "_") (Term.hole "_")]
                []
                "=>"
                (Term.app (Term.proj (Term.app `not_congr [`mul_swap_eq_iff]) "." `mpr) [`hij])))
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.hole "_") (Term.hole "_")]
                []
                "=>"
                (Term.app `mem_univ [(Term.hole "_")])))
              (Term.fun
               "fun"
               (Term.basicFun
                [`σ (Term.hole "_")]
                []
                "=>"
                (Term.app `mul_swap_involutive [`i `j `σ])))]))])))
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
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hpij)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hij)])
                 [])]
               "⟩")])]
           [":"
            («term∃_,_»
             "∃"
             (Lean.explicitBinders
              (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i) (Lean.binderIdent `j)] []))
             ","
             («term_∧_»
              («term_=_» (Term.app `p [`i]) "=" (Term.app `p [`j]))
              "∧"
              («term_≠_» `i "≠" `j)))]
           [":="
            [(Term.byTactic
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
                     `Finite.injective_iff_bijective)
                    ","
                    (Tactic.rwRule [] `injective)]
                   "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`H] []))])
                 []
                 (Mathlib.Tactic.PushNeg.tacticPush_neg__
                  "push_neg"
                  [(Tactic.location "at" (Tactic.locationHyp [`H] []))])
                 []
                 (Tactic.exact "exact" `H)])))]])
          []
          (Tactic.exact
           "exact"
           (Term.app
            `sum_involution
            [(Term.fun
              "fun"
              (Term.basicFun
               [`σ (Term.hole "_")]
               []
               "=>"
               («term_*_» `σ "*" (Term.app `swap [`i `j]))))
             (Term.fun
              "fun"
              (Term.basicFun
               [`σ (Term.hole "_")]
               []
               "=>"
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
                         (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                          "∏"
                          (Std.ExtendedBinder.extBinders
                           (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                          ", "
                          (Term.app `M [(Term.app `σ [`x]) (Term.app `p [`x])]))
                         "="
                         (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                          "∏"
                          (Std.ExtendedBinder.extBinders
                           (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                          ", "
                          (Term.app
                           `M
                           [(Term.app («term_*_» `σ "*" (Term.app `swap [`i `j])) [`x])
                            (Term.app `p [`x])]))))]
                      ":="
                      (Term.app
                       `Fintype.prod_equiv
                       [(Term.app `swap [`i `j])
                        (Term.hole "_")
                        (Term.hole "_")
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
                              [(Tactic.simpLemma [] [] (Term.app `apply_swap_eq_self [`hpij]))]
                              "]"]
                             [])])))]))))
                   []
                   (Tactic.simp
                    "simp"
                    []
                    []
                    []
                    ["["
                     [(Tactic.simpLemma [] [] `this)
                      ","
                      (Tactic.simpLemma [] [] (Term.app `sign_swap [`hij]))
                      ","
                      (Tactic.simpLemma [] [] `prod_mul_distrib)]
                     "]"]
                    [])])))))
             (Term.fun
              "fun"
              (Term.basicFun
               [`σ (Term.hole "_") (Term.hole "_")]
               []
               "=>"
               (Term.app (Term.proj (Term.app `not_congr [`mul_swap_eq_iff]) "." `mpr) [`hij])))
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.hole "_") (Term.hole "_")]
               []
               "=>"
               (Term.app `mem_univ [(Term.hole "_")])))
             (Term.fun
              "fun"
              (Term.basicFun
               [`σ (Term.hole "_")]
               []
               "=>"
               (Term.app `mul_swap_involutive [`i `j `σ])))]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `sum_involution
        [(Term.fun
          "fun"
          (Term.basicFun [`σ (Term.hole "_")] [] "=>" («term_*_» `σ "*" (Term.app `swap [`i `j]))))
         (Term.fun
          "fun"
          (Term.basicFun
           [`σ (Term.hole "_")]
           []
           "=>"
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
                     (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                      "∏"
                      (Std.ExtendedBinder.extBinders
                       (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                      ", "
                      (Term.app `M [(Term.app `σ [`x]) (Term.app `p [`x])]))
                     "="
                     (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                      "∏"
                      (Std.ExtendedBinder.extBinders
                       (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                      ", "
                      (Term.app
                       `M
                       [(Term.app («term_*_» `σ "*" (Term.app `swap [`i `j])) [`x])
                        (Term.app `p [`x])]))))]
                  ":="
                  (Term.app
                   `Fintype.prod_equiv
                   [(Term.app `swap [`i `j])
                    (Term.hole "_")
                    (Term.hole "_")
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.simp
                         "simp"
                         []
                         []
                         []
                         ["[" [(Tactic.simpLemma [] [] (Term.app `apply_swap_eq_self [`hpij]))] "]"]
                         [])])))]))))
               []
               (Tactic.simp
                "simp"
                []
                []
                []
                ["["
                 [(Tactic.simpLemma [] [] `this)
                  ","
                  (Tactic.simpLemma [] [] (Term.app `sign_swap [`hij]))
                  ","
                  (Tactic.simpLemma [] [] `prod_mul_distrib)]
                 "]"]
                [])])))))
         (Term.fun
          "fun"
          (Term.basicFun
           [`σ (Term.hole "_") (Term.hole "_")]
           []
           "=>"
           (Term.app (Term.proj (Term.app `not_congr [`mul_swap_eq_iff]) "." `mpr) [`hij])))
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.hole "_") (Term.hole "_")]
           []
           "=>"
           (Term.app `mem_univ [(Term.hole "_")])))
         (Term.fun
          "fun"
          (Term.basicFun
           [`σ (Term.hole "_")]
           []
           "=>"
           (Term.app `mul_swap_involutive [`i `j `σ])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `sum_involution
       [(Term.fun
         "fun"
         (Term.basicFun [`σ (Term.hole "_")] [] "=>" («term_*_» `σ "*" (Term.app `swap [`i `j]))))
        (Term.fun
         "fun"
         (Term.basicFun
          [`σ (Term.hole "_")]
          []
          "=>"
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
                    (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                     "∏"
                     (Std.ExtendedBinder.extBinders
                      (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                     ", "
                     (Term.app `M [(Term.app `σ [`x]) (Term.app `p [`x])]))
                    "="
                    (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                     "∏"
                     (Std.ExtendedBinder.extBinders
                      (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                     ", "
                     (Term.app
                      `M
                      [(Term.app («term_*_» `σ "*" (Term.app `swap [`i `j])) [`x])
                       (Term.app `p [`x])]))))]
                 ":="
                 (Term.app
                  `Fintype.prod_equiv
                  [(Term.app `swap [`i `j])
                   (Term.hole "_")
                   (Term.hole "_")
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Tactic.simp
                        "simp"
                        []
                        []
                        []
                        ["[" [(Tactic.simpLemma [] [] (Term.app `apply_swap_eq_self [`hpij]))] "]"]
                        [])])))]))))
              []
              (Tactic.simp
               "simp"
               []
               []
               []
               ["["
                [(Tactic.simpLemma [] [] `this)
                 ","
                 (Tactic.simpLemma [] [] (Term.app `sign_swap [`hij]))
                 ","
                 (Tactic.simpLemma [] [] `prod_mul_distrib)]
                "]"]
               [])])))))
        (Term.fun
         "fun"
         (Term.basicFun
          [`σ (Term.hole "_") (Term.hole "_")]
          []
          "=>"
          (Term.app (Term.proj (Term.app `not_congr [`mul_swap_eq_iff]) "." `mpr) [`hij])))
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.hole "_") (Term.hole "_")]
          []
          "=>"
          (Term.app `mem_univ [(Term.hole "_")])))
        (Term.fun
         "fun"
         (Term.basicFun [`σ (Term.hole "_")] [] "=>" (Term.app `mul_swap_involutive [`i `j `σ])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun [`σ (Term.hole "_")] [] "=>" (Term.app `mul_swap_involutive [`i `j `σ])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_swap_involutive [`i `j `σ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `σ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
      `mul_swap_involutive
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `σ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.hole "_") (Term.hole "_")]
        []
        "=>"
        (Term.app `mem_univ [(Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mem_univ [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mem_univ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.hole "_") (Term.hole "_")]
       []
       "=>"
       (Term.app `mem_univ [(Term.hole "_")])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`σ (Term.hole "_") (Term.hole "_")]
        []
        "=>"
        (Term.app (Term.proj (Term.app `not_congr [`mul_swap_eq_iff]) "." `mpr) [`hij])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `not_congr [`mul_swap_eq_iff]) "." `mpr) [`hij])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hij
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `not_congr [`mul_swap_eq_iff]) "." `mpr)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `not_congr [`mul_swap_eq_iff])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_swap_eq_iff
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `not_congr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `not_congr [`mul_swap_eq_iff])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `σ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`σ (Term.hole "_") (Term.hole "_")]
       []
       "=>"
       (Term.app
        (Term.proj (Term.paren "(" (Term.app `not_congr [`mul_swap_eq_iff]) ")") "." `mpr)
        [`hij])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`σ (Term.hole "_")]
        []
        "=>"
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
                  (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                   "∏"
                   (Std.ExtendedBinder.extBinders
                    (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                   ", "
                   (Term.app `M [(Term.app `σ [`x]) (Term.app `p [`x])]))
                  "="
                  (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                   "∏"
                   (Std.ExtendedBinder.extBinders
                    (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                   ", "
                   (Term.app
                    `M
                    [(Term.app («term_*_» `σ "*" (Term.app `swap [`i `j])) [`x])
                     (Term.app `p [`x])]))))]
               ":="
               (Term.app
                `Fintype.prod_equiv
                [(Term.app `swap [`i `j])
                 (Term.hole "_")
                 (Term.hole "_")
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.simp
                      "simp"
                      []
                      []
                      []
                      ["[" [(Tactic.simpLemma [] [] (Term.app `apply_swap_eq_self [`hpij]))] "]"]
                      [])])))]))))
            []
            (Tactic.simp
             "simp"
             []
             []
             []
             ["["
              [(Tactic.simpLemma [] [] `this)
               ","
               (Tactic.simpLemma [] [] (Term.app `sign_swap [`hij]))
               ","
               (Tactic.simpLemma [] [] `prod_mul_distrib)]
              "]"]
             [])])))))
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
                (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                 "∏"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                 ", "
                 (Term.app `M [(Term.app `σ [`x]) (Term.app `p [`x])]))
                "="
                (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                 "∏"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                 ", "
                 (Term.app
                  `M
                  [(Term.app («term_*_» `σ "*" (Term.app `swap [`i `j])) [`x])
                   (Term.app `p [`x])]))))]
             ":="
             (Term.app
              `Fintype.prod_equiv
              [(Term.app `swap [`i `j])
               (Term.hole "_")
               (Term.hole "_")
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.simp
                    "simp"
                    []
                    []
                    []
                    ["[" [(Tactic.simpLemma [] [] (Term.app `apply_swap_eq_self [`hpij]))] "]"]
                    [])])))]))))
          []
          (Tactic.simp
           "simp"
           []
           []
           []
           ["["
            [(Tactic.simpLemma [] [] `this)
             ","
             (Tactic.simpLemma [] [] (Term.app `sign_swap [`hij]))
             ","
             (Tactic.simpLemma [] [] `prod_mul_distrib)]
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
        [(Tactic.simpLemma [] [] `this)
         ","
         (Tactic.simpLemma [] [] (Term.app `sign_swap [`hij]))
         ","
         (Tactic.simpLemma [] [] `prod_mul_distrib)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `prod_mul_distrib
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `sign_swap [`hij])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hij
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sign_swap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
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
            (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
             "∏"
             (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
             ", "
             (Term.app `M [(Term.app `σ [`x]) (Term.app `p [`x])]))
            "="
            (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
             "∏"
             (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
             ", "
             (Term.app
              `M
              [(Term.app («term_*_» `σ "*" (Term.app `swap [`i `j])) [`x]) (Term.app `p [`x])]))))]
         ":="
         (Term.app
          `Fintype.prod_equiv
          [(Term.app `swap [`i `j])
           (Term.hole "_")
           (Term.hole "_")
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.simp
                "simp"
                []
                []
                []
                ["[" [(Tactic.simpLemma [] [] (Term.app `apply_swap_eq_self [`hpij]))] "]"]
                [])])))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Fintype.prod_equiv
       [(Term.app `swap [`i `j])
        (Term.hole "_")
        (Term.hole "_")
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.simp
             "simp"
             []
             []
             []
             ["[" [(Tactic.simpLemma [] [] (Term.app `apply_swap_eq_self [`hpij]))] "]"]
             [])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
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
           ["[" [(Tactic.simpLemma [] [] (Term.app `apply_swap_eq_self [`hpij]))] "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["[" [(Tactic.simpLemma [] [] (Term.app `apply_swap_eq_self [`hpij]))] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `apply_swap_eq_self [`hpij])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hpij
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `apply_swap_eq_self
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(Tactic.simp
          "simp"
          []
          []
          []
          ["[" [(Tactic.simpLemma [] [] (Term.app `apply_swap_eq_self [`hpij]))] "]"]
          [])])))
     ")")
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `swap [`i `j])
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
      `swap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `swap [`i `j]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Fintype.prod_equiv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
        "∏"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
        ", "
        (Term.app `M [(Term.app `σ [`x]) (Term.app `p [`x])]))
       "="
       (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
        "∏"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
        ", "
        (Term.app
         `M
         [(Term.app («term_*_» `σ "*" (Term.app `swap [`i `j])) [`x]) (Term.app `p [`x])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
       "∏"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
       ", "
       (Term.app
        `M
        [(Term.app («term_*_» `σ "*" (Term.app `swap [`i `j])) [`x]) (Term.app `p [`x])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `M [(Term.app («term_*_» `σ "*" (Term.app `swap [`i `j])) [`x]) (Term.app `p [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `p [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `p [`x]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app («term_*_» `σ "*" (Term.app `swap [`i `j])) [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      («term_*_» `σ "*" (Term.app `swap [`i `j]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `swap [`i `j])
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
      `swap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `σ
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 70, (some 71, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_*_» `σ "*" (Term.app `swap [`i `j]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.paren "(" («term_*_» `σ "*" (Term.app `swap [`i `j])) ")") [`x])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `M
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
       "∏"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
       ", "
       (Term.app `M [(Term.app `σ [`x]) (Term.app `p [`x])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `M [(Term.app `σ [`x]) (Term.app `p [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `p [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `p [`x]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `σ [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `σ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `σ [`x]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `M
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
      "∏"
      (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
      ", "
      (Term.app
       `M
       [(Term.paren "(" (Term.app `σ [`x]) ")") (Term.paren "(" (Term.app `p [`x]) ")")]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `σ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`σ (Term.hole "_")]
       []
       "=>"
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
                 (Term.paren
                  "("
                  (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                   "∏"
                   (Std.ExtendedBinder.extBinders
                    (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                   ", "
                   (Term.app
                    `M
                    [(Term.paren "(" (Term.app `σ [`x]) ")")
                     (Term.paren "(" (Term.app `p [`x]) ")")]))
                  ")")
                 "="
                 (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                  "∏"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
                  ", "
                  (Term.app
                   `M
                   [(Term.paren
                     "("
                     (Term.app
                      (Term.paren "(" («term_*_» `σ "*" (Term.app `swap [`i `j])) ")")
                      [`x])
                     ")")
                    (Term.paren "(" (Term.app `p [`x]) ")")]))))]
              ":="
              (Term.app
               `Fintype.prod_equiv
               [(Term.paren "(" (Term.app `swap [`i `j]) ")")
                (Term.hole "_")
                (Term.hole "_")
                (Term.paren
                 "("
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.simp
                      "simp"
                      []
                      []
                      []
                      ["[" [(Tactic.simpLemma [] [] (Term.app `apply_swap_eq_self [`hpij]))] "]"]
                      [])])))
                 ")")]))))
           []
           (Tactic.simp
            "simp"
            []
            []
            []
            ["["
             [(Tactic.simpLemma [] [] `this)
              ","
              (Tactic.simpLemma [] [] (Term.app `sign_swap [`hij]))
              ","
              (Tactic.simpLemma [] [] `prod_mul_distrib)]
             "]"]
            [])])))))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun [`σ (Term.hole "_")] [] "=>" («term_*_» `σ "*" (Term.app `swap [`i `j]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `σ "*" (Term.app `swap [`i `j]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `swap [`i `j])
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
      `swap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `σ
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `σ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun [`σ (Term.hole "_")] [] "=>" («term_*_» `σ "*" (Term.app `swap [`i `j]))))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sum_involution
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `i)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `j)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hpij)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hij)])
             [])]
           "⟩")])]
       [":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders
          (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i) (Lean.binderIdent `j)] []))
         ","
         («term_∧_»
          («term_=_» (Term.app `p [`i]) "=" (Term.app `p [`j]))
          "∧"
          («term_≠_» `i "≠" `j)))]
       [":="
        [(Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Finite.injective_iff_bijective)
                ","
                (Tactic.rwRule [] `injective)]
               "]")
              [(Tactic.location "at" (Tactic.locationHyp [`H] []))])
             []
             (Mathlib.Tactic.PushNeg.tacticPush_neg__
              "push_neg"
              [(Tactic.location "at" (Tactic.locationHyp [`H] []))])
             []
             (Tactic.exact "exact" `H)])))]])
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
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Finite.injective_iff_bijective)
             ","
             (Tactic.rwRule [] `injective)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`H] []))])
          []
          (Mathlib.Tactic.PushNeg.tacticPush_neg__
           "push_neg"
           [(Tactic.location "at" (Tactic.locationHyp [`H] []))])
          []
          (Tactic.exact "exact" `H)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `H)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.PushNeg.tacticPush_neg__
       "push_neg"
       [(Tactic.location "at" (Tactic.locationHyp [`H] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Finite.injective_iff_bijective)
         ","
         (Tactic.rwRule [] `injective)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`H] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `injective
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Finite.injective_iff_bijective
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders
        (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i) (Lean.binderIdent `j)] []))
       ","
       («term_∧_» («term_=_» (Term.app `p [`i]) "=" (Term.app `p [`j])) "∧" («term_≠_» `i "≠" `j)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∧_» («term_=_» (Term.app `p [`i]) "=" (Term.app `p [`j])) "∧" («term_≠_» `i "≠" `j))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» `i "≠" `j)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 35 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      («term_=_» (Term.app `p [`i]) "=" (Term.app `p [`j]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `p [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `p [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 36 >? 50, (some 51, term) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 35, (some 35, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'Lean.bracketedExplicitBinders'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
        "∑"
        (Std.ExtendedBinder.extBinders
         (Std.ExtendedBinder.extBinder (Lean.binderIdent `σ) [(group ":" (Term.app `Perm [`n]))]))
        ", "
        («term_*_»
         (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `σ)
         "*"
         (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
          "∏"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
          ", "
          («term_*_»
           (Term.app `M [(Term.app `σ [`x]) (Term.app `p [`x])])
           "*"
           (Term.app `N [(Term.app `p [`x]) `x])))))
       "="
       (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
       "∑"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder (Lean.binderIdent `σ) [(group ":" (Term.app `Perm [`n]))]))
       ", "
       («term_*_»
        (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `σ)
        "*"
        (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
         "∏"
         (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
         ", "
         («term_*_»
          (Term.app `M [(Term.app `σ [`x]) (Term.app `p [`x])])
          "*"
          (Term.app `N [(Term.app `p [`x]) `x])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `σ)
       "*"
       (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
        "∏"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
        ", "
        («term_*_»
         (Term.app `M [(Term.app `σ [`x]) (Term.app `p [`x])])
         "*"
         (Term.app `N [(Term.app `p [`x]) `x]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
       "∏"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) []))
       ", "
       («term_*_»
        (Term.app `M [(Term.app `σ [`x]) (Term.app `p [`x])])
        "*"
        (Term.app `N [(Term.app `p [`x]) `x])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.app `M [(Term.app `σ [`x]) (Term.app `p [`x])])
       "*"
       (Term.app `N [(Term.app `p [`x]) `x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `N [(Term.app `p [`x]) `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `p [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `p [`x]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `N
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `M [(Term.app `σ [`x]) (Term.app `p [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `p [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `p [`x]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `σ [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `σ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `σ [`x]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `M
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `σ)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.LinearAlgebra.Matrix.Determinant.termε_', expected 'Matrix.LinearAlgebra.Matrix.Determinant.termε_._@.LinearAlgebra.Matrix.Determinant._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  det_mul_aux
  { M N : Matrix n n R } { p : n → n } ( H : ¬ Bijective p )
    : ∑ σ : Perm n , ε σ * ∏ x , M σ x p x * N p x x = 0
  :=
    by
      obtain
          ⟨ i , j , hpij , hij ⟩
          : ∃ i j , p i = p j ∧ i ≠ j
          := by rw [ ← Finite.injective_iff_bijective , injective ] at H push_neg at H exact H
        exact
          sum_involution
            fun σ _ => σ * swap i j
              fun
                σ _
                  =>
                  by
                    have
                        : ∏ x , M σ x p x = ∏ x , M σ * swap i j x p x
                          :=
                          Fintype.prod_equiv swap i j _ _ by simp [ apply_swap_eq_self hpij ]
                      simp [ this , sign_swap hij , prod_mul_distrib ]
              fun σ _ _ => not_congr mul_swap_eq_iff . mpr hij
              fun _ _ => mem_univ _
              fun σ _ => mul_swap_involutive i j σ
#align matrix.det_mul_aux Matrix.det_mul_aux

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
      (Command.declId `det_mul [])
      (Command.declSig
       [(Term.explicitBinder "(" [`M `N] [":" (Term.app `Matrix [`n `n `R])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `det [(Matrix.Data.Matrix.Basic.matrix.mul `M " ⬝ " `N)])
         "="
         («term_*_» (Term.app `det [`M]) "*" (Term.app `det [`N])))))
      (Command.declValSimple
       ":="
       (calc
        "calc"
        (calcStep
         («term_=_»
          (Term.app `det [(Matrix.Data.Matrix.Basic.matrix.mul `M " ⬝ " `N)])
          "="
          (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
           "∑"
           (Std.ExtendedBinder.extBinders
            (Std.ExtendedBinder.extBinder
             (Lean.binderIdent `p)
             [(group ":" (Term.arrow `n "→" `n))]))
           ", "
           (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
            "∑"
            (Std.ExtendedBinder.extBinders
             (Std.ExtendedBinder.extBinder
              (Lean.binderIdent `σ)
              [(group ":" (Term.app `Perm [`n]))]))
            ", "
            («term_*_»
             (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `σ)
             "*"
             (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
              "∏"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
              ", "
              («term_*_»
               (Term.app `M [(Term.app `σ [`i]) (Term.app `p [`i])])
               "*"
               (Term.app `N [(Term.app `p [`i]) `i])))))))
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
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `det_apply')
                 ","
                 (Tactic.simpLemma [] [] `mul_apply)
                 ","
                 (Tactic.simpLemma [] [] `prod_univ_sum)
                 ","
                 (Tactic.simpLemma [] [] `mul_sum)
                 ","
                 (Tactic.simpLemma [] [] `Fintype.pi_finset_univ)]
                "]"]
               [])
              "<;>"
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.sum_comm)] "]")
               []))]))))
        [(calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (BigOperators.Algebra.BigOperators.Basic.finset.sum
            "∑"
            (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `p) []))
            " in "
            (Term.app
             (Term.proj
              (Term.app (Term.explicit "@" `univ) [(Term.arrow `n "→" `n) (Term.hole "_")])
              "."
              `filter)
             [`Bijective])
            ", "
            (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
             "∑"
             (Std.ExtendedBinder.extBinders
              (Std.ExtendedBinder.extBinder
               (Lean.binderIdent `σ)
               [(group ":" (Term.app `Perm [`n]))]))
             ", "
             («term_*_»
              (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `σ)
              "*"
              (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
               "∏"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
               ", "
               («term_*_»
                (Term.app `M [(Term.app `σ [`i]) (Term.app `p [`i])])
                "*"
                (Term.app `N [(Term.app `p [`i]) `i])))))))
          ":="
          («term_<|_»
           `Eq.symm
           "<|"
           (Term.app
            `sum_subset
            [(Term.app `filter_subset [(Term.hole "_") (Term.hole "_")])
             (Term.fun
              "fun"
              (Term.basicFun
               [`f (Term.hole "_") `hbij]
               []
               "=>"
               («term_<|_»
                `det_mul_aux
                "<|"
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
                      ["only"]
                      [(Tactic.simpArgs
                        "["
                        [(Tactic.simpLemma [] [] `true_and_iff)
                         ","
                         (Tactic.simpLemma [] [] `mem_filter)
                         ","
                         (Tactic.simpLemma [] [] `mem_univ)]
                        "]")]
                      ["using" `hbij]))]))))))])))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
            "∑"
            (Std.ExtendedBinder.extBinders
             (Std.ExtendedBinder.extBinder
              (Lean.binderIdent `τ)
              [(group ":" (Term.app `Perm [`n]))]))
            ", "
            (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
             "∑"
             (Std.ExtendedBinder.extBinders
              (Std.ExtendedBinder.extBinder
               (Lean.binderIdent `σ)
               [(group ":" (Term.app `Perm [`n]))]))
             ", "
             («term_*_»
              (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `σ)
              "*"
              (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
               "∏"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
               ", "
               («term_*_»
                (Term.app `M [(Term.app `σ [`i]) (Term.app `τ [`i])])
                "*"
                (Term.app `N [(Term.app `τ [`i]) `i])))))))
          ":="
          (Term.app
           `sum_bij
           [(Term.fun
             "fun"
             (Term.basicFun
              [`p `h]
              []
              "=>"
              (Term.app
               `Equiv.ofBijective
               [`p
                (Term.proj
                 (Term.app (Term.proj `mem_filter "." (fieldIdx "1")) [`h])
                 "."
                 (fieldIdx "2"))])))
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.hole "_") (Term.hole "_")]
              []
              "=>"
              (Term.app `mem_univ [(Term.hole "_")])))
            (Term.fun "fun" (Term.basicFun [(Term.hole "_") (Term.hole "_")] [] "=>" `rfl))
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") `h]
              []
              "=>"
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented [(Tactic.injection "injection" `h [])])))))
            (Term.fun
             "fun"
             (Term.basicFun
              [`b (Term.hole "_")]
              []
              "=>"
              (Term.anonymousCtor
               "⟨"
               [`b
                ","
                (Term.app
                 (Term.proj `mem_filter "." (fieldIdx "2"))
                 [(Term.anonymousCtor
                   "⟨"
                   [(Term.app `mem_univ [(Term.hole "_")]) "," (Term.proj `b "." `Bijective)]
                   "⟩")])
                ","
                (Term.app `coe_fn_injective [`rfl])]
               "⟩")))]))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
            "∑"
            (Std.ExtendedBinder.extBinders
             (Std.ExtendedBinder.extBinder
              (Lean.binderIdent `σ)
              [(group ":" (Term.app `Perm [`n]))]))
            ", "
            (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
             "∑"
             (Std.ExtendedBinder.extBinders
              (Std.ExtendedBinder.extBinder
               (Lean.binderIdent `τ)
               [(group ":" (Term.app `Perm [`n]))]))
             ", "
             («term_*_»
              («term_*_»
               (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                "∏"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                ", "
                (Term.app `N [(Term.app `σ [`i]) `i]))
               "*"
               (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `τ))
              "*"
              (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
               "∏"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
               ", "
               (Term.app `M [(Term.app `τ [`j]) (Term.app `σ [`j])]))))))
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
                [(Tactic.simpLemma [] [] `mul_comm)
                 ","
                 (Tactic.simpLemma [] [] `mul_left_comm)
                 ","
                 (Tactic.simpLemma [] [] `prod_mul_distrib)
                 ","
                 (Tactic.simpLemma [] [] `mul_assoc)]
                "]"]
               [])]))))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
            "∑"
            (Std.ExtendedBinder.extBinders
             (Std.ExtendedBinder.extBinder
              (Lean.binderIdent `σ)
              [(group ":" (Term.app `Perm [`n]))]))
            ", "
            (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
             "∑"
             (Std.ExtendedBinder.extBinders
              (Std.ExtendedBinder.extBinder
               (Lean.binderIdent `τ)
               [(group ":" (Term.app `Perm [`n]))]))
             ", "
             («term_*_»
              («term_*_»
               (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                "∏"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                ", "
                (Term.app `N [(Term.app `σ [`i]) `i]))
               "*"
               («term_*_»
                (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `σ)
                "*"
                (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `τ)))
              "*"
              (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
               "∏"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
               ", "
               (Term.app `M [(Term.app `τ [`i]) `i]))))))
          ":="
          (Term.app
           `sum_congr
           [`rfl
            (Term.fun
             "fun"
             (Term.basicFun
              [`σ (Term.hole "_")]
              []
              "=>"
              (Term.app
               `Fintype.sum_equiv
               [(Term.app `Equiv.mulRight [(«term_⁻¹» `σ "⁻¹")])
                (Term.hole "_")
                (Term.hole "_")
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`τ]
                  []
                  "=>"
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
                            (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                             "∏"
                             (Std.ExtendedBinder.extBinders
                              (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
                             ", "
                             (Term.app `M [(Term.app `τ [`j]) (Term.app `σ [`j])]))
                            "="
                            (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                             "∏"
                             (Std.ExtendedBinder.extBinders
                              (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
                             ", "
                             (Term.app
                              `M
                              [(Term.app («term_*_» `τ "*" («term_⁻¹» `σ "⁻¹")) [`j]) `j]))))]
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
                                 (Term.proj
                                  (Term.typeAscription
                                   "("
                                   («term_⁻¹» `σ "⁻¹")
                                   ":"
                                   [(Logic.Equiv.Defs.«term_≃_»
                                     (Term.hole "_")
                                     " ≃ "
                                     (Term.hole "_"))]
                                   ")")
                                  "."
                                  `prod_comp))]
                               "]")
                              [])
                             []
                             (Tactic.simp
                              "simp"
                              []
                              []
                              ["only"]
                              ["["
                               [(Tactic.simpLemma [] [] `Equiv.Perm.coe_mul)
                                ","
                                (Tactic.simpLemma [] [] `apply_inv_self)]
                               "]"]
                              [])]))))))
                      []
                      (Tactic.tacticHave_
                       "have"
                       (Term.haveDecl
                        (Term.haveIdDecl
                         [`h []]
                         [(Term.typeSpec
                           ":"
                           («term_=_»
                            («term_*_»
                             (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `σ)
                             "*"
                             (Matrix.LinearAlgebra.Matrix.Determinant.termε_
                              "ε "
                              («term_*_» `τ "*" («term_⁻¹» `σ "⁻¹"))))
                            "="
                            (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `τ)))]
                         ":="
                         (calc
                          "calc"
                          (calcStep
                           («term_=_»
                            («term_*_»
                             (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `σ)
                             "*"
                             (Matrix.LinearAlgebra.Matrix.Determinant.termε_
                              "ε "
                              («term_*_» `τ "*" («term_⁻¹» `σ "⁻¹"))))
                            "="
                            (Matrix.LinearAlgebra.Matrix.Determinant.termε_
                             "ε "
                             («term_*_» («term_*_» `τ "*" («term_⁻¹» `σ "⁻¹")) "*" `σ)))
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
                                 [(Tactic.rwRule [] `mul_comm)
                                  ","
                                  (Tactic.rwRule
                                   []
                                   (Term.app `sign_mul [(«term_*_» `τ "*" («term_⁻¹» `σ "⁻¹"))]))]
                                 "]")
                                [])
                               []
                               (Tactic.simp
                                "simp"
                                []
                                []
                                ["only"]
                                ["["
                                 [(Tactic.simpLemma [] [] `Int.cast_mul)
                                  ","
                                  (Tactic.simpLemma [] [] `Units.val_mul)]
                                 "]"]
                                [])]))))
                          [(calcStep
                            («term_=_»
                             (Term.hole "_")
                             "="
                             (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `τ))
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
                                 ["[" [(Tactic.simpLemma [] [] `inv_mul_cancel_right)] "]"]
                                 [])]))))]))))
                      []
                      (Mathlib.Tactic.tacticSimp_rw__
                       "simp_rw"
                       (Tactic.rwRuleSeq
                        "["
                        [(Tactic.rwRule [] `Equiv.coe_mulRight) "," (Tactic.rwRule [] `h)]
                        "]")
                       [])
                      []
                      (Tactic.simp
                       "simp"
                       []
                       []
                       ["only"]
                       ["[" [(Tactic.simpLemma [] [] `this)] "]"]
                       [])])))))])))]))
         (calcStep
          («term_=_» (Term.hole "_") "=" («term_*_» (Term.app `det [`M]) "*" (Term.app `det [`N])))
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
                [(Tactic.simpLemma [] [] `det_apply')
                 ","
                 (Tactic.simpLemma [] [] `Finset.mul_sum)
                 ","
                 (Tactic.simpLemma [] [] `mul_comm)
                 ","
                 (Tactic.simpLemma [] [] `mul_left_comm)]
                "]"]
               [])]))))])
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
         (Term.app `det [(Matrix.Data.Matrix.Basic.matrix.mul `M " ⬝ " `N)])
         "="
         (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
          "∑"
          (Std.ExtendedBinder.extBinders
           (Std.ExtendedBinder.extBinder
            (Lean.binderIdent `p)
            [(group ":" (Term.arrow `n "→" `n))]))
          ", "
          (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
           "∑"
           (Std.ExtendedBinder.extBinders
            (Std.ExtendedBinder.extBinder
             (Lean.binderIdent `σ)
             [(group ":" (Term.app `Perm [`n]))]))
           ", "
           («term_*_»
            (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `σ)
            "*"
            (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
             "∏"
             (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
             ", "
             («term_*_»
              (Term.app `M [(Term.app `σ [`i]) (Term.app `p [`i])])
              "*"
              (Term.app `N [(Term.app `p [`i]) `i])))))))
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
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `det_apply')
                ","
                (Tactic.simpLemma [] [] `mul_apply)
                ","
                (Tactic.simpLemma [] [] `prod_univ_sum)
                ","
                (Tactic.simpLemma [] [] `mul_sum)
                ","
                (Tactic.simpLemma [] [] `Fintype.pi_finset_univ)]
               "]"]
              [])
             "<;>"
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.sum_comm)] "]")
              []))]))))
       [(calcStep
         («term_=_»
          (Term.hole "_")
          "="
          (BigOperators.Algebra.BigOperators.Basic.finset.sum
           "∑"
           (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `p) []))
           " in "
           (Term.app
            (Term.proj
             (Term.app (Term.explicit "@" `univ) [(Term.arrow `n "→" `n) (Term.hole "_")])
             "."
             `filter)
            [`Bijective])
           ", "
           (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
            "∑"
            (Std.ExtendedBinder.extBinders
             (Std.ExtendedBinder.extBinder
              (Lean.binderIdent `σ)
              [(group ":" (Term.app `Perm [`n]))]))
            ", "
            («term_*_»
             (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `σ)
             "*"
             (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
              "∏"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
              ", "
              («term_*_»
               (Term.app `M [(Term.app `σ [`i]) (Term.app `p [`i])])
               "*"
               (Term.app `N [(Term.app `p [`i]) `i])))))))
         ":="
         («term_<|_»
          `Eq.symm
          "<|"
          (Term.app
           `sum_subset
           [(Term.app `filter_subset [(Term.hole "_") (Term.hole "_")])
            (Term.fun
             "fun"
             (Term.basicFun
              [`f (Term.hole "_") `hbij]
              []
              "=>"
              («term_<|_»
               `det_mul_aux
               "<|"
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
                     ["only"]
                     [(Tactic.simpArgs
                       "["
                       [(Tactic.simpLemma [] [] `true_and_iff)
                        ","
                        (Tactic.simpLemma [] [] `mem_filter)
                        ","
                        (Tactic.simpLemma [] [] `mem_univ)]
                       "]")]
                     ["using" `hbij]))]))))))])))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
           "∑"
           (Std.ExtendedBinder.extBinders
            (Std.ExtendedBinder.extBinder
             (Lean.binderIdent `τ)
             [(group ":" (Term.app `Perm [`n]))]))
           ", "
           (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
            "∑"
            (Std.ExtendedBinder.extBinders
             (Std.ExtendedBinder.extBinder
              (Lean.binderIdent `σ)
              [(group ":" (Term.app `Perm [`n]))]))
            ", "
            («term_*_»
             (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `σ)
             "*"
             (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
              "∏"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
              ", "
              («term_*_»
               (Term.app `M [(Term.app `σ [`i]) (Term.app `τ [`i])])
               "*"
               (Term.app `N [(Term.app `τ [`i]) `i])))))))
         ":="
         (Term.app
          `sum_bij
          [(Term.fun
            "fun"
            (Term.basicFun
             [`p `h]
             []
             "=>"
             (Term.app
              `Equiv.ofBijective
              [`p
               (Term.proj
                (Term.app (Term.proj `mem_filter "." (fieldIdx "1")) [`h])
                "."
                (fieldIdx "2"))])))
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.hole "_") (Term.hole "_")]
             []
             "=>"
             (Term.app `mem_univ [(Term.hole "_")])))
           (Term.fun "fun" (Term.basicFun [(Term.hole "_") (Term.hole "_")] [] "=>" `rfl))
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") `h]
             []
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented [(Tactic.injection "injection" `h [])])))))
           (Term.fun
            "fun"
            (Term.basicFun
             [`b (Term.hole "_")]
             []
             "=>"
             (Term.anonymousCtor
              "⟨"
              [`b
               ","
               (Term.app
                (Term.proj `mem_filter "." (fieldIdx "2"))
                [(Term.anonymousCtor
                  "⟨"
                  [(Term.app `mem_univ [(Term.hole "_")]) "," (Term.proj `b "." `Bijective)]
                  "⟩")])
               ","
               (Term.app `coe_fn_injective [`rfl])]
              "⟩")))]))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
           "∑"
           (Std.ExtendedBinder.extBinders
            (Std.ExtendedBinder.extBinder
             (Lean.binderIdent `σ)
             [(group ":" (Term.app `Perm [`n]))]))
           ", "
           (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
            "∑"
            (Std.ExtendedBinder.extBinders
             (Std.ExtendedBinder.extBinder
              (Lean.binderIdent `τ)
              [(group ":" (Term.app `Perm [`n]))]))
            ", "
            («term_*_»
             («term_*_»
              (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
               "∏"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
               ", "
               (Term.app `N [(Term.app `σ [`i]) `i]))
              "*"
              (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `τ))
             "*"
             (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
              "∏"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
              ", "
              (Term.app `M [(Term.app `τ [`j]) (Term.app `σ [`j])]))))))
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
               [(Tactic.simpLemma [] [] `mul_comm)
                ","
                (Tactic.simpLemma [] [] `mul_left_comm)
                ","
                (Tactic.simpLemma [] [] `prod_mul_distrib)
                ","
                (Tactic.simpLemma [] [] `mul_assoc)]
               "]"]
              [])]))))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
           "∑"
           (Std.ExtendedBinder.extBinders
            (Std.ExtendedBinder.extBinder
             (Lean.binderIdent `σ)
             [(group ":" (Term.app `Perm [`n]))]))
           ", "
           (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
            "∑"
            (Std.ExtendedBinder.extBinders
             (Std.ExtendedBinder.extBinder
              (Lean.binderIdent `τ)
              [(group ":" (Term.app `Perm [`n]))]))
            ", "
            («term_*_»
             («term_*_»
              (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
               "∏"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
               ", "
               (Term.app `N [(Term.app `σ [`i]) `i]))
              "*"
              («term_*_»
               (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `σ)
               "*"
               (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `τ)))
             "*"
             (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
              "∏"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
              ", "
              (Term.app `M [(Term.app `τ [`i]) `i]))))))
         ":="
         (Term.app
          `sum_congr
          [`rfl
           (Term.fun
            "fun"
            (Term.basicFun
             [`σ (Term.hole "_")]
             []
             "=>"
             (Term.app
              `Fintype.sum_equiv
              [(Term.app `Equiv.mulRight [(«term_⁻¹» `σ "⁻¹")])
               (Term.hole "_")
               (Term.hole "_")
               (Term.fun
                "fun"
                (Term.basicFun
                 [`τ]
                 []
                 "=>"
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
                           (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                            "∏"
                            (Std.ExtendedBinder.extBinders
                             (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
                            ", "
                            (Term.app `M [(Term.app `τ [`j]) (Term.app `σ [`j])]))
                           "="
                           (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                            "∏"
                            (Std.ExtendedBinder.extBinders
                             (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
                            ", "
                            (Term.app
                             `M
                             [(Term.app («term_*_» `τ "*" («term_⁻¹» `σ "⁻¹")) [`j]) `j]))))]
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
                                (Term.proj
                                 (Term.typeAscription
                                  "("
                                  («term_⁻¹» `σ "⁻¹")
                                  ":"
                                  [(Logic.Equiv.Defs.«term_≃_»
                                    (Term.hole "_")
                                    " ≃ "
                                    (Term.hole "_"))]
                                  ")")
                                 "."
                                 `prod_comp))]
                              "]")
                             [])
                            []
                            (Tactic.simp
                             "simp"
                             []
                             []
                             ["only"]
                             ["["
                              [(Tactic.simpLemma [] [] `Equiv.Perm.coe_mul)
                               ","
                               (Tactic.simpLemma [] [] `apply_inv_self)]
                              "]"]
                             [])]))))))
                     []
                     (Tactic.tacticHave_
                      "have"
                      (Term.haveDecl
                       (Term.haveIdDecl
                        [`h []]
                        [(Term.typeSpec
                          ":"
                          («term_=_»
                           («term_*_»
                            (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `σ)
                            "*"
                            (Matrix.LinearAlgebra.Matrix.Determinant.termε_
                             "ε "
                             («term_*_» `τ "*" («term_⁻¹» `σ "⁻¹"))))
                           "="
                           (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `τ)))]
                        ":="
                        (calc
                         "calc"
                         (calcStep
                          («term_=_»
                           («term_*_»
                            (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `σ)
                            "*"
                            (Matrix.LinearAlgebra.Matrix.Determinant.termε_
                             "ε "
                             («term_*_» `τ "*" («term_⁻¹» `σ "⁻¹"))))
                           "="
                           (Matrix.LinearAlgebra.Matrix.Determinant.termε_
                            "ε "
                            («term_*_» («term_*_» `τ "*" («term_⁻¹» `σ "⁻¹")) "*" `σ)))
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
                                [(Tactic.rwRule [] `mul_comm)
                                 ","
                                 (Tactic.rwRule
                                  []
                                  (Term.app `sign_mul [(«term_*_» `τ "*" («term_⁻¹» `σ "⁻¹"))]))]
                                "]")
                               [])
                              []
                              (Tactic.simp
                               "simp"
                               []
                               []
                               ["only"]
                               ["["
                                [(Tactic.simpLemma [] [] `Int.cast_mul)
                                 ","
                                 (Tactic.simpLemma [] [] `Units.val_mul)]
                                "]"]
                               [])]))))
                         [(calcStep
                           («term_=_»
                            (Term.hole "_")
                            "="
                            (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `τ))
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
                                ["[" [(Tactic.simpLemma [] [] `inv_mul_cancel_right)] "]"]
                                [])]))))]))))
                     []
                     (Mathlib.Tactic.tacticSimp_rw__
                      "simp_rw"
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [] `Equiv.coe_mulRight) "," (Tactic.rwRule [] `h)]
                       "]")
                      [])
                     []
                     (Tactic.simp
                      "simp"
                      []
                      []
                      ["only"]
                      ["[" [(Tactic.simpLemma [] [] `this)] "]"]
                      [])])))))])))]))
        (calcStep
         («term_=_» (Term.hole "_") "=" («term_*_» (Term.app `det [`M]) "*" (Term.app `det [`N])))
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
               [(Tactic.simpLemma [] [] `det_apply')
                ","
                (Tactic.simpLemma [] [] `Finset.mul_sum)
                ","
                (Tactic.simpLemma [] [] `mul_comm)
                ","
                (Tactic.simpLemma [] [] `mul_left_comm)]
               "]"]
              [])]))))])
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
            [(Tactic.simpLemma [] [] `det_apply')
             ","
             (Tactic.simpLemma [] [] `Finset.mul_sum)
             ","
             (Tactic.simpLemma [] [] `mul_comm)
             ","
             (Tactic.simpLemma [] [] `mul_left_comm)]
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
        [(Tactic.simpLemma [] [] `det_apply')
         ","
         (Tactic.simpLemma [] [] `Finset.mul_sum)
         ","
         (Tactic.simpLemma [] [] `mul_comm)
         ","
         (Tactic.simpLemma [] [] `mul_left_comm)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_left_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Finset.mul_sum
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `det_apply'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.hole "_") "=" («term_*_» (Term.app `det [`M]) "*" (Term.app `det [`N])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (Term.app `det [`M]) "*" (Term.app `det [`N]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `det [`N])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `N
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `det
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `det [`M])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `M
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `det
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.app
       `sum_congr
       [`rfl
        (Term.fun
         "fun"
         (Term.basicFun
          [`σ (Term.hole "_")]
          []
          "=>"
          (Term.app
           `Fintype.sum_equiv
           [(Term.app `Equiv.mulRight [(«term_⁻¹» `σ "⁻¹")])
            (Term.hole "_")
            (Term.hole "_")
            (Term.fun
             "fun"
             (Term.basicFun
              [`τ]
              []
              "=>"
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
                        (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                         "∏"
                         (Std.ExtendedBinder.extBinders
                          (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
                         ", "
                         (Term.app `M [(Term.app `τ [`j]) (Term.app `σ [`j])]))
                        "="
                        (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                         "∏"
                         (Std.ExtendedBinder.extBinders
                          (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
                         ", "
                         (Term.app
                          `M
                          [(Term.app («term_*_» `τ "*" («term_⁻¹» `σ "⁻¹")) [`j]) `j]))))]
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
                             (Term.proj
                              (Term.typeAscription
                               "("
                               («term_⁻¹» `σ "⁻¹")
                               ":"
                               [(Logic.Equiv.Defs.«term_≃_» (Term.hole "_") " ≃ " (Term.hole "_"))]
                               ")")
                              "."
                              `prod_comp))]
                           "]")
                          [])
                         []
                         (Tactic.simp
                          "simp"
                          []
                          []
                          ["only"]
                          ["["
                           [(Tactic.simpLemma [] [] `Equiv.Perm.coe_mul)
                            ","
                            (Tactic.simpLemma [] [] `apply_inv_self)]
                           "]"]
                          [])]))))))
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`h []]
                     [(Term.typeSpec
                       ":"
                       («term_=_»
                        («term_*_»
                         (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `σ)
                         "*"
                         (Matrix.LinearAlgebra.Matrix.Determinant.termε_
                          "ε "
                          («term_*_» `τ "*" («term_⁻¹» `σ "⁻¹"))))
                        "="
                        (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `τ)))]
                     ":="
                     (calc
                      "calc"
                      (calcStep
                       («term_=_»
                        («term_*_»
                         (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `σ)
                         "*"
                         (Matrix.LinearAlgebra.Matrix.Determinant.termε_
                          "ε "
                          («term_*_» `τ "*" («term_⁻¹» `σ "⁻¹"))))
                        "="
                        (Matrix.LinearAlgebra.Matrix.Determinant.termε_
                         "ε "
                         («term_*_» («term_*_» `τ "*" («term_⁻¹» `σ "⁻¹")) "*" `σ)))
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
                             [(Tactic.rwRule [] `mul_comm)
                              ","
                              (Tactic.rwRule
                               []
                               (Term.app `sign_mul [(«term_*_» `τ "*" («term_⁻¹» `σ "⁻¹"))]))]
                             "]")
                            [])
                           []
                           (Tactic.simp
                            "simp"
                            []
                            []
                            ["only"]
                            ["["
                             [(Tactic.simpLemma [] [] `Int.cast_mul)
                              ","
                              (Tactic.simpLemma [] [] `Units.val_mul)]
                             "]"]
                            [])]))))
                      [(calcStep
                        («term_=_»
                         (Term.hole "_")
                         "="
                         (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `τ))
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
                             ["[" [(Tactic.simpLemma [] [] `inv_mul_cancel_right)] "]"]
                             [])]))))]))))
                  []
                  (Mathlib.Tactic.tacticSimp_rw__
                   "simp_rw"
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `Equiv.coe_mulRight) "," (Tactic.rwRule [] `h)]
                    "]")
                   [])
                  []
                  (Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["[" [(Tactic.simpLemma [] [] `this)] "]"]
                   [])])))))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`σ (Term.hole "_")]
        []
        "=>"
        (Term.app
         `Fintype.sum_equiv
         [(Term.app `Equiv.mulRight [(«term_⁻¹» `σ "⁻¹")])
          (Term.hole "_")
          (Term.hole "_")
          (Term.fun
           "fun"
           (Term.basicFun
            [`τ]
            []
            "=>"
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
                      (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                       "∏"
                       (Std.ExtendedBinder.extBinders
                        (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
                       ", "
                       (Term.app `M [(Term.app `τ [`j]) (Term.app `σ [`j])]))
                      "="
                      (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                       "∏"
                       (Std.ExtendedBinder.extBinders
                        (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
                       ", "
                       (Term.app `M [(Term.app («term_*_» `τ "*" («term_⁻¹» `σ "⁻¹")) [`j]) `j]))))]
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
                           (Term.proj
                            (Term.typeAscription
                             "("
                             («term_⁻¹» `σ "⁻¹")
                             ":"
                             [(Logic.Equiv.Defs.«term_≃_» (Term.hole "_") " ≃ " (Term.hole "_"))]
                             ")")
                            "."
                            `prod_comp))]
                         "]")
                        [])
                       []
                       (Tactic.simp
                        "simp"
                        []
                        []
                        ["only"]
                        ["["
                         [(Tactic.simpLemma [] [] `Equiv.Perm.coe_mul)
                          ","
                          (Tactic.simpLemma [] [] `apply_inv_self)]
                         "]"]
                        [])]))))))
                []
                (Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   [`h []]
                   [(Term.typeSpec
                     ":"
                     («term_=_»
                      («term_*_»
                       (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `σ)
                       "*"
                       (Matrix.LinearAlgebra.Matrix.Determinant.termε_
                        "ε "
                        («term_*_» `τ "*" («term_⁻¹» `σ "⁻¹"))))
                      "="
                      (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `τ)))]
                   ":="
                   (calc
                    "calc"
                    (calcStep
                     («term_=_»
                      («term_*_»
                       (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `σ)
                       "*"
                       (Matrix.LinearAlgebra.Matrix.Determinant.termε_
                        "ε "
                        («term_*_» `τ "*" («term_⁻¹» `σ "⁻¹"))))
                      "="
                      (Matrix.LinearAlgebra.Matrix.Determinant.termε_
                       "ε "
                       («term_*_» («term_*_» `τ "*" («term_⁻¹» `σ "⁻¹")) "*" `σ)))
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
                           [(Tactic.rwRule [] `mul_comm)
                            ","
                            (Tactic.rwRule
                             []
                             (Term.app `sign_mul [(«term_*_» `τ "*" («term_⁻¹» `σ "⁻¹"))]))]
                           "]")
                          [])
                         []
                         (Tactic.simp
                          "simp"
                          []
                          []
                          ["only"]
                          ["["
                           [(Tactic.simpLemma [] [] `Int.cast_mul)
                            ","
                            (Tactic.simpLemma [] [] `Units.val_mul)]
                           "]"]
                          [])]))))
                    [(calcStep
                      («term_=_»
                       (Term.hole "_")
                       "="
                       (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `τ))
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
                           ["[" [(Tactic.simpLemma [] [] `inv_mul_cancel_right)] "]"]
                           [])]))))]))))
                []
                (Mathlib.Tactic.tacticSimp_rw__
                 "simp_rw"
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `Equiv.coe_mulRight) "," (Tactic.rwRule [] `h)]
                  "]")
                 [])
                []
                (Tactic.simp
                 "simp"
                 []
                 []
                 ["only"]
                 ["[" [(Tactic.simpLemma [] [] `this)] "]"]
                 [])])))))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Fintype.sum_equiv
       [(Term.app `Equiv.mulRight [(«term_⁻¹» `σ "⁻¹")])
        (Term.hole "_")
        (Term.hole "_")
        (Term.fun
         "fun"
         (Term.basicFun
          [`τ]
          []
          "=>"
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
                    (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                     "∏"
                     (Std.ExtendedBinder.extBinders
                      (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
                     ", "
                     (Term.app `M [(Term.app `τ [`j]) (Term.app `σ [`j])]))
                    "="
                    (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                     "∏"
                     (Std.ExtendedBinder.extBinders
                      (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
                     ", "
                     (Term.app `M [(Term.app («term_*_» `τ "*" («term_⁻¹» `σ "⁻¹")) [`j]) `j]))))]
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
                         (Term.proj
                          (Term.typeAscription
                           "("
                           («term_⁻¹» `σ "⁻¹")
                           ":"
                           [(Logic.Equiv.Defs.«term_≃_» (Term.hole "_") " ≃ " (Term.hole "_"))]
                           ")")
                          "."
                          `prod_comp))]
                       "]")
                      [])
                     []
                     (Tactic.simp
                      "simp"
                      []
                      []
                      ["only"]
                      ["["
                       [(Tactic.simpLemma [] [] `Equiv.Perm.coe_mul)
                        ","
                        (Tactic.simpLemma [] [] `apply_inv_self)]
                       "]"]
                      [])]))))))
              []
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`h []]
                 [(Term.typeSpec
                   ":"
                   («term_=_»
                    («term_*_»
                     (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `σ)
                     "*"
                     (Matrix.LinearAlgebra.Matrix.Determinant.termε_
                      "ε "
                      («term_*_» `τ "*" («term_⁻¹» `σ "⁻¹"))))
                    "="
                    (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `τ)))]
                 ":="
                 (calc
                  "calc"
                  (calcStep
                   («term_=_»
                    («term_*_»
                     (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `σ)
                     "*"
                     (Matrix.LinearAlgebra.Matrix.Determinant.termε_
                      "ε "
                      («term_*_» `τ "*" («term_⁻¹» `σ "⁻¹"))))
                    "="
                    (Matrix.LinearAlgebra.Matrix.Determinant.termε_
                     "ε "
                     («term_*_» («term_*_» `τ "*" («term_⁻¹» `σ "⁻¹")) "*" `σ)))
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
                         [(Tactic.rwRule [] `mul_comm)
                          ","
                          (Tactic.rwRule
                           []
                           (Term.app `sign_mul [(«term_*_» `τ "*" («term_⁻¹» `σ "⁻¹"))]))]
                         "]")
                        [])
                       []
                       (Tactic.simp
                        "simp"
                        []
                        []
                        ["only"]
                        ["["
                         [(Tactic.simpLemma [] [] `Int.cast_mul)
                          ","
                          (Tactic.simpLemma [] [] `Units.val_mul)]
                         "]"]
                        [])]))))
                  [(calcStep
                    («term_=_»
                     (Term.hole "_")
                     "="
                     (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `τ))
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
                         ["[" [(Tactic.simpLemma [] [] `inv_mul_cancel_right)] "]"]
                         [])]))))]))))
              []
              (Mathlib.Tactic.tacticSimp_rw__
               "simp_rw"
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `Equiv.coe_mulRight) "," (Tactic.rwRule [] `h)]
                "]")
               [])
              []
              (Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["[" [(Tactic.simpLemma [] [] `this)] "]"]
               [])])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`τ]
        []
        "=>"
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
                  (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                   "∏"
                   (Std.ExtendedBinder.extBinders
                    (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
                   ", "
                   (Term.app `M [(Term.app `τ [`j]) (Term.app `σ [`j])]))
                  "="
                  (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                   "∏"
                   (Std.ExtendedBinder.extBinders
                    (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
                   ", "
                   (Term.app `M [(Term.app («term_*_» `τ "*" («term_⁻¹» `σ "⁻¹")) [`j]) `j]))))]
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
                       (Term.proj
                        (Term.typeAscription
                         "("
                         («term_⁻¹» `σ "⁻¹")
                         ":"
                         [(Logic.Equiv.Defs.«term_≃_» (Term.hole "_") " ≃ " (Term.hole "_"))]
                         ")")
                        "."
                        `prod_comp))]
                     "]")
                    [])
                   []
                   (Tactic.simp
                    "simp"
                    []
                    []
                    ["only"]
                    ["["
                     [(Tactic.simpLemma [] [] `Equiv.Perm.coe_mul)
                      ","
                      (Tactic.simpLemma [] [] `apply_inv_self)]
                     "]"]
                    [])]))))))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`h []]
               [(Term.typeSpec
                 ":"
                 («term_=_»
                  («term_*_»
                   (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `σ)
                   "*"
                   (Matrix.LinearAlgebra.Matrix.Determinant.termε_
                    "ε "
                    («term_*_» `τ "*" («term_⁻¹» `σ "⁻¹"))))
                  "="
                  (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `τ)))]
               ":="
               (calc
                "calc"
                (calcStep
                 («term_=_»
                  («term_*_»
                   (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `σ)
                   "*"
                   (Matrix.LinearAlgebra.Matrix.Determinant.termε_
                    "ε "
                    («term_*_» `τ "*" («term_⁻¹» `σ "⁻¹"))))
                  "="
                  (Matrix.LinearAlgebra.Matrix.Determinant.termε_
                   "ε "
                   («term_*_» («term_*_» `τ "*" («term_⁻¹» `σ "⁻¹")) "*" `σ)))
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
                       [(Tactic.rwRule [] `mul_comm)
                        ","
                        (Tactic.rwRule
                         []
                         (Term.app `sign_mul [(«term_*_» `τ "*" («term_⁻¹» `σ "⁻¹"))]))]
                       "]")
                      [])
                     []
                     (Tactic.simp
                      "simp"
                      []
                      []
                      ["only"]
                      ["["
                       [(Tactic.simpLemma [] [] `Int.cast_mul)
                        ","
                        (Tactic.simpLemma [] [] `Units.val_mul)]
                       "]"]
                      [])]))))
                [(calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `τ))
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
                       ["[" [(Tactic.simpLemma [] [] `inv_mul_cancel_right)] "]"]
                       [])]))))]))))
            []
            (Mathlib.Tactic.tacticSimp_rw__
             "simp_rw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `Equiv.coe_mulRight) "," (Tactic.rwRule [] `h)]
              "]")
             [])
            []
            (Tactic.simp "simp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `this)] "]"] [])])))))
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
                (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                 "∏"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
                 ", "
                 (Term.app `M [(Term.app `τ [`j]) (Term.app `σ [`j])]))
                "="
                (BigOperators.Algebra.BigOperators.Basic.finset.prod_univ
                 "∏"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) []))
                 ", "
                 (Term.app `M [(Term.app («term_*_» `τ "*" («term_⁻¹» `σ "⁻¹")) [`j]) `j]))))]
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
                     (Term.proj
                      (Term.typeAscription
                       "("
                       («term_⁻¹» `σ "⁻¹")
                       ":"
                       [(Logic.Equiv.Defs.«term_≃_» (Term.hole "_") " ≃ " (Term.hole "_"))]
                       ")")
                      "."
                      `prod_comp))]
                   "]")
                  [])
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `Equiv.Perm.coe_mul)
                    ","
                    (Tactic.simpLemma [] [] `apply_inv_self)]
                   "]"]
                  [])]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h []]
             [(Term.typeSpec
               ":"
               («term_=_»
                («term_*_»
                 (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `σ)
                 "*"
                 (Matrix.LinearAlgebra.Matrix.Determinant.termε_
                  "ε "
                  («term_*_» `τ "*" («term_⁻¹» `σ "⁻¹"))))
                "="
                (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `τ)))]
             ":="
             (calc
              "calc"
              (calcStep
               («term_=_»
                («term_*_»
                 (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `σ)
                 "*"
                 (Matrix.LinearAlgebra.Matrix.Determinant.termε_
                  "ε "
                  («term_*_» `τ "*" («term_⁻¹» `σ "⁻¹"))))
                "="
                (Matrix.LinearAlgebra.Matrix.Determinant.termε_
                 "ε "
                 («term_*_» («term_*_» `τ "*" («term_⁻¹» `σ "⁻¹")) "*" `σ)))
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
                     [(Tactic.rwRule [] `mul_comm)
                      ","
                      (Tactic.rwRule
                       []
                       (Term.app `sign_mul [(«term_*_» `τ "*" («term_⁻¹» `σ "⁻¹"))]))]
                     "]")
                    [])
                   []
                   (Tactic.simp
                    "simp"
                    []
                    []
                    ["only"]
                    ["["
                     [(Tactic.simpLemma [] [] `Int.cast_mul)
                      ","
                      (Tactic.simpLemma [] [] `Units.val_mul)]
                     "]"]
                    [])]))))
              [(calcStep
                («term_=_»
                 (Term.hole "_")
                 "="
                 (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `τ))
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
                     ["[" [(Tactic.simpLemma [] [] `inv_mul_cancel_right)] "]"]
                     [])]))))]))))
          []
          (Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `Equiv.coe_mulRight) "," (Tactic.rwRule [] `h)]
            "]")
           [])
          []
          (Tactic.simp "simp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `this)] "]"] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `this)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Equiv.coe_mulRight) "," (Tactic.rwRule [] `h)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Equiv.coe_mulRight
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
            («term_*_»
             (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `σ)
             "*"
             (Matrix.LinearAlgebra.Matrix.Determinant.termε_
              "ε "
              («term_*_» `τ "*" («term_⁻¹» `σ "⁻¹"))))
            "="
            (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `τ)))]
         ":="
         (calc
          "calc"
          (calcStep
           («term_=_»
            («term_*_»
             (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `σ)
             "*"
             (Matrix.LinearAlgebra.Matrix.Determinant.termε_
              "ε "
              («term_*_» `τ "*" («term_⁻¹» `σ "⁻¹"))))
            "="
            (Matrix.LinearAlgebra.Matrix.Determinant.termε_
             "ε "
             («term_*_» («term_*_» `τ "*" («term_⁻¹» `σ "⁻¹")) "*" `σ)))
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
                 [(Tactic.rwRule [] `mul_comm)
                  ","
                  (Tactic.rwRule [] (Term.app `sign_mul [(«term_*_» `τ "*" («term_⁻¹» `σ "⁻¹"))]))]
                 "]")
                [])
               []
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `Int.cast_mul)
                  ","
                  (Tactic.simpLemma [] [] `Units.val_mul)]
                 "]"]
                [])]))))
          [(calcStep
            («term_=_» (Term.hole "_") "=" (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `τ))
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
                 ["[" [(Tactic.simpLemma [] [] `inv_mul_cancel_right)] "]"]
                 [])]))))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calc
       "calc"
       (calcStep
        («term_=_»
         («term_*_»
          (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `σ)
          "*"
          (Matrix.LinearAlgebra.Matrix.Determinant.termε_
           "ε "
           («term_*_» `τ "*" («term_⁻¹» `σ "⁻¹"))))
         "="
         (Matrix.LinearAlgebra.Matrix.Determinant.termε_
          "ε "
          («term_*_» («term_*_» `τ "*" («term_⁻¹» `σ "⁻¹")) "*" `σ)))
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
              [(Tactic.rwRule [] `mul_comm)
               ","
               (Tactic.rwRule [] (Term.app `sign_mul [(«term_*_» `τ "*" («term_⁻¹» `σ "⁻¹"))]))]
              "]")
             [])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `Int.cast_mul) "," (Tactic.simpLemma [] [] `Units.val_mul)]
              "]"]
             [])]))))
       [(calcStep
         («term_=_» (Term.hole "_") "=" (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `τ))
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
              ["[" [(Tactic.simpLemma [] [] `inv_mul_cancel_right)] "]"]
              [])]))))])
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
           ["[" [(Tactic.simpLemma [] [] `inv_mul_cancel_right)] "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["[" [(Tactic.simpLemma [] [] `inv_mul_cancel_right)] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inv_mul_cancel_right
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.hole "_") "=" (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `τ))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Matrix.LinearAlgebra.Matrix.Determinant.termε_ "ε " `τ)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Matrix.LinearAlgebra.Matrix.Determinant.termε_', expected 'Matrix.LinearAlgebra.Matrix.Determinant.termε_._@.LinearAlgebra.Matrix.Determinant._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
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
    det_mul
    ( M N : Matrix n n R ) : det M ⬝ N = det M * det N
    :=
      calc
        det M ⬝ N = ∑ p : n → n , ∑ σ : Perm n , ε σ * ∏ i , M σ i p i * N p i i
          :=
          by
            simp only [ det_apply' , mul_apply , prod_univ_sum , mul_sum , Fintype.pi_finset_univ ]
              <;>
              rw [ Finset.sum_comm ]
        _
              =
              ∑
                p
                in
                @ univ n → n _ . filter Bijective
                ,
                ∑ σ : Perm n , ε σ * ∏ i , M σ i p i * N p i i
            :=
            Eq.symm
              <|
              sum_subset
                filter_subset _ _
                  fun
                    f _ hbij
                      =>
                      det_mul_aux
                        <|
                        by simpa only [ true_and_iff , mem_filter , mem_univ ] using hbij
          _ = ∑ τ : Perm n , ∑ σ : Perm n , ε σ * ∏ i , M σ i τ i * N τ i i
            :=
            sum_bij
              fun p h => Equiv.ofBijective p mem_filter . 1 h . 2
                fun _ _ => mem_univ _
                fun _ _ => rfl
                fun _ _ _ _ h => by injection h
                fun
                  b _
                    =>
                    ⟨ b , mem_filter . 2 ⟨ mem_univ _ , b . Bijective ⟩ , coe_fn_injective rfl ⟩
          _ = ∑ σ : Perm n , ∑ τ : Perm n , ∏ i , N σ i i * ε τ * ∏ j , M τ j σ j
            :=
            by simp only [ mul_comm , mul_left_comm , prod_mul_distrib , mul_assoc ]
          _ = ∑ σ : Perm n , ∑ τ : Perm n , ∏ i , N σ i i * ε σ * ε τ * ∏ i , M τ i i
            :=
            sum_congr
              rfl
                fun
                  σ _
                    =>
                    Fintype.sum_equiv
                      Equiv.mulRight σ ⁻¹
                        _
                        _
                        fun
                          τ
                            =>
                            by
                              have
                                  : ∏ j , M τ j σ j = ∏ j , M τ * σ ⁻¹ j j
                                    :=
                                    by
                                      rw [ ← ( σ ⁻¹ : _ ≃ _ ) . prod_comp ]
                                        simp only [ Equiv.Perm.coe_mul , apply_inv_self ]
                                have
                                  h
                                    : ε σ * ε τ * σ ⁻¹ = ε τ
                                    :=
                                    calc
                                      ε σ * ε τ * σ ⁻¹ = ε τ * σ ⁻¹ * σ
                                        :=
                                        by
                                          rw [ mul_comm , sign_mul τ * σ ⁻¹ ]
                                            simp only [ Int.cast_mul , Units.val_mul ]
                                      _ = ε τ := by simp only [ inv_mul_cancel_right ]
                                simp_rw [ Equiv.coe_mulRight , h ]
                                simp only [ this ]
          _ = det M * det N
            :=
            by simp only [ det_apply' , Finset.mul_sum , mul_comm , mul_left_comm ]
#align matrix.det_mul Matrix.det_mul

/-- The determinant of a matrix, as a monoid homomorphism. -/
def detMonoidHom : Matrix n n R →* R where
  toFun := det
  map_one' := det_one
  map_mul' := det_mul
#align matrix.det_monoid_hom Matrix.detMonoidHom

@[simp]
theorem coe_det_monoid_hom : (detMonoidHom : Matrix n n R → R) = det :=
  rfl
#align matrix.coe_det_monoid_hom Matrix.coe_det_monoid_hom

/-- On square matrices, `mul_comm` applies under `det`. -/
theorem det_mul_comm (M N : Matrix m m R) : det (M ⬝ N) = det (N ⬝ M) := by
  rw [det_mul, det_mul, mul_comm]
#align matrix.det_mul_comm Matrix.det_mul_comm

/-- On square matrices, `mul_left_comm` applies under `det`. -/
theorem det_mul_left_comm (M N P : Matrix m m R) : det (M ⬝ (N ⬝ P)) = det (N ⬝ (M ⬝ P)) := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, det_mul, det_mul_comm M N, ← det_mul]
#align matrix.det_mul_left_comm Matrix.det_mul_left_comm

/-- On square matrices, `mul_right_comm` applies under `det`. -/
theorem det_mul_right_comm (M N P : Matrix m m R) : det (M ⬝ N ⬝ P) = det (M ⬝ P ⬝ N) := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc, det_mul, det_mul_comm N P, ← det_mul]
#align matrix.det_mul_right_comm Matrix.det_mul_right_comm

theorem det_units_conj (M : (Matrix m m R)ˣ) (N : Matrix m m R) :
    det (↑M ⬝ N ⬝ ↑M⁻¹ : Matrix m m R) = det N := by
  rw [det_mul_right_comm, ← mul_eq_mul, ← mul_eq_mul, Units.mul_inv, one_mul]
#align matrix.det_units_conj Matrix.det_units_conj

theorem det_units_conj' (M : (Matrix m m R)ˣ) (N : Matrix m m R) :
    det (↑M⁻¹ ⬝ N ⬝ ↑M : Matrix m m R) = det N :=
  det_units_conj M⁻¹ N
#align matrix.det_units_conj' Matrix.det_units_conj'

/-- Transposing a matrix preserves the determinant. -/
@[simp]
theorem det_transpose (M : Matrix n n R) : Mᵀ.det = M.det :=
  by
  rw [det_apply', det_apply']
  refine' Fintype.sum_bijective _ inv_involutive.bijective _ _ _
  intro σ
  rw [sign_inv]
  congr 1
  apply Fintype.prod_equiv σ
  intros
  simp
#align matrix.det_transpose Matrix.det_transpose

/-- Permuting the columns changes the sign of the determinant. -/
theorem det_permute (σ : Perm n) (M : Matrix n n R) :
    (Matrix.det fun i => M (σ i)) = σ.sign * M.det :=
  ((detRowAlternating : AlternatingMap R (n → R) R n).map_perm M σ).trans (by simp [Units.smul_def])
#align matrix.det_permute Matrix.det_permute

/-- Permuting rows and columns with the same equivalence has no effect. -/
@[simp]
theorem det_submatrix_equiv_self (e : n ≃ m) (A : Matrix m m R) : det (A.submatrix e e) = det A :=
  by
  rw [det_apply', det_apply']
  apply Fintype.sum_equiv (Equiv.permCongr e)
  intro σ
  rw [Equiv.Perm.sign_perm_congr e σ]
  congr 1
  apply Fintype.prod_equiv e
  intro i
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply, submatrix_apply]
#align matrix.det_submatrix_equiv_self Matrix.det_submatrix_equiv_self

/-- Reindexing both indices along the same equivalence preserves the determinant.

For the `simp` version of this lemma, see `det_submatrix_equiv_self`; this one is unsuitable because
`matrix.reindex_apply` unfolds `reindex` first.
-/
theorem det_reindex_self (e : m ≃ n) (A : Matrix m m R) : det (reindex e e A) = det A :=
  det_submatrix_equiv_self e.symm A
#align matrix.det_reindex_self Matrix.det_reindex_self

/-- The determinant of a permutation matrix equals its sign. -/
@[simp]
theorem det_permutation (σ : Perm n) : Matrix.det (σ.toPequiv.toMatrix : Matrix n n R) = σ.sign :=
  by
  rw [← Matrix.mul_one (σ.to_pequiv.to_matrix : Matrix n n R), PEquiv.to_pequiv_mul_matrix,
    det_permute, det_one, mul_one]
#align matrix.det_permutation Matrix.det_permutation

theorem det_smul (A : Matrix n n R) (c : R) : det (c • A) = c ^ Fintype.card n * det A :=
  calc
    det (c • A) = det (Matrix.mul (diagonal fun _ => c) A) := by rw [smul_eq_diagonal_mul]
    _ = det (diagonal fun _ => c) * det A := det_mul _ _
    _ = c ^ Fintype.card n * det A := by simp [card_univ]
    
#align matrix.det_smul Matrix.det_smul

@[simp]
theorem det_smul_of_tower {α} [Monoid α] [DistribMulAction α R] [IsScalarTower α R R]
    [SMulCommClass α R R] (c : α) (A : Matrix n n R) : det (c • A) = c ^ Fintype.card n • det A :=
  by rw [← smul_one_smul R c A, det_smul, smul_pow, one_pow, smul_mul_assoc, one_mul]
#align matrix.det_smul_of_tower Matrix.det_smul_of_tower

theorem det_neg (A : Matrix n n R) : det (-A) = (-1) ^ Fintype.card n * det A := by
  rw [← det_smul, neg_one_smul]
#align matrix.det_neg Matrix.det_neg

/-- A variant of `matrix.det_neg` with scalar multiplication by `units ℤ` instead of multiplication
by `R`. -/
theorem det_neg_eq_smul (A : Matrix n n R) : det (-A) = (-1 : Units ℤ) ^ Fintype.card n • det A :=
  by rw [← det_smul_of_tower, Units.neg_smul, one_smul]
#align matrix.det_neg_eq_smul Matrix.det_neg_eq_smul

/-- Multiplying each row by a fixed `v i` multiplies the determinant by
the product of the `v`s. -/
theorem det_mul_row (v : n → R) (A : Matrix n n R) :
    det (of fun i j => v j * A i j) = (∏ i, v i) * det A :=
  calc
    det (of fun i j => v j * A i j) = det (A ⬝ diagonal v) :=
      congr_arg det <| by
        ext
        simp [mul_comm]
    _ = (∏ i, v i) * det A := by rw [det_mul, det_diagonal, mul_comm]
    
#align matrix.det_mul_row Matrix.det_mul_row

/-- Multiplying each column by a fixed `v j` multiplies the determinant by
the product of the `v`s. -/
theorem det_mul_column (v : n → R) (A : Matrix n n R) :
    det (of fun i j => v i * A i j) = (∏ i, v i) * det A :=
  MultilinearMap.map_smul_univ _ v A
#align matrix.det_mul_column Matrix.det_mul_column

@[simp]
theorem det_pow (M : Matrix m m R) (n : ℕ) : det (M ^ n) = det M ^ n :=
  (detMonoidHom : Matrix m m R →* R).map_pow M n
#align matrix.det_pow Matrix.det_pow

section HomMap

variable {S : Type w} [CommRing S]

theorem RingHom.map_det (f : R →+* S) (M : Matrix n n R) : f M.det = Matrix.det (f.mapMatrix M) :=
  by simp [Matrix.det_apply', f.map_sum, f.map_prod]
#align ring_hom.map_det RingHom.map_det

theorem RingEquiv.map_det (f : R ≃+* S) (M : Matrix n n R) : f M.det = Matrix.det (f.mapMatrix M) :=
  f.toRingHom.map_det _
#align ring_equiv.map_det RingEquiv.map_det

theorem AlgHom.map_det [Algebra R S] {T : Type z} [CommRing T] [Algebra R T] (f : S →ₐ[R] T)
    (M : Matrix n n S) : f M.det = Matrix.det (f.mapMatrix M) :=
  f.toRingHom.map_det _
#align alg_hom.map_det AlgHom.map_det

theorem AlgEquiv.map_det [Algebra R S] {T : Type z} [CommRing T] [Algebra R T] (f : S ≃ₐ[R] T)
    (M : Matrix n n S) : f M.det = Matrix.det (f.mapMatrix M) :=
  f.toAlgHom.map_det _
#align alg_equiv.map_det AlgEquiv.map_det

end HomMap

@[simp]
theorem det_conj_transpose [StarRing R] (M : Matrix m m R) : det Mᴴ = star (det M) :=
  ((starRingEnd R).map_det _).symm.trans <| congr_arg star M.det_transpose
#align matrix.det_conj_transpose Matrix.det_conj_transpose

section DetZero

/-!
### `det_zero` section

Prove that a matrix with a repeated column has determinant equal to zero.
-/


theorem det_eq_zero_of_row_eq_zero {A : Matrix n n R} (i : n) (h : ∀ j, A i j = 0) : det A = 0 :=
  (detRowAlternating : AlternatingMap R (n → R) R n).map_coord_zero i (funext h)
#align matrix.det_eq_zero_of_row_eq_zero Matrix.det_eq_zero_of_row_eq_zero

theorem det_eq_zero_of_column_eq_zero {A : Matrix n n R} (j : n) (h : ∀ i, A i j = 0) : det A = 0 :=
  by
  rw [← det_transpose]
  exact det_eq_zero_of_row_eq_zero j h
#align matrix.det_eq_zero_of_column_eq_zero Matrix.det_eq_zero_of_column_eq_zero

variable {M : Matrix n n R} {i j : n}

/-- If a matrix has a repeated row, the determinant will be zero. -/
theorem det_zero_of_row_eq (i_ne_j : i ≠ j) (hij : M i = M j) : M.det = 0 :=
  (detRowAlternating : AlternatingMap R (n → R) R n).map_eq_zero_of_eq M hij i_ne_j
#align matrix.det_zero_of_row_eq Matrix.det_zero_of_row_eq

/-- If a matrix has a repeated column, the determinant will be zero. -/
theorem det_zero_of_column_eq (i_ne_j : i ≠ j) (hij : ∀ k, M k i = M k j) : M.det = 0 :=
  by
  rw [← det_transpose, det_zero_of_row_eq i_ne_j]
  exact funext hij
#align matrix.det_zero_of_column_eq Matrix.det_zero_of_column_eq

end DetZero

theorem det_update_row_add (M : Matrix n n R) (j : n) (u v : n → R) :
    det (updateRow M j <| u + v) = det (updateRow M j u) + det (updateRow M j v) :=
  (detRowAlternating : AlternatingMap R (n → R) R n).map_add M j u v
#align matrix.det_update_row_add Matrix.det_update_row_add

theorem det_update_column_add (M : Matrix n n R) (j : n) (u v : n → R) :
    det (updateColumn M j <| u + v) = det (updateColumn M j u) + det (updateColumn M j v) :=
  by
  rw [← det_transpose, ← update_row_transpose, det_update_row_add]
  simp [update_row_transpose, det_transpose]
#align matrix.det_update_column_add Matrix.det_update_column_add

theorem det_update_row_smul (M : Matrix n n R) (j : n) (s : R) (u : n → R) :
    det (updateRow M j <| s • u) = s * det (updateRow M j u) :=
  (detRowAlternating : AlternatingMap R (n → R) R n).map_smul M j s u
#align matrix.det_update_row_smul Matrix.det_update_row_smul

theorem det_update_column_smul (M : Matrix n n R) (j : n) (s : R) (u : n → R) :
    det (updateColumn M j <| s • u) = s * det (updateColumn M j u) :=
  by
  rw [← det_transpose, ← update_row_transpose, det_update_row_smul]
  simp [update_row_transpose, det_transpose]
#align matrix.det_update_column_smul Matrix.det_update_column_smul

theorem det_update_row_smul' (M : Matrix n n R) (j : n) (s : R) (u : n → R) :
    det (updateRow (s • M) j u) = s ^ (Fintype.card n - 1) * det (updateRow M j u) :=
  MultilinearMap.map_update_smul _ M j s u
#align matrix.det_update_row_smul' Matrix.det_update_row_smul'

theorem det_update_column_smul' (M : Matrix n n R) (j : n) (s : R) (u : n → R) :
    det (updateColumn (s • M) j u) = s ^ (Fintype.card n - 1) * det (updateColumn M j u) :=
  by
  rw [← det_transpose, ← update_row_transpose, transpose_smul, det_update_row_smul']
  simp [update_row_transpose, det_transpose]
#align matrix.det_update_column_smul' Matrix.det_update_column_smul'

section DetEq

/-! ### `det_eq` section

Lemmas showing the determinant is invariant under a variety of operations.
-/


theorem det_eq_of_eq_mul_det_one {A B : Matrix n n R} (C : Matrix n n R) (hC : det C = 1)
    (hA : A = B ⬝ C) : det A = det B :=
  calc
    det A = det (B ⬝ C) := congr_arg _ hA
    _ = det B * det C := det_mul _ _
    _ = det B := by rw [hC, mul_one]
    
#align matrix.det_eq_of_eq_mul_det_one Matrix.det_eq_of_eq_mul_det_one

theorem det_eq_of_eq_det_one_mul {A B : Matrix n n R} (C : Matrix n n R) (hC : det C = 1)
    (hA : A = C ⬝ B) : det A = det B :=
  calc
    det A = det (C ⬝ B) := congr_arg _ hA
    _ = det C * det B := det_mul _ _
    _ = det B := by rw [hC, one_mul]
    
#align matrix.det_eq_of_eq_det_one_mul Matrix.det_eq_of_eq_det_one_mul

theorem det_update_row_add_self (A : Matrix n n R) {i j : n} (hij : i ≠ j) :
    det (updateRow A i (A i + A j)) = det A := by
  simp [det_update_row_add,
    det_zero_of_row_eq hij (update_row_self.trans (update_row_ne hij.symm).symm)]
#align matrix.det_update_row_add_self Matrix.det_update_row_add_self

theorem det_update_column_add_self (A : Matrix n n R) {i j : n} (hij : i ≠ j) :
    det (updateColumn A i fun k => A k i + A k j) = det A :=
  by
  rw [← det_transpose, ← update_row_transpose, ← det_transpose A]
  exact det_update_row_add_self Aᵀ hij
#align matrix.det_update_column_add_self Matrix.det_update_column_add_self

theorem det_update_row_add_smul_self (A : Matrix n n R) {i j : n} (hij : i ≠ j) (c : R) :
    det (updateRow A i (A i + c • A j)) = det A := by
  simp [det_update_row_add, det_update_row_smul,
    det_zero_of_row_eq hij (update_row_self.trans (update_row_ne hij.symm).symm)]
#align matrix.det_update_row_add_smul_self Matrix.det_update_row_add_smul_self

theorem det_update_column_add_smul_self (A : Matrix n n R) {i j : n} (hij : i ≠ j) (c : R) :
    det (updateColumn A i fun k => A k i + c • A k j) = det A :=
  by
  rw [← det_transpose, ← update_row_transpose, ← det_transpose A]
  exact det_update_row_add_smul_self Aᵀ hij c
#align matrix.det_update_column_add_smul_self Matrix.det_update_column_add_smul_self

theorem det_eq_of_forall_row_eq_smul_add_const_aux {A B : Matrix n n R} {s : Finset n} :
    ∀ (c : n → R) (hs : ∀ i, i ∉ s → c i = 0) (k : n) (hk : k ∉ s)
      (A_eq : ∀ i j, A i j = B i j + c i * B k j), det A = det B :=
  by
  revert B
  refine' s.induction_on _ _
  · intro A c hs k hk A_eq
    have : ∀ i, c i = 0 := by
      intro i
      specialize hs i
      contrapose! hs
      simp [hs]
    congr
    ext (i j)
    rw [A_eq, this, zero_mul, add_zero]
  · intro i s hi ih B c hs k hk A_eq
    have hAi : A i = B i + c i • B k := funext (A_eq i)
    rw [@ih (update_row B i (A i)) (Function.update c i 0), hAi, det_update_row_add_smul_self]
    · exact mt (fun h => show k ∈ insert i s from h ▸ Finset.mem_insert_self _ _) hk
    · intro i' hi'
      rw [Function.update_apply]
      split_ifs with hi'i
      · rfl
      · exact hs i' fun h => hi' ((finset.mem_insert.mp h).resolve_left hi'i)
    · exact fun h => hk (Finset.mem_insert_of_mem h)
    · intro i' j'
      rw [update_row_apply, Function.update_apply]
      split_ifs with hi'i
      · simp [hi'i]
      rw [A_eq, update_row_ne fun h : k = i => hk <| h ▸ Finset.mem_insert_self k s]
#align
  matrix.det_eq_of_forall_row_eq_smul_add_const_aux Matrix.det_eq_of_forall_row_eq_smul_add_const_aux

/-- If you add multiples of row `B k` to other rows, the determinant doesn't change. -/
theorem det_eq_of_forall_row_eq_smul_add_const {A B : Matrix n n R} (c : n → R) (k : n)
    (hk : c k = 0) (A_eq : ∀ i j, A i j = B i j + c i * B k j) : det A = det B :=
  det_eq_of_forall_row_eq_smul_add_const_aux c
    (fun i =>
      not_imp_comm.mp fun hi =>
        Finset.mem_erase.mpr
          ⟨mt (fun h : i = k => show c i = 0 from h.symm ▸ hk) hi, Finset.mem_univ i⟩)
    k (Finset.not_mem_erase k Finset.univ) A_eq
#align matrix.det_eq_of_forall_row_eq_smul_add_const Matrix.det_eq_of_forall_row_eq_smul_add_const

theorem det_eq_of_forall_row_eq_smul_add_pred_aux {n : ℕ} (k : Fin (n + 1)) :
    ∀ (c : Fin n → R) (hc : ∀ i : Fin n, k < i.succ → c i = 0)
      {M N : Matrix (Fin n.succ) (Fin n.succ) R} (h0 : ∀ j, M 0 j = N 0 j)
      (hsucc : ∀ (i : Fin n) (j), M i.succ j = N i.succ j + c i * M i.cast_succ j), det M = det N :=
  by
  refine' Fin.induction _ (fun k ih => _) k <;> intro c hc M N h0 hsucc
  · congr
    ext (i j)
    refine' Fin.cases (h0 j) (fun i => _) i
    rw [hsucc, hc i (Fin.succ_pos _), zero_mul, add_zero]
  set M' := update_row M k.succ (N k.succ) with hM'
  have hM : M = update_row M' k.succ (M' k.succ + c k • M k.cast_succ) :=
    by
    ext (i j)
    by_cases hi : i = k.succ
    · simp [hi, hM', hsucc, update_row_self]
    rw [update_row_ne hi, hM', update_row_ne hi]
  have k_ne_succ : k.cast_succ ≠ k.succ := (Fin.cast_succ_lt_succ k).Ne
  have M_k : M k.cast_succ = M' k.cast_succ := (update_row_ne k_ne_succ).symm
  rw [hM, M_k, det_update_row_add_smul_self M' k_ne_succ.symm, ih (Function.update c k 0)]
  · intro i hi
    rw [Fin.lt_iff_coe_lt_coe, Fin.coe_cast_succ, Fin.coe_succ, Nat.lt_succ_iff] at hi
    rw [Function.update_apply]
    split_ifs with hik
    · rfl
    exact hc _ (fin.succ_lt_succ_iff.mpr (lt_of_le_of_ne hi (Ne.symm hik)))
  · rwa [hM', update_row_ne (Fin.succ_ne_zero _).symm]
  intro i j
  rw [Function.update_apply]
  split_ifs with hik
  · rw [zero_mul, add_zero, hM', hik, update_row_self]
  rw [hM', update_row_ne ((Fin.succ_injective _).Ne hik), hsucc]
  by_cases hik2 : k < i
  · simp [hc i (fin.succ_lt_succ_iff.mpr hik2)]
  rw [update_row_ne]
  apply ne_of_lt
  rwa [Fin.lt_iff_coe_lt_coe, Fin.coe_cast_succ, Fin.coe_succ, Nat.lt_succ_iff, ← not_lt]
#align
  matrix.det_eq_of_forall_row_eq_smul_add_pred_aux Matrix.det_eq_of_forall_row_eq_smul_add_pred_aux

/-- If you add multiples of previous rows to the next row, the determinant doesn't change. -/
theorem det_eq_of_forall_row_eq_smul_add_pred {n : ℕ} {A B : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
    (c : Fin n → R) (A_zero : ∀ j, A 0 j = B 0 j)
    (A_succ : ∀ (i : Fin n) (j), A i.succ j = B i.succ j + c i * A i.cast_succ j) : det A = det B :=
  det_eq_of_forall_row_eq_smul_add_pred_aux (Fin.last _) c
    (fun i hi => absurd hi (not_lt_of_ge (Fin.le_last _))) A_zero A_succ
#align matrix.det_eq_of_forall_row_eq_smul_add_pred Matrix.det_eq_of_forall_row_eq_smul_add_pred

/-- If you add multiples of previous columns to the next columns, the determinant doesn't change. -/
theorem det_eq_of_forall_col_eq_smul_add_pred {n : ℕ} {A B : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
    (c : Fin n → R) (A_zero : ∀ i, A i 0 = B i 0)
    (A_succ : ∀ (i) (j : Fin n), A i j.succ = B i j.succ + c j * A i j.cast_succ) : det A = det B :=
  by
  rw [← det_transpose A, ← det_transpose B]
  exact det_eq_of_forall_row_eq_smul_add_pred c A_zero fun i j => A_succ j i
#align matrix.det_eq_of_forall_col_eq_smul_add_pred Matrix.det_eq_of_forall_col_eq_smul_add_pred

end DetEq

@[simp]
theorem det_block_diagonal {o : Type _} [Fintype o] [DecidableEq o] (M : o → Matrix n n R) :
    (blockDiagonal M).det = ∏ k, (M k).det :=
  by
  -- Rewrite the determinants as a sum over permutations.
  simp_rw [det_apply']
  -- The right hand side is a product of sums, rewrite it as a sum of products.
  rw [Finset.prod_sum]
  simp_rw [Finset.mem_univ, Finset.prod_attach_univ, Finset.univ_pi_univ]
  -- We claim that the only permutations contributing to the sum are those that
  -- preserve their second component.
  let preserving_snd : Finset (Equiv.Perm (n × o)) :=
    finset.univ.filter fun σ => ∀ x, (σ x).snd = x.snd
  have mem_preserving_snd :
    ∀ {σ : Equiv.Perm (n × o)}, σ ∈ preserving_snd ↔ ∀ x, (σ x).snd = x.snd := fun σ =>
    finset.mem_filter.trans ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  rw [← Finset.sum_subset (Finset.subset_univ preserving_snd) _]
  -- And that these are in bijection with `o → equiv.perm m`.
  rw [(Finset.sum_bij
        (fun (σ : ∀ k : o, k ∈ Finset.univ → Equiv.Perm n) _ =>
          prod_congr_left fun k => σ k (Finset.mem_univ k))
        _ _ _ _).symm]
  · intro σ _
    rw [mem_preserving_snd]
    rintro ⟨k, x⟩
    simp only [prod_congr_left_apply]
  · intro σ _
    rw [Finset.prod_mul_distrib, ← Finset.univ_product_univ, Finset.prod_product_right]
    simp only [sign_prod_congr_left, Units.coe_prod, Int.cast_prod, block_diagonal_apply_eq,
      prod_congr_left_apply]
  · intro σ σ' _ _ eq
    ext (x hx k)
    simp only at eq
    have :
      ∀ k x,
        prod_congr_left (fun k => σ k (Finset.mem_univ _)) (k, x) =
          prod_congr_left (fun k => σ' k (Finset.mem_univ _)) (k, x) :=
      fun k x => by rw [Eq]
    simp only [prod_congr_left_apply, Prod.mk.inj_iff] at this
    exact (this k x).1
  · intro σ hσ
    rw [mem_preserving_snd] at hσ
    have hσ' : ∀ x, (σ⁻¹ x).snd = x.snd := by
      intro x
      conv_rhs => rw [← perm.apply_inv_self σ x, hσ]
    have mk_apply_eq : ∀ k x, ((σ (x, k)).fst, k) = σ (x, k) :=
      by
      intro k x
      ext
      · simp only
      · simp only [hσ]
    have mk_inv_apply_eq : ∀ k x, ((σ⁻¹ (x, k)).fst, k) = σ⁻¹ (x, k) :=
      by
      intro k x
      conv_lhs => rw [← perm.apply_inv_self σ (x, k)]
      ext
      · simp only [apply_inv_self]
      · simp only [hσ']
    refine' ⟨fun k _ => ⟨fun x => (σ (x, k)).fst, fun x => (σ⁻¹ (x, k)).fst, _, _⟩, _, _⟩
    · intro x
      simp only [mk_apply_eq, inv_apply_self]
    · intro x
      simp only [mk_inv_apply_eq, apply_inv_self]
    · apply Finset.mem_univ
    · ext ⟨k, x⟩
      · simp only [coe_fn_mk, prod_congr_left_apply]
      · simp only [prod_congr_left_apply, hσ]
  · intro σ _ hσ
    rw [mem_preserving_snd] at hσ
    obtain ⟨⟨k, x⟩, hkx⟩ := not_forall.mp hσ
    rw [Finset.prod_eq_zero (Finset.mem_univ (k, x)), mul_zero]
    rw [← @Prod.mk.eta _ _ (σ (k, x)), block_diagonal_apply_ne]
    exact hkx
#align matrix.det_block_diagonal Matrix.det_block_diagonal

/-- The determinant of a 2×2 block matrix with the lower-left block equal to zero is the product of
the determinants of the diagonal blocks. For the generalization to any number of blocks, see
`matrix.det_of_upper_triangular`. -/
@[simp]
theorem det_from_blocks_zero₂₁ (A : Matrix m m R) (B : Matrix m n R) (D : Matrix n n R) :
    (Matrix.fromBlocks A B 0 D).det = A.det * D.det := by
  classical
    simp_rw [det_apply']
    convert
      (sum_subset (subset_univ ((sum_congr_hom m n).range : Set (perm (Sum m n))).toFinset) _).symm
    rw [sum_mul_sum]
    simp_rw [univ_product_univ]
    rw [(sum_bij (fun (σ : perm m × perm n) _ => Equiv.sumCongr σ.fst σ.snd) _ _ _ _).symm]
    · intro σ₁₂ h
      simp only
      erw [Set.mem_to_finset, MonoidHom.mem_range]
      use σ₁₂
      simp only [sum_congr_hom_apply]
    · simp only [forall_prop_of_true, Prod.forall, mem_univ]
      intro σ₁ σ₂
      rw [Fintype.prod_sum_type]
      simp_rw [Equiv.sum_congr_apply, Sum.map_inr, Sum.map_inl, from_blocks_apply₁₁,
        from_blocks_apply₂₂]
      rw [mul_mul_mul_comm]
      congr
      rw [sign_sum_congr, Units.val_mul, Int.cast_mul]
    · intro σ₁ σ₂ h₁ h₂
      dsimp only
      intro h
      have h2 : ∀ x, perm.sum_congr σ₁.fst σ₁.snd x = perm.sum_congr σ₂.fst σ₂.snd x :=
        by
        intro x
        exact congr_fun (congr_arg to_fun h) x
      simp only [Sum.map_inr, Sum.map_inl, perm.sum_congr_apply, Sum.forall] at h2
      ext
      · exact h2.left x
      · exact h2.right x
    · intro σ hσ
      erw [Set.mem_to_finset, MonoidHom.mem_range] at hσ
      obtain ⟨σ₁₂, hσ₁₂⟩ := hσ
      use σ₁₂
      rw [← hσ₁₂]
      simp
    · intro σ hσ hσn
      have h1 : ¬∀ x, ∃ y, Sum.inl y = σ (Sum.inl x) :=
        by
        by_contra
        rw [Set.mem_to_finset] at hσn
        apply absurd (mem_sum_congr_hom_range_of_perm_maps_to_inl _) hσn
        rintro x ⟨a, ha⟩
        rw [← ha]
        exact h a
      obtain ⟨a, ha⟩ := not_forall.mp h1
      cases' hx : σ (Sum.inl a) with a2 b
      · have hn := (not_exists.mp ha) a2
        exact absurd hx.symm hn
      · rw [Finset.prod_eq_zero (Finset.mem_univ (Sum.inl a)), mul_zero]
        rw [hx, from_blocks_apply₂₁]
        rfl
#align matrix.det_from_blocks_zero₂₁ Matrix.det_from_blocks_zero₂₁

/-- The determinant of a 2×2 block matrix with the upper-right block equal to zero is the product of
the determinants of the diagonal blocks. For the generalization to any number of blocks, see
`matrix.det_of_lower_triangular`. -/
@[simp]
theorem det_from_blocks_zero₁₂ (A : Matrix m m R) (C : Matrix n m R) (D : Matrix n n R) :
    (Matrix.fromBlocks A 0 C D).det = A.det * D.det := by
  rw [← det_transpose, from_blocks_transpose, transpose_zero, det_from_blocks_zero₂₁, det_transpose,
    det_transpose]
#align matrix.det_from_blocks_zero₁₂ Matrix.det_from_blocks_zero₁₂

/-- Laplacian expansion of the determinant of an `n+1 × n+1` matrix along column 0. -/
theorem det_succ_column_zero {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) R) :
    det A = ∑ i : Fin n.succ, (-1) ^ (i : ℕ) * A i 0 * det (A.submatrix i.succAbove Fin.succ) :=
  by
  rw [Matrix.det_apply, Finset.univ_perm_fin_succ, ← Finset.univ_product_univ]
  simp only [Finset.sum_map, Equiv.toEmbedding_apply, Finset.sum_product, Matrix.submatrix]
  refine' Finset.sum_congr rfl fun i _ => Fin.cases _ (fun i => _) i
  ·
    simp only [Fin.prod_univ_succ, Matrix.det_apply, Finset.mul_sum,
      Equiv.Perm.decompose_fin_symm_apply_zero, Fin.coe_zero, one_mul,
      Equiv.Perm.decomposeFin.symm_sign, Equiv.swap_self, if_true, id.def, eq_self_iff_true,
      Equiv.Perm.decompose_fin_symm_apply_succ, Fin.succ_above_zero, Equiv.coe_refl, pow_zero,
      mul_smul_comm, of_apply]
  -- `univ_perm_fin_succ` gives a different embedding of `perm (fin n)` into
  -- `perm (fin n.succ)` than the determinant of the submatrix we want,
  -- permute `A` so that we get the correct one.
  have : (-1 : R) ^ (i : ℕ) = i.cycle_range.sign := by simp [Fin.sign_cycle_range]
  rw [Fin.coe_succ, pow_succ, this, mul_assoc, mul_assoc, mul_left_comm ↑(Equiv.Perm.sign _), ←
    det_permute, Matrix.det_apply, Finset.mul_sum, Finset.mul_sum]
  -- now we just need to move the corresponding parts to the same place
  refine' Finset.sum_congr rfl fun σ _ => _
  rw [Equiv.Perm.decomposeFin.symm_sign, if_neg (Fin.succ_ne_zero i)]
  calc
    ((-1 * σ.sign : ℤ) • ∏ i', A (equiv.perm.decompose_fin.symm (Fin.succ i, σ) i') i') =
        (-1 * σ.sign : ℤ) •
          (A (Fin.succ i) 0 * ∏ i', A ((Fin.succ i).succAbove (Fin.cycleRange i (σ i'))) i'.succ) :=
      by
      simp only [Fin.prod_univ_succ, Fin.succ_above_cycle_range,
        Equiv.Perm.decompose_fin_symm_apply_zero, Equiv.Perm.decompose_fin_symm_apply_succ]
    _ =
        -1 *
          (A (Fin.succ i) 0 *
            (σ.sign : ℤ) • ∏ i', A ((Fin.succ i).succAbove (Fin.cycleRange i (σ i'))) i'.succ) :=
      by
      simp only [mul_assoc, mul_comm, _root_.neg_mul, one_mul, zsmul_eq_mul, neg_inj, neg_smul,
        Fin.succ_above_cycle_range]
    
#align matrix.det_succ_column_zero Matrix.det_succ_column_zero

/-- Laplacian expansion of the determinant of an `n+1 × n+1` matrix along row 0. -/
theorem det_succ_row_zero {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) R) :
    det A = ∑ j : Fin n.succ, (-1) ^ (j : ℕ) * A 0 j * det (A.submatrix Fin.succ j.succAbove) :=
  by
  rw [← det_transpose A, det_succ_column_zero]
  refine' Finset.sum_congr rfl fun i _ => _
  rw [← det_transpose]
  simp only [transpose_apply, transpose_submatrix, transpose_transpose]
#align matrix.det_succ_row_zero Matrix.det_succ_row_zero

/-- Laplacian expansion of the determinant of an `n+1 × n+1` matrix along row `i`. -/
theorem det_succ_row {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) R) (i : Fin n.succ) :
    det A =
      ∑ j : Fin n.succ, (-1) ^ (i + j : ℕ) * A i j * det (A.submatrix i.succAbove j.succAbove) :=
  by
  simp_rw [pow_add, mul_assoc, ← mul_sum]
  have : det A = (-1 : R) ^ (i : ℕ) * i.cycle_range⁻¹.sign * det A := by
    calc
      det A = ↑((-1 : ℤˣ) ^ (i : ℕ) * (-1 : ℤˣ) ^ (i : ℕ) : ℤˣ) * det A := by simp
      _ = (-1 : R) ^ (i : ℕ) * i.cycle_range⁻¹.sign * det A := by simp [-Int.units_mul_self]
      
  rw [this, mul_assoc]
  congr
  rw [← det_permute, det_succ_row_zero]
  refine' Finset.sum_congr rfl fun j _ => _
  rw [mul_assoc, Matrix.submatrix, Matrix.submatrix]
  congr
  · rw [Equiv.Perm.inv_def, Fin.cycle_range_symm_zero]
  · ext (i' j')
    rw [Equiv.Perm.inv_def, Fin.cycle_range_symm_succ]
#align matrix.det_succ_row Matrix.det_succ_row

/-- Laplacian expansion of the determinant of an `n+1 × n+1` matrix along column `j`. -/
theorem det_succ_column {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) R) (j : Fin n.succ) :
    det A =
      ∑ i : Fin n.succ, (-1) ^ (i + j : ℕ) * A i j * det (A.submatrix i.succAbove j.succAbove) :=
  by
  rw [← det_transpose, det_succ_row _ j]
  refine' Finset.sum_congr rfl fun i _ => _
  rw [add_comm, ← det_transpose, transpose_apply, transpose_submatrix, transpose_transpose]
#align matrix.det_succ_column Matrix.det_succ_column

/-- Determinant of 0x0 matrix -/
@[simp]
theorem det_fin_zero {A : Matrix (Fin 0) (Fin 0) R} : det A = 1 :=
  det_is_empty
#align matrix.det_fin_zero Matrix.det_fin_zero

/-- Determinant of 1x1 matrix -/
theorem det_fin_one (A : Matrix (Fin 1) (Fin 1) R) : det A = A 0 0 :=
  det_unique A
#align matrix.det_fin_one Matrix.det_fin_one

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr!![ » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation -/
theorem det_fin_one_of (a : R) :
    det
        («expr!![ »
          "./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation") =
      a :=
  det_fin_one _
#align matrix.det_fin_one_of Matrix.det_fin_one_of

/-- Determinant of 2x2 matrix -/
theorem det_fin_two (A : Matrix (Fin 2) (Fin 2) R) : det A = A 0 0 * A 1 1 - A 0 1 * A 1 0 :=
  by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  ring
#align matrix.det_fin_two Matrix.det_fin_two

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr!![ » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation -/
@[simp]
theorem det_fin_two_of (a b c d : R) :
    Matrix.det
        («expr!![ »
          "./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation") =
      a * d - b * c :=
  det_fin_two _
#align matrix.det_fin_two_of Matrix.det_fin_two_of

/-- Determinant of 3x3 matrix -/
theorem det_fin_three (A : Matrix (Fin 3) (Fin 3) R) :
    det A =
      A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1 - A 0 1 * A 1 0 * A 2 2 +
            A 0 1 * A 1 2 * A 2 0 +
          A 0 2 * A 1 0 * A 2 1 -
        A 0 2 * A 1 1 * A 2 0 :=
  by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  ring
#align matrix.det_fin_three Matrix.det_fin_three

end Matrix

