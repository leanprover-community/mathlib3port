/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Frédéric Dupuis, Heather Macbeth

! This file was ported from Lean 3 source module analysis.inner_product_space.symmetric
! leanprover-community/mathlib commit 6afc9b06856ad973f6a2619e3e8a0a8d537a58f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.InnerProductSpace.Basic
import Mathbin.Analysis.NormedSpace.Banach
import Mathbin.LinearAlgebra.SesquilinearForm

/-!
# Symmetric linear maps in an inner product space

This file defines and proves basic theorems about symmetric **not necessarily bounded** operators
on an inner product space, i.e linear maps `T : E → E` such that `∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫`.

In comparison to `is_self_adjoint`, this definition works for non-continuous linear maps, and
doesn't rely on the definition of the adjoint, which allows it to be stated in non-complete space.

## Main definitions

* `linear_map.is_symmetric`: a (not necessarily bounded) operator on an inner product space is
symmetric, if for all `x`, `y`, we have `⟪T x, y⟫ = ⟪x, T y⟫`

## Main statements

* `is_symmetric.continuous`: if a symmetric operator is defined on a complete space, then
  it is automatically continuous.

## Tags

self-adjoint, symmetric
-/


open IsROrC

open ComplexConjugate

variable {𝕜 E E' F G : Type _} [IsROrC 𝕜]

variable [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] [InnerProductSpace 𝕜 G]

variable [InnerProductSpace ℝ E']

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

namespace LinearMap

/-! ### Symmetric operators -/


/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "A (not necessarily bounded) operator on an inner product space is symmetric, if for all\n`x`, `y`, we have `⟪T x, y⟫ = ⟪x, T y⟫`. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `IsSymmetric [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`T]
         [":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `E " →ₗ[" `𝕜 "] " `E)]
         []
         ")")]
       [(Term.typeSpec ":" (Term.prop "Prop"))])
      (Command.declValSimple
       ":="
       (Term.forall
        "∀"
        [`x `y]
        []
        ","
        («term_=_»
         (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫» "⟪" (Term.app `T [`x]) ", " `y "⟫")
         "="
         (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫» "⟪" `x ", " (Term.app `T [`y]) "⟫")))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`x `y]
       []
       ","
       («term_=_»
        (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫» "⟪" (Term.app `T [`x]) ", " `y "⟫")
        "="
        (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫» "⟪" `x ", " (Term.app `T [`y]) "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫» "⟪" (Term.app `T [`x]) ", " `y "⟫")
       "="
       (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫» "⟪" `x ", " (Term.app `T [`y]) "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫» "⟪" `x ", " (Term.app `T [`y]) "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Symmetric.term⟪_,_⟫._@.Analysis.InnerProductSpace.Symmetric._hyg.6'
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
    A (not necessarily bounded) operator on an inner product space is symmetric, if for all
    `x`, `y`, we have `⟪T x, y⟫ = ⟪x, T y⟫`. -/
  def IsSymmetric ( T : E →ₗ[ 𝕜 ] E ) : Prop := ∀ x y , ⟪ T x , y ⟫ = ⟪ x , T y ⟫
#align linear_map.is_symmetric LinearMap.IsSymmetric

section Real

variable ()

/-- An operator `T` on an inner product space is symmetric if and only if it is
`linear_map.is_self_adjoint` with respect to the sesquilinear form given by the inner product. -/
theorem is_symmetric_iff_sesq_form (T : E →ₗ[𝕜] E) :
    T.IsSymmetric ↔ @LinearMap.IsSelfAdjoint 𝕜 E _ _ _ (starRingEnd 𝕜) sesqFormOfInner T :=
  ⟨fun h x y => (h y x).symm, fun h x y => (h y x).symm⟩
#align linear_map.is_symmetric_iff_sesq_form LinearMap.is_symmetric_iff_sesq_form

end Real

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `IsSymmetric.conj_inner_sym [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`T]
         [":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `E " →ₗ[" `𝕜 "] " `E)]
         "}")
        (Term.explicitBinder "(" [`hT] [":" (Term.app `IsSymmetric [`T])] [] ")")
        (Term.explicitBinder "(" [`x `y] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj")
          [(Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫» "⟪" (Term.app `T [`x]) ", " `y "⟫")])
         "="
         (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫» "⟪" (Term.app `T [`y]) ", " `x "⟫"))))
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
             [(Tactic.rwRule [] (Term.app `hT [`x `y])) "," (Tactic.rwRule [] `inner_conj_sym)]
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
            [(Tactic.rwRule [] (Term.app `hT [`x `y])) "," (Tactic.rwRule [] `inner_conj_sym)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] (Term.app `hT [`x `y])) "," (Tactic.rwRule [] `inner_conj_sym)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner_conj_sym
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hT [`x `y])
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
      `hT
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj")
        [(Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫» "⟪" (Term.app `T [`x]) ", " `y "⟫")])
       "="
       (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫» "⟪" (Term.app `T [`y]) ", " `x "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫» "⟪" (Term.app `T [`y]) ", " `x "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Symmetric.term⟪_,_⟫._@.Analysis.InnerProductSpace.Symmetric._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  IsSymmetric.conj_inner_sym
  { T : E →ₗ[ 𝕜 ] E } ( hT : IsSymmetric T ) ( x y : E ) : conj ⟪ T x , y ⟫ = ⟪ T y , x ⟫
  := by rw [ hT x y , inner_conj_sym ]
#align linear_map.is_symmetric.conj_inner_sym LinearMap.IsSymmetric.conj_inner_sym

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
      (Command.declId `IsSymmetric.apply_clm [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`T]
         [":" (Topology.Algebra.Module.Basic.«term_→L[_]_» `E " →L[" `𝕜 "] " `E)]
         "}")
        (Term.explicitBinder
         "("
         [`hT]
         [":"
          (Term.app
           `IsSymmetric
           [(Term.typeAscription
             "("
             `T
             ":"
             [(Algebra.Module.LinearMap.«term_→ₗ[_]_» `E " →ₗ[" `𝕜 "] " `E)]
             ")")])]
         []
         ")")
        (Term.explicitBinder "(" [`x `y] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫» "⟪" (Term.app `T [`x]) ", " `y "⟫")
         "="
         (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫» "⟪" `x ", " (Term.app `T [`y]) "⟫"))))
      (Command.declValSimple ":=" (Term.app `hT [`x `y]) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hT [`x `y])
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
      `hT
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫» "⟪" (Term.app `T [`x]) ", " `y "⟫")
       "="
       (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫» "⟪" `x ", " (Term.app `T [`y]) "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫» "⟪" `x ", " (Term.app `T [`y]) "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Symmetric.term⟪_,_⟫._@.Analysis.InnerProductSpace.Symmetric._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    IsSymmetric.apply_clm
    { T : E →L[ 𝕜 ] E } ( hT : IsSymmetric ( T : E →ₗ[ 𝕜 ] E ) ) ( x y : E )
      : ⟪ T x , y ⟫ = ⟪ x , T y ⟫
    := hT x y
#align linear_map.is_symmetric.apply_clm LinearMap.IsSymmetric.apply_clm

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `isSymmetricZero [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.proj
         (Term.typeAscription
          "("
          (num "0")
          ":"
          [(Algebra.Module.LinearMap.«term_→ₗ[_]_» `E " →ₗ[" `𝕜 "] " `E)]
          ")")
         "."
         `IsSymmetric)))
      (Command.declValSimple
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [`x `y]
         []
         "=>"
         (Term.subst
          (Term.proj
           (Term.typeAscription
            "("
            `inner_zero_right
            ":"
            [(«term_=_»
              (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫» "⟪" `x ", " (num "0") "⟫")
              "="
              (num "0"))]
            ")")
           "."
           `symm)
          "▸"
          [(Term.typeAscription
            "("
            `inner_zero_left
            ":"
            [(«term_=_»
              (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫» "⟪" (num "0") ", " `y "⟫")
              "="
              (num "0"))]
            ")")])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x `y]
        []
        "=>"
        (Term.subst
         (Term.proj
          (Term.typeAscription
           "("
           `inner_zero_right
           ":"
           [(«term_=_»
             (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫» "⟪" `x ", " (num "0") "⟫")
             "="
             (num "0"))]
           ")")
          "."
          `symm)
         "▸"
         [(Term.typeAscription
           "("
           `inner_zero_left
           ":"
           [(«term_=_»
             (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫» "⟪" (num "0") ", " `y "⟫")
             "="
             (num "0"))]
           ")")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.subst
       (Term.proj
        (Term.typeAscription
         "("
         `inner_zero_right
         ":"
         [(«term_=_»
           (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫» "⟪" `x ", " (num "0") "⟫")
           "="
           (num "0"))]
         ")")
        "."
        `symm)
       "▸"
       [(Term.typeAscription
         "("
         `inner_zero_left
         ":"
         [(«term_=_»
           (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫» "⟪" (num "0") ", " `y "⟫")
           "="
           (num "0"))]
         ")")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       `inner_zero_left
       ":"
       [(«term_=_»
         (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫» "⟪" (num "0") ", " `y "⟫")
         "="
         (num "0"))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫» "⟪" (num "0") ", " `y "⟫")
       "="
       (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫» "⟪" (num "0") ", " `y "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Symmetric.term⟪_,_⟫._@.Analysis.InnerProductSpace.Symmetric._hyg.6'
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
theorem
  isSymmetricZero
  : ( 0 : E →ₗ[ 𝕜 ] E ) . IsSymmetric
  := fun x y => ( inner_zero_right : ⟪ x , 0 ⟫ = 0 ) . symm ▸ ( inner_zero_left : ⟪ 0 , y ⟫ = 0 )
#align linear_map.is_symmetric_zero LinearMap.isSymmetricZero

theorem isSymmetricId : (LinearMap.id : E →ₗ[𝕜] E).IsSymmetric := fun x y => rfl
#align linear_map.is_symmetric_id LinearMap.isSymmetricId

theorem IsSymmetric.add {T S : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric) :
    (T + S).IsSymmetric := by
  intro x y
  rw [LinearMap.add_apply, inner_add_left, hT x y, hS x y, ← inner_add_right]
  rfl
#align linear_map.is_symmetric.add LinearMap.IsSymmetric.add

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The **Hellinger--Toeplitz theorem**: if a symmetric operator is defined on a complete space,\n  then it is automatically continuous. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `IsSymmetric.continuous [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `CompleteSpace [`E]) "]")
        (Term.implicitBinder
         "{"
         [`T]
         [":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `E " →ₗ[" `𝕜 "] " `E)]
         "}")
        (Term.explicitBinder "(" [`hT] [":" (Term.app `IsSymmetric [`T])] [] ")")]
       (Term.typeSpec ":" (Term.app `Continuous [`T])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.app
             `T.continuous_of_seq_closed_graph
             [(Term.fun "fun" (Term.basicFun [`u `x `y `hu `hTu] [] "=>" (Term.hole "_")))]))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_eq_zero)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `inner_self_eq_zero)]
             "]")
            [])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hlhs []]
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [`k]
                 [(Term.typeSpec ":" (termℕ "ℕ"))]
                 ","
                 («term_=_»
                  (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫»
                   "⟪"
                   («term_-_» (Term.app `T [(Term.app `u [`k])]) "-" (Term.app `T [`x]))
                   ", "
                   («term_-_» `y "-" (Term.app `T [`x]))
                   "⟫")
                  "="
                  (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫»
                   "⟪"
                   («term_-_» (Term.app `u [`k]) "-" `x)
                   ", "
                   (Term.app `T [(«term_-_» `y "-" (Term.app `T [`x]))])
                   "⟫"))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.intro "intro" [`k])
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `T.map_sub)
                     ","
                     (Tactic.rwRule [] `hT)]
                    "]")
                   [])]))))))
           []
           (Tactic.refine'
            "refine'"
            (Term.app
             `tendsto_nhds_unique
             [(Term.app
               (Term.proj (Term.app `hTu.sub_const [(Term.hole "_")]) "." `inner)
               [`tendsto_const_nhds])
              (Term.hole "_")]))
           []
           (Mathlib.Tactic.tacticSimp_rw__
            "simp_rw"
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hlhs)] "]")
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app
                (Term.explicit "@" `inner_zero_left)
                [`𝕜
                 `E
                 (Term.hole "_")
                 (Term.hole "_")
                 (Term.app `T [(«term_-_» `y "-" (Term.app `T [`x]))])]))]
             "]")
            [])
           []
           (Tactic.refine'
            "refine'"
            (Term.app `Filter.Tendsto.inner [(Term.hole "_") `tendsto_const_nhds]))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `sub_self [`x]))]
             "]")
            [])
           []
           (Tactic.exact "exact" (Term.app `hu.sub_const [(Term.hole "_")]))])))
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
           (Term.app
            `T.continuous_of_seq_closed_graph
            [(Term.fun "fun" (Term.basicFun [`u `x `y `hu `hTu] [] "=>" (Term.hole "_")))]))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_eq_zero)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `inner_self_eq_zero)]
            "]")
           [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hlhs []]
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [`k]
                [(Term.typeSpec ":" (termℕ "ℕ"))]
                ","
                («term_=_»
                 (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫»
                  "⟪"
                  («term_-_» (Term.app `T [(Term.app `u [`k])]) "-" (Term.app `T [`x]))
                  ", "
                  («term_-_» `y "-" (Term.app `T [`x]))
                  "⟫")
                 "="
                 (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫»
                  "⟪"
                  («term_-_» (Term.app `u [`k]) "-" `x)
                  ", "
                  (Term.app `T [(«term_-_» `y "-" (Term.app `T [`x]))])
                  "⟫"))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.intro "intro" [`k])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `T.map_sub)
                    ","
                    (Tactic.rwRule [] `hT)]
                   "]")
                  [])]))))))
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            `tendsto_nhds_unique
            [(Term.app
              (Term.proj (Term.app `hTu.sub_const [(Term.hole "_")]) "." `inner)
              [`tendsto_const_nhds])
             (Term.hole "_")]))
          []
          (Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hlhs)] "]")
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app
               (Term.explicit "@" `inner_zero_left)
               [`𝕜
                `E
                (Term.hole "_")
                (Term.hole "_")
                (Term.app `T [(«term_-_» `y "-" (Term.app `T [`x]))])]))]
            "]")
           [])
          []
          (Tactic.refine'
           "refine'"
           (Term.app `Filter.Tendsto.inner [(Term.hole "_") `tendsto_const_nhds]))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `sub_self [`x]))]
            "]")
           [])
          []
          (Tactic.exact "exact" (Term.app `hu.sub_const [(Term.hole "_")]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `hu.sub_const [(Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hu.sub_const [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hu.sub_const
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
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `sub_self [`x]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `sub_self [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sub_self
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app `Filter.Tendsto.inner [(Term.hole "_") `tendsto_const_nhds]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Filter.Tendsto.inner [(Term.hole "_") `tendsto_const_nhds])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tendsto_const_nhds
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Filter.Tendsto.inner
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
          (Term.app
           (Term.explicit "@" `inner_zero_left)
           [`𝕜
            `E
            (Term.hole "_")
            (Term.hole "_")
            (Term.app `T [(«term_-_» `y "-" (Term.app `T [`x]))])]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicit "@" `inner_zero_left)
       [`𝕜
        `E
        (Term.hole "_")
        (Term.hole "_")
        (Term.app `T [(«term_-_» `y "-" (Term.app `T [`x]))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `T [(«term_-_» `y "-" (Term.app `T [`x]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» `y "-" (Term.app `T [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `T [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `T
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_-_» `y "-" (Term.app `T [`x]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `T
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `T [(Term.paren "(" («term_-_» `y "-" (Term.app `T [`x])) ")")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝕜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `inner_zero_left)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner_zero_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hlhs)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hlhs
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `tendsto_nhds_unique
        [(Term.app
          (Term.proj (Term.app `hTu.sub_const [(Term.hole "_")]) "." `inner)
          [`tendsto_const_nhds])
         (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `tendsto_nhds_unique
       [(Term.app
         (Term.proj (Term.app `hTu.sub_const [(Term.hole "_")]) "." `inner)
         [`tendsto_const_nhds])
        (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app
       (Term.proj (Term.app `hTu.sub_const [(Term.hole "_")]) "." `inner)
       [`tendsto_const_nhds])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tendsto_const_nhds
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `hTu.sub_const [(Term.hole "_")]) "." `inner)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `hTu.sub_const [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hTu.sub_const
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `hTu.sub_const [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.paren "(" (Term.app `hTu.sub_const [(Term.hole "_")]) ")") "." `inner)
      [`tendsto_const_nhds])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tendsto_nhds_unique
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hlhs []]
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            [`k]
            [(Term.typeSpec ":" (termℕ "ℕ"))]
            ","
            («term_=_»
             (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫»
              "⟪"
              («term_-_» (Term.app `T [(Term.app `u [`k])]) "-" (Term.app `T [`x]))
              ", "
              («term_-_» `y "-" (Term.app `T [`x]))
              "⟫")
             "="
             (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫»
              "⟪"
              («term_-_» (Term.app `u [`k]) "-" `x)
              ", "
              (Term.app `T [(«term_-_» `y "-" (Term.app `T [`x]))])
              "⟫"))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.intro "intro" [`k])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `T.map_sub)
                ","
                (Tactic.rwRule [] `hT)]
               "]")
              [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intro "intro" [`k])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `T.map_sub)
             ","
             (Tactic.rwRule [] `hT)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `T.map_sub) "," (Tactic.rwRule [] `hT)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hT
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `T.map_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`k])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`k]
       [(Term.typeSpec ":" (termℕ "ℕ"))]
       ","
       («term_=_»
        (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫»
         "⟪"
         («term_-_» (Term.app `T [(Term.app `u [`k])]) "-" (Term.app `T [`x]))
         ", "
         («term_-_» `y "-" (Term.app `T [`x]))
         "⟫")
        "="
        (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫»
         "⟪"
         («term_-_» (Term.app `u [`k]) "-" `x)
         ", "
         (Term.app `T [(«term_-_» `y "-" (Term.app `T [`x]))])
         "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫»
        "⟪"
        («term_-_» (Term.app `T [(Term.app `u [`k])]) "-" (Term.app `T [`x]))
        ", "
        («term_-_» `y "-" (Term.app `T [`x]))
        "⟫")
       "="
       (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫»
        "⟪"
        («term_-_» (Term.app `u [`k]) "-" `x)
        ", "
        (Term.app `T [(«term_-_» `y "-" (Term.app `T [`x]))])
        "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫»
       "⟪"
       («term_-_» (Term.app `u [`k]) "-" `x)
       ", "
       (Term.app `T [(«term_-_» `y "-" (Term.app `T [`x]))])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Symmetric.term⟪_,_⟫._@.Analysis.InnerProductSpace.Symmetric._hyg.6'
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
/--
    The **Hellinger--Toeplitz theorem**: if a symmetric operator is defined on a complete space,
      then it is automatically continuous. -/
  theorem
    IsSymmetric.continuous
    [ CompleteSpace E ] { T : E →ₗ[ 𝕜 ] E } ( hT : IsSymmetric T ) : Continuous T
    :=
      by
        refine' T.continuous_of_seq_closed_graph fun u x y hu hTu => _
          rw [ ← sub_eq_zero , ← inner_self_eq_zero ]
          have
            hlhs
              : ∀ k : ℕ , ⟪ T u k - T x , y - T x ⟫ = ⟪ u k - x , T y - T x ⟫
              :=
              by intro k rw [ ← T.map_sub , hT ]
          refine' tendsto_nhds_unique hTu.sub_const _ . inner tendsto_const_nhds _
          simp_rw [ hlhs ]
          rw [ ← @ inner_zero_left 𝕜 E _ _ T y - T x ]
          refine' Filter.Tendsto.inner _ tendsto_const_nhds
          rw [ ← sub_self x ]
          exact hu.sub_const _
#align linear_map.is_symmetric.continuous LinearMap.IsSymmetric.continuous

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "For a symmetric operator `T`, the function `λ x, ⟪T x, x⟫` is real-valued. -/")]
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `IsSymmetric.coe_re_apply_inner_self_apply [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`T]
         [":" (Topology.Algebra.Module.Basic.«term_→L[_]_» `E " →L[" `𝕜 "] " `E)]
         "}")
        (Term.explicitBinder
         "("
         [`hT]
         [":"
          (Term.app
           `IsSymmetric
           [(Term.typeAscription
             "("
             `T
             ":"
             [(Algebra.Module.LinearMap.«term_→ₗ[_]_» `E " →ₗ[" `𝕜 "] " `E)]
             ")")])]
         []
         ")")
        (Term.explicitBinder "(" [`x] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.typeAscription "(" (Term.app (Term.proj `T "." `reApplyInnerSelf) [`x]) ":" [`𝕜] ")")
         "="
         (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫» "⟪" (Term.app `T [`x]) ", " `x "⟫"))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rsuffices
            "rsuffices"
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
            [":"
             («term∃_,_»
              "∃"
              (Lean.explicitBinders
               (Lean.unbracketedExplicitBinders
                [(Lean.binderIdent `r)]
                [":" (Data.Real.Basic.termℝ "ℝ")]))
              ","
              («term_=_»
               (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫» "⟪" (Term.app `T [`x]) ", " `x "⟫")
               "="
               `r))]
            [])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp
              "simp"
              []
              []
              []
              ["["
               [(Tactic.simpLemma [] [] `hr)
                ","
                (Tactic.simpLemma [] [] `T.re_apply_inner_self_apply)]
               "]"]
              [])])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eq_conj_iff_real)]
             "]")
            [])
           []
           (Tactic.exact "exact" (Term.app `hT.conj_inner_sym [`x `x]))])))
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
         [(Tactic.rsuffices
           "rsuffices"
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
           [":"
            («term∃_,_»
             "∃"
             (Lean.explicitBinders
              (Lean.unbracketedExplicitBinders
               [(Lean.binderIdent `r)]
               [":" (Data.Real.Basic.termℝ "ℝ")]))
             ","
             («term_=_»
              (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫» "⟪" (Term.app `T [`x]) ", " `x "⟫")
              "="
              `r))]
           [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             []
             ["["
              [(Tactic.simpLemma [] [] `hr)
               ","
               (Tactic.simpLemma [] [] `T.re_apply_inner_self_apply)]
              "]"]
             [])])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eq_conj_iff_real)]
            "]")
           [])
          []
          (Tactic.exact "exact" (Term.app `hT.conj_inner_sym [`x `x]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `hT.conj_inner_sym [`x `x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hT.conj_inner_sym [`x `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hT.conj_inner_sym
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
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `eq_conj_iff_real)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq_conj_iff_real
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         []
         ["["
          [(Tactic.simpLemma [] [] `hr) "," (Tactic.simpLemma [] [] `T.re_apply_inner_self_apply)]
          "]"]
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpLemma [] [] `hr) "," (Tactic.simpLemma [] [] `T.re_apply_inner_self_apply)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `T.re_apply_inner_self_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hr
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rsuffices
       "rsuffices"
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
       [":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders
          (Lean.unbracketedExplicitBinders
           [(Lean.binderIdent `r)]
           [":" (Data.Real.Basic.termℝ "ℝ")]))
         ","
         («term_=_»
          (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫» "⟪" (Term.app `T [`x]) ", " `x "⟫")
          "="
          `r))]
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders
        (Lean.unbracketedExplicitBinders [(Lean.binderIdent `r)] [":" (Data.Real.Basic.termℝ "ℝ")]))
       ","
       («term_=_»
        (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫» "⟪" (Term.app `T [`x]) ", " `x "⟫")
        "="
        `r))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫» "⟪" (Term.app `T [`x]) ", " `x "⟫")
       "="
       `r)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫» "⟪" (Term.app `T [`x]) ", " `x "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Symmetric.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Symmetric.term⟪_,_⟫._@.Analysis.InnerProductSpace.Symmetric._hyg.6'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- For a symmetric operator `T`, the function `λ x, ⟪T x, x⟫` is real-valued. -/ @[ simp ]
  theorem
    IsSymmetric.coe_re_apply_inner_self_apply
    { T : E →L[ 𝕜 ] E } ( hT : IsSymmetric ( T : E →ₗ[ 𝕜 ] E ) ) ( x : E )
      : ( T . reApplyInnerSelf x : 𝕜 ) = ⟪ T x , x ⟫
    :=
      by
        rsuffices ⟨ r , hr ⟩ : ∃ r : ℝ , ⟪ T x , x ⟫ = r
          · simp [ hr , T.re_apply_inner_self_apply ]
          rw [ ← eq_conj_iff_real ]
          exact hT.conj_inner_sym x x
#align
  linear_map.is_symmetric.coe_re_apply_inner_self_apply LinearMap.IsSymmetric.coe_re_apply_inner_self_apply

/-- If a symmetric operator preserves a submodule, its restriction to that submodule is
symmetric. -/
theorem IsSymmetric.restrictInvariant {T : E →ₗ[𝕜] E} (hT : IsSymmetric T) {V : Submodule 𝕜 E}
    (hV : ∀ v ∈ V, T v ∈ V) : IsSymmetric (T.restrict hV) := fun v w => hT v w
#align linear_map.is_symmetric.restrict_invariant LinearMap.IsSymmetric.restrictInvariant

theorem IsSymmetric.restrictScalars {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) :
    @LinearMap.IsSymmetric ℝ E _ (InnerProductSpace.isROrCToReal 𝕜 E)
      (@LinearMap.restrictScalars ℝ 𝕜 _ _ _ _ _ _ (InnerProductSpace.isROrCToReal 𝕜 E).toModule
        (InnerProductSpace.isROrCToReal 𝕜 E).toModule _ _ _ T) :=
  fun x y => by simp [hT x y, real_inner_eq_re_inner, LinearMap.coe_restrict_scalars_eq_coe]
#align linear_map.is_symmetric.restrict_scalars LinearMap.IsSymmetric.restrictScalars

section Complex

variable {V : Type _} [InnerProductSpace ℂ V]

/-- A linear operator on a complex inner product space is symmetric precisely when
`⟪T v, v⟫_ℂ` is real for all v.-/
theorem is_symmetric_iff_inner_map_self_real (T : V →ₗ[ℂ] V) :
    IsSymmetric T ↔ ∀ v : V, conj ⟪T v, v⟫_ℂ = ⟪T v, v⟫_ℂ :=
  by
  constructor
  · intro hT v
    apply is_symmetric.conj_inner_sym hT
  · intro h x y
    nth_rw 2 [← inner_conj_sym]
    nth_rw 2 [inner_map_polarization]
    simp only [star_ring_end_apply, star_div', star_sub, star_add, star_mul]
    simp only [← star_ring_end_apply]
    rw [h (x + y), h (x - y), h (x + Complex.i • y), h (x - Complex.i • y)]
    simp only [Complex.conj_I]
    rw [inner_map_polarization']
    norm_num
    ring
#align
  linear_map.is_symmetric_iff_inner_map_self_real LinearMap.is_symmetric_iff_inner_map_self_real

end Complex

end LinearMap

