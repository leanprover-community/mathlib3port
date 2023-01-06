/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux

! This file was ported from Lean 3 source module algebra.algebra.spectrum
! leanprover-community/mathlib commit 26f081a2fb920140ed5bc5cc5344e84bcc7cb2b2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Star.Pointwise
import Mathbin.Algebra.Star.Subalgebra
import Mathbin.FieldTheory.IsAlgClosed.Basic
import Mathbin.Tactic.NoncommRing

/-!
# Spectrum of an element in an algebra
This file develops the basic theory of the spectrum of an element of an algebra.
This theory will serve as the foundation for spectral theory in Banach algebras.

## Main definitions

* `resolvent_set a : set R`: the resolvent set of an element `a : A` where
  `A` is an  `R`-algebra.
* `spectrum a : set R`: the spectrum of an element `a : A` where
  `A` is an  `R`-algebra.
* `resolvent : R → A`: the resolvent function is `λ r, ring.inverse (↑ₐr - a)`, and hence
  when `r ∈ resolvent R A`, it is actually the inverse of the unit `(↑ₐr - a)`.

## Main statements

* `spectrum.unit_smul_eq_smul` and `spectrum.smul_eq_smul`: units in the scalar ring commute
  (multiplication) with the spectrum, and over a field even `0` commutes with the spectrum.
* `spectrum.left_add_coset_eq`: elements of the scalar ring commute (addition) with the spectrum.
* `spectrum.unit_mem_mul_iff_mem_swap_mul` and `spectrum.preimage_units_mul_eq_swap_mul`: the
  units (of `R`) in `σ (a*b)` coincide with those in `σ (b*a)`.
* `spectrum.scalar_eq`: in a nontrivial algebra over a field, the spectrum of a scalar is
  a singleton.
* `spectrum.subset_polynomial_aeval`, `spectrum.map_polynomial_aeval_of_degree_pos`,
  `spectrum.map_polynomial_aeval_of_nonempty`: variations on the spectral mapping theorem.

## Notations

* `σ a` : `spectrum R a` of `a : A`
-/


open Set

open Pointwise

universe u v

section Defs

variable (R : Type u) {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

-- mathport name: «expr↑ₐ»
local notation "↑ₐ" => algebraMap R A

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Given a commutative ring `R` and an `R`-algebra `A`, the *resolvent set* of `a : A`\nis the `set R` consisting of those `r : R` for which `r•1 - a` is a unit of the\nalgebra `A`.  -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `resolventSet [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`a] [":" `A] [] ")")]
       [(Term.typeSpec ":" (Term.app `Set [`R]))])
      (Command.declValSimple
       ":="
       (Set.«term{_|_}»
        "{"
        (Std.ExtendedBinder.extBinder (Lean.binderIdent `r) [(group ":" `R)])
        "|"
        (Term.app
         `IsUnit
         [(«term_-_» (Term.app (Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`r]) "-" `a)])
        "}")
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.«term{_|_}»
       "{"
       (Std.ExtendedBinder.extBinder (Lean.binderIdent `r) [(group ":" `R)])
       "|"
       (Term.app
        `IsUnit
        [(«term_-_» (Term.app (Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`r]) "-" `a)])
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `IsUnit
       [(«term_-_» (Term.app (Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`r]) "-" `a)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» (Term.app (Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`r]) "-" `a)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app (Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`r])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Algebra.Spectrum.«term↑ₐ»', expected 'Algebra.Algebra.Spectrum.term↑ₐ._@.Algebra.Algebra.Spectrum._hyg.7'
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
    Given a commutative ring `R` and an `R`-algebra `A`, the *resolvent set* of `a : A`
    is the `set R` consisting of those `r : R` for which `r•1 - a` is a unit of the
    algebra `A`.  -/
  def resolventSet ( a : A ) : Set R := { r : R | IsUnit ↑ₐ r - a }
#align resolvent_set resolventSet

/-- Given a commutative ring `R` and an `R`-algebra `A`, the *spectrum* of `a : A`
is the `set R` consisting of those `r : R` for which `r•1 - a` is not a unit of the
algebra `A`.

The spectrum is simply the complement of the resolvent set.  -/
def spectrum (a : A) : Set R :=
  resolventSet R aᶜ
#align spectrum spectrum

variable {R}

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Given an `a : A` where `A` is an `R`-algebra, the *resolvent* is\n    a map `R → A` which sends `r : R` to `(algebra_map R A r - a)⁻¹` when\n    `r ∈ resolvent R A` and `0` when `r ∈ spectrum R A`. -/")]
      []
      []
      [(Command.noncomputable "noncomputable")]
      []
      [])
     (Command.def
      "def"
      (Command.declId `resolvent [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`a] [":" `A] [] ")")
        (Term.explicitBinder "(" [`r] [":" `R] [] ")")]
       [(Term.typeSpec ":" `A)])
      (Command.declValSimple
       ":="
       (Term.app
        `Ring.inverse
        [(«term_-_» (Term.app (Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`r]) "-" `a)])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Ring.inverse
       [(«term_-_» (Term.app (Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`r]) "-" `a)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» (Term.app (Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`r]) "-" `a)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app (Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`r])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Algebra.Spectrum.«term↑ₐ»', expected 'Algebra.Algebra.Spectrum.term↑ₐ._@.Algebra.Algebra.Spectrum._hyg.7'
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
      Given an `a : A` where `A` is an `R`-algebra, the *resolvent* is
          a map `R → A` which sends `r : R` to `(algebra_map R A r - a)⁻¹` when
          `r ∈ resolvent R A` and `0` when `r ∈ spectrum R A`. -/
    noncomputable
  def resolvent ( a : A ) ( r : R ) : A := Ring.inverse ↑ₐ r - a
#align resolvent resolvent

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The unit `1 - r⁻¹ • a` constructed from `r • 1 - a` when the latter is a unit. -/")]
      [(Term.attributes
        "@["
        [(Term.attrInstance (Term.attrKind []) (Attr.simps "simps" [] (Attr.simpsArgsRest [] [])))]
        "]")]
      []
      [(Command.noncomputable "noncomputable")]
      []
      [])
     (Command.def
      "def"
      (Command.declId `IsUnit.subInvSmul [])
      (Command.optDeclSig
       [(Term.implicitBinder "{" [`r] [":" (Algebra.Group.Units.«term_ˣ» `R "ˣ")] "}")
        (Term.implicitBinder "{" [`s] [":" `R] "}")
        (Term.implicitBinder "{" [`a] [":" `A] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          («term_<|_»
           `IsUnit
           "<|"
           («term_-_»
            (Algebra.Group.Defs.«term_•_»
             `r
             " • "
             (Term.app (Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`s]))
            "-"
            `a))]
         []
         ")")]
       [(Term.typeSpec ":" (Algebra.Group.Units.«term_ˣ» `A "ˣ"))])
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `val
           []
           []
           ":="
           («term_-_»
            (Term.app (Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`s])
            "-"
            (Algebra.Group.Defs.«term_•_» («term_⁻¹» `r "⁻¹") " • " `a)))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `inv
           []
           []
           ":="
           (Algebra.Group.Defs.«term_•_»
            `r
            " • "
            (coeNotation "↑" («term_⁻¹» (Term.proj `h "." `Unit) "⁻¹"))))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `val_inv
           []
           []
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
                 [(Tactic.rwRule [] `mul_smul_comm)
                  ","
                  (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `smul_mul_assoc)
                  ","
                  (Tactic.rwRule [] `smul_sub)
                  ","
                  (Tactic.rwRule [] `smul_inv_smul)
                  ","
                  (Tactic.rwRule [] `h.mul_coe_inv)]
                 "]")
                [])]))))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `inv_val
           []
           []
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
                 [(Tactic.rwRule [] `smul_mul_assoc)
                  ","
                  (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_smul_comm)
                  ","
                  (Tactic.rwRule [] `smul_sub)
                  ","
                  (Tactic.rwRule [] `smul_inv_smul)
                  ","
                  (Tactic.rwRule [] `h.coe_inv_mul)]
                 "]")
                [])]))))))]
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
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `smul_mul_assoc)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_smul_comm)
             ","
             (Tactic.rwRule [] `smul_sub)
             ","
             (Tactic.rwRule [] `smul_inv_smul)
             ","
             (Tactic.rwRule [] `h.coe_inv_mul)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `smul_mul_assoc)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_smul_comm)
         ","
         (Tactic.rwRule [] `smul_sub)
         ","
         (Tactic.rwRule [] `smul_inv_smul)
         ","
         (Tactic.rwRule [] `h.coe_inv_mul)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h.coe_inv_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `smul_inv_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `smul_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_smul_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `smul_mul_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
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
            [(Tactic.rwRule [] `mul_smul_comm)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `smul_mul_assoc)
             ","
             (Tactic.rwRule [] `smul_sub)
             ","
             (Tactic.rwRule [] `smul_inv_smul)
             ","
             (Tactic.rwRule [] `h.mul_coe_inv)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `mul_smul_comm)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `smul_mul_assoc)
         ","
         (Tactic.rwRule [] `smul_sub)
         ","
         (Tactic.rwRule [] `smul_inv_smul)
         ","
         (Tactic.rwRule [] `h.mul_coe_inv)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h.mul_coe_inv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `smul_inv_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `smul_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `smul_mul_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_smul_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_»
       `r
       " • "
       (coeNotation "↑" («term_⁻¹» (Term.proj `h "." `Unit) "⁻¹")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (coeNotation "↑" («term_⁻¹» (Term.proj `h "." `Unit) "⁻¹"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⁻¹» (Term.proj `h "." `Unit) "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `h "." `Unit)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (some 1024,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_»
       (Term.app (Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`s])
       "-"
       (Algebra.Group.Defs.«term_•_» («term_⁻¹» `r "⁻¹") " • " `a))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_» («term_⁻¹» `r "⁻¹") " • " `a)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      («term_⁻¹» `r "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app (Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Algebra.Spectrum.«term↑ₐ»', expected 'Algebra.Algebra.Spectrum.term↑ₐ._@.Algebra.Algebra.Spectrum._hyg.7'
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
/-- The unit `1 - r⁻¹ • a` constructed from `r • 1 - a` when the latter is a unit. -/
    @[ simps ]
    noncomputable
  def
    IsUnit.subInvSmul
    { r : R ˣ } { s : R } { a : A } ( h : IsUnit <| r • ↑ₐ s - a ) : A ˣ
    where
      val := ↑ₐ s - r ⁻¹ • a
        inv := r • ↑ h . Unit ⁻¹
        val_inv
          :=
          by rw [ mul_smul_comm , ← smul_mul_assoc , smul_sub , smul_inv_smul , h.mul_coe_inv ]
        inv_val
          :=
          by rw [ smul_mul_assoc , ← mul_smul_comm , smul_sub , smul_inv_smul , h.coe_inv_mul ]
#align is_unit.sub_inv_smul IsUnit.subInvSmul

end Defs

namespace spectrum

open Polynomial

section ScalarSemiring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

-- mathport name: exprσ
local notation "σ" => spectrum R

-- mathport name: «expr↑ₐ»
local notation "↑ₐ" => algebraMap R A

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mem_iff [])
      (Command.declSig
       [(Term.implicitBinder "{" [`r] [":" `R] "}") (Term.implicitBinder "{" [`a] [":" `A] "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_∈_» `r "∈" (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [`a]))
         "↔"
         («term¬_»
          "¬"
          (Term.app
           `IsUnit
           [(«term_-_»
             (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`r])
             "-"
             `a)])))))
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
       («term_∈_» `r "∈" (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [`a]))
       "↔"
       («term¬_»
        "¬"
        (Term.app
         `IsUnit
         [(«term_-_» (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`r]) "-" `a)])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term¬_»
       "¬"
       (Term.app
        `IsUnit
        [(«term_-_» (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`r]) "-" `a)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `IsUnit
       [(«term_-_» (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`r]) "-" `a)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`r]) "-" `a)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`r])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Algebra.Algebra.Spectrum.«term↑ₐ»', expected 'spectrum.Algebra.Algebra.Spectrum.term↑ₐ._@.Algebra.Algebra.Spectrum._hyg.1096'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem mem_iff { r : R } { a : A } : r ∈ σ a ↔ ¬ IsUnit ↑ₐ r - a := Iff.rfl
#align spectrum.mem_iff spectrum.mem_iff

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `not_mem_iff [])
      (Command.declSig
       [(Term.implicitBinder "{" [`r] [":" `R] "}") (Term.implicitBinder "{" [`a] [":" `A] "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_∉_» `r "∉" (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [`a]))
         "↔"
         (Term.app
          `IsUnit
          [(«term_-_» (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`r]) "-" `a)]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.apply "apply" `not_iff_not.mp)
           []
           (Tactic.simp
            "simp"
            []
            []
            []
            ["["
             [(Tactic.simpLemma [] [] `Set.not_not_mem) "," (Tactic.simpLemma [] [] `mem_iff)]
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
         [(Tactic.apply "apply" `not_iff_not.mp)
          []
          (Tactic.simp
           "simp"
           []
           []
           []
           ["["
            [(Tactic.simpLemma [] [] `Set.not_not_mem) "," (Tactic.simpLemma [] [] `mem_iff)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["[" [(Tactic.simpLemma [] [] `Set.not_not_mem) "," (Tactic.simpLemma [] [] `mem_iff)] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.not_not_mem
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `not_iff_not.mp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `not_iff_not.mp
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_∉_» `r "∉" (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [`a]))
       "↔"
       (Term.app
        `IsUnit
        [(«term_-_» (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`r]) "-" `a)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `IsUnit
       [(«term_-_» (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`r]) "-" `a)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`r]) "-" `a)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`r])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Algebra.Algebra.Spectrum.«term↑ₐ»', expected 'spectrum.Algebra.Algebra.Spectrum.term↑ₐ._@.Algebra.Algebra.Spectrum._hyg.1096'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  not_mem_iff
  { r : R } { a : A } : r ∉ σ a ↔ IsUnit ↑ₐ r - a
  := by apply not_iff_not.mp simp [ Set.not_not_mem , mem_iff ]
#align spectrum.not_mem_iff spectrum.not_mem_iff

variable (R)

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `zero_mem_iff [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a] [":" `A] "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_∈_»
          (Term.typeAscription "(" (num "0") ":" [`R] ")")
          "∈"
          (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [`a]))
         "↔"
         («term¬_» "¬" (Term.app `IsUnit [`a])))))
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
             [(Tactic.rwRule [] `mem_iff)
              ","
              (Tactic.rwRule [] `map_zero)
              ","
              (Tactic.rwRule [] `zero_sub)
              ","
              (Tactic.rwRule [] `IsUnit.neg_iff)]
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
            [(Tactic.rwRule [] `mem_iff)
             ","
             (Tactic.rwRule [] `map_zero)
             ","
             (Tactic.rwRule [] `zero_sub)
             ","
             (Tactic.rwRule [] `IsUnit.neg_iff)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `mem_iff)
         ","
         (Tactic.rwRule [] `map_zero)
         ","
         (Tactic.rwRule [] `zero_sub)
         ","
         (Tactic.rwRule [] `IsUnit.neg_iff)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `IsUnit.neg_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_∈_»
        (Term.typeAscription "(" (num "0") ":" [`R] ")")
        "∈"
        (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [`a]))
       "↔"
       («term¬_» "¬" (Term.app `IsUnit [`a])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term¬_» "¬" (Term.app `IsUnit [`a]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsUnit [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsUnit
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 40 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 21 >? 1024, (some 40, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      («term_∈_»
       (Term.typeAscription "(" (num "0") ":" [`R] ")")
       "∈"
       (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [`a]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Algebra.Algebra.Spectrum.termσ "σ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Algebra.Algebra.Spectrum.termσ', expected 'spectrum.Algebra.Algebra.Spectrum.termσ._@.Algebra.Algebra.Spectrum._hyg.600'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  zero_mem_iff
  { a : A } : ( 0 : R ) ∈ σ a ↔ ¬ IsUnit a
  := by rw [ mem_iff , map_zero , zero_sub , IsUnit.neg_iff ]
#align spectrum.zero_mem_iff spectrum.zero_mem_iff

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `zero_not_mem_iff [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a] [":" `A] "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_∉_»
          (Term.typeAscription "(" (num "0") ":" [`R] ")")
          "∉"
          (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [`a]))
         "↔"
         (Term.app `IsUnit [`a]))))
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
             [(Tactic.rwRule [] `zero_mem_iff) "," (Tactic.rwRule [] `not_not)]
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
            [(Tactic.rwRule [] `zero_mem_iff) "," (Tactic.rwRule [] `not_not)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `zero_mem_iff) "," (Tactic.rwRule [] `not_not)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `not_not
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_mem_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_∉_»
        (Term.typeAscription "(" (num "0") ":" [`R] ")")
        "∉"
        (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [`a]))
       "↔"
       (Term.app `IsUnit [`a]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsUnit [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsUnit
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      («term_∉_»
       (Term.typeAscription "(" (num "0") ":" [`R] ")")
       "∉"
       (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [`a]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Algebra.Algebra.Spectrum.termσ "σ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Algebra.Algebra.Spectrum.termσ', expected 'spectrum.Algebra.Algebra.Spectrum.termσ._@.Algebra.Algebra.Spectrum._hyg.600'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem zero_not_mem_iff { a : A } : ( 0 : R ) ∉ σ a ↔ IsUnit a := by rw [ zero_mem_iff , not_not ]
#align spectrum.zero_not_mem_iff spectrum.zero_not_mem_iff

variable {R}

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mem_resolvent_set_of_left_right_inverse [])
      (Command.declSig
       [(Term.implicitBinder "{" [`r] [":" `R] "}")
        (Term.implicitBinder "{" [`a `b `c] [":" `A] "}")
        (Term.explicitBinder
         "("
         [`h₁]
         [":"
          («term_=_»
           («term_*_»
            («term_-_» (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`r]) "-" `a)
            "*"
            `b)
           "="
           (num "1"))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`h₂]
         [":"
          («term_=_»
           («term_*_»
            `c
            "*"
            («term_-_» (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`r]) "-" `a))
           "="
           (num "1"))]
         []
         ")")]
       (Term.typeSpec ":" («term_∈_» `r "∈" (Term.app `resolventSet [`R `a]))))
      (Command.declValSimple
       ":="
       (Term.app
        `Units.isUnit
        [(Term.anonymousCtor
          "⟨"
          [(«term_-_» (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`r]) "-" `a)
           ","
           `b
           ","
           `h₁
           ","
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.tacticRwa__
                "rwa"
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule
                   [(patternIgnore (token.«← » "←"))]
                   (Term.app `left_inv_eq_right_inv [`h₂ `h₁]))]
                 "]")
                [])])))]
          "⟩")])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Units.isUnit
       [(Term.anonymousCtor
         "⟨"
         [(«term_-_» (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`r]) "-" `a)
          ","
          `b
          ","
          `h₁
          ","
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Std.Tactic.tacticRwa__
               "rwa"
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule
                  [(patternIgnore (token.«← » "←"))]
                  (Term.app `left_inv_eq_right_inv [`h₂ `h₁]))]
                "]")
               [])])))]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(«term_-_» (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`r]) "-" `a)
        ","
        `b
        ","
        `h₁
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Std.Tactic.tacticRwa__
             "rwa"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.app `left_inv_eq_right_inv [`h₂ `h₁]))]
              "]")
             [])])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.tacticRwa__
           "rwa"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app `left_inv_eq_right_inv [`h₂ `h₁]))]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app `left_inv_eq_right_inv [`h₂ `h₁]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `left_inv_eq_right_inv [`h₂ `h₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `left_inv_eq_right_inv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`r]) "-" `a)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`r])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Algebra.Algebra.Spectrum.«term↑ₐ»', expected 'spectrum.Algebra.Algebra.Spectrum.term↑ₐ._@.Algebra.Algebra.Spectrum._hyg.1096'
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
  mem_resolvent_set_of_left_right_inverse
  { r : R } { a b c : A } ( h₁ : ↑ₐ r - a * b = 1 ) ( h₂ : c * ↑ₐ r - a = 1 ) : r ∈ resolventSet R a
  := Units.isUnit ⟨ ↑ₐ r - a , b , h₁ , by rwa [ ← left_inv_eq_right_inv h₂ h₁ ] ⟩
#align
  spectrum.mem_resolvent_set_of_left_right_inverse spectrum.mem_resolvent_set_of_left_right_inverse

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mem_resolvent_set_iff [])
      (Command.declSig
       [(Term.implicitBinder "{" [`r] [":" `R] "}") (Term.implicitBinder "{" [`a] [":" `A] "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_∈_» `r "∈" (Term.app `resolventSet [`R `a]))
         "↔"
         (Term.app
          `IsUnit
          [(«term_-_» (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`r]) "-" `a)]))))
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
       («term_∈_» `r "∈" (Term.app `resolventSet [`R `a]))
       "↔"
       (Term.app
        `IsUnit
        [(«term_-_» (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`r]) "-" `a)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `IsUnit
       [(«term_-_» (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`r]) "-" `a)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`r]) "-" `a)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`r])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Algebra.Algebra.Spectrum.«term↑ₐ»', expected 'spectrum.Algebra.Algebra.Spectrum.term↑ₐ._@.Algebra.Algebra.Spectrum._hyg.1096'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  mem_resolvent_set_iff
  { r : R } { a : A } : r ∈ resolventSet R a ↔ IsUnit ↑ₐ r - a
  := Iff.rfl
#align spectrum.mem_resolvent_set_iff spectrum.mem_resolvent_set_iff

@[simp]
theorem resolvent_set_of_subsingleton [Subsingleton A] (a : A) : resolventSet R a = Set.univ := by
  simp_rw [resolventSet, Subsingleton.elim (algebraMap R A _ - a) 1, isUnit_one, Set.setOf_true]
#align spectrum.resolvent_set_of_subsingleton spectrum.resolvent_set_of_subsingleton

@[simp]
theorem of_subsingleton [Subsingleton A] (a : A) : spectrum R a = ∅ := by
  rw [spectrum, resolvent_set_of_subsingleton, Set.compl_univ]
#align spectrum.of_subsingleton spectrum.of_subsingleton

theorem resolvent_eq {a : A} {r : R} (h : r ∈ resolventSet R a) : resolvent a r = ↑h.Unit⁻¹ :=
  Ring.inverse_unit h.Unit
#align spectrum.resolvent_eq spectrum.resolvent_eq

theorem units_smul_resolvent {r : Rˣ} {s : R} {a : A} :
    r • resolvent a (s : R) = resolvent (r⁻¹ • a) (r⁻¹ • s : R) :=
  by
  by_cases h : s ∈ spectrum R a
  · rw [mem_iff] at h
    simp only [resolvent, Algebra.algebra_map_eq_smul_one] at *
    rw [smul_assoc, ← smul_sub]
    have h' : ¬IsUnit (r⁻¹ • (s • 1 - a)) := fun hu =>
      h (by simpa only [smul_inv_smul] using IsUnit.smul r hu)
    simp only [Ring.inverse_non_unit _ h, Ring.inverse_non_unit _ h', smul_zero]
  · simp only [resolvent]
    have h' : IsUnit (r • algebraMap R A (r⁻¹ • s) - a) := by
      simpa [Algebra.algebra_map_eq_smul_one, smul_assoc] using not_mem_iff.mp h
    rw [← h'.coe_sub_inv_smul, ← (not_mem_iff.mp h).unit_spec, Ring.inverse_unit, Ring.inverse_unit,
      h'.coe_inv_sub_inv_smul]
    simp only [Algebra.algebra_map_eq_smul_one, smul_assoc, smul_inv_smul]
#align spectrum.units_smul_resolvent spectrum.units_smul_resolvent

theorem units_smul_resolvent_self {r : Rˣ} {a : A} :
    r • resolvent a (r : R) = resolvent (r⁻¹ • a) (1 : R) := by
  simpa only [Units.smul_def, Algebra.id.smul_eq_mul, Units.inv_mul] using
    @units_smul_resolvent _ _ _ _ _ r r a
#align spectrum.units_smul_resolvent_self spectrum.units_smul_resolvent_self

/-- The resolvent is a unit when the argument is in the resolvent set. -/
theorem is_unit_resolvent {r : R} {a : A} : r ∈ resolventSet R a ↔ IsUnit (resolvent a r) :=
  isUnit_ring_inverse.symm
#align spectrum.is_unit_resolvent spectrum.is_unit_resolvent

theorem inv_mem_resolvent_set {r : Rˣ} {a : Aˣ} (h : (r : R) ∈ resolventSet R (a : A)) :
    (↑r⁻¹ : R) ∈ resolventSet R (↑a⁻¹ : A) :=
  by
  rw [mem_resolvent_set_iff, Algebra.algebra_map_eq_smul_one, ← Units.smul_def] at h⊢
  rw [IsUnit.smul_sub_iff_sub_inv_smul, inv_inv, IsUnit.sub_iff]
  have h₁ : (a : A) * (r • (↑a⁻¹ : A) - 1) = r • 1 - a := by
    rw [mul_sub, mul_smul_comm, a.mul_inv, mul_one]
  have h₂ : (r • (↑a⁻¹ : A) - 1) * a = r • 1 - a := by
    rw [sub_mul, smul_mul_assoc, a.inv_mul, one_mul]
  have hcomm : Commute (a : A) (r • (↑a⁻¹ : A) - 1) := by rwa [← h₂] at h₁
  exact (hcomm.is_unit_mul_iff.mp (h₁.symm ▸ h)).2
#align spectrum.inv_mem_resolvent_set spectrum.inv_mem_resolvent_set

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `inv_mem_iff [])
      (Command.declSig
       [(Term.implicitBinder "{" [`r] [":" (Algebra.Group.Units.«term_ˣ» `R "ˣ")] "}")
        (Term.implicitBinder "{" [`a] [":" (Algebra.Group.Units.«term_ˣ» `A "ˣ")] "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_∈_»
          (Term.typeAscription "(" `r ":" [`R] ")")
          "∈"
          (Term.app
           (spectrum.Algebra.Algebra.Spectrum.termσ "σ")
           [(Term.typeAscription "(" `a ":" [`A] ")")]))
         "↔"
         («term_∈_»
          (Term.typeAscription "(" (coeNotation "↑" («term_⁻¹» `r "⁻¹")) ":" [`R] ")")
          "∈"
          (Term.app
           (spectrum.Algebra.Algebra.Spectrum.termσ "σ")
           [(Term.typeAscription "(" (coeNotation "↑" («term_⁻¹» `a "⁻¹")) ":" [`A] ")")])))))
      (Command.declValSimple
       ":="
       («term_<|_»
        (Term.proj `not_iff_not "." (fieldIdx "2"))
        "<|"
        (Term.anonymousCtor "⟨" [`inv_mem_resolvent_set "," `inv_mem_resolvent_set] "⟩"))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj `not_iff_not "." (fieldIdx "2"))
       "<|"
       (Term.anonymousCtor "⟨" [`inv_mem_resolvent_set "," `inv_mem_resolvent_set] "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`inv_mem_resolvent_set "," `inv_mem_resolvent_set] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inv_mem_resolvent_set
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inv_mem_resolvent_set
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `not_iff_not "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `not_iff_not
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_∈_»
        (Term.typeAscription "(" `r ":" [`R] ")")
        "∈"
        (Term.app
         (spectrum.Algebra.Algebra.Spectrum.termσ "σ")
         [(Term.typeAscription "(" `a ":" [`A] ")")]))
       "↔"
       («term_∈_»
        (Term.typeAscription "(" (coeNotation "↑" («term_⁻¹» `r "⁻¹")) ":" [`R] ")")
        "∈"
        (Term.app
         (spectrum.Algebra.Algebra.Spectrum.termσ "σ")
         [(Term.typeAscription "(" (coeNotation "↑" («term_⁻¹» `a "⁻¹")) ":" [`A] ")")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_»
       (Term.typeAscription "(" (coeNotation "↑" («term_⁻¹» `r "⁻¹")) ":" [`R] ")")
       "∈"
       (Term.app
        (spectrum.Algebra.Algebra.Spectrum.termσ "σ")
        [(Term.typeAscription "(" (coeNotation "↑" («term_⁻¹» `a "⁻¹")) ":" [`A] ")")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (spectrum.Algebra.Algebra.Spectrum.termσ "σ")
       [(Term.typeAscription "(" (coeNotation "↑" («term_⁻¹» `a "⁻¹")) ":" [`A] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" (coeNotation "↑" («term_⁻¹» `a "⁻¹")) ":" [`A] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (coeNotation "↑" («term_⁻¹» `a "⁻¹"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⁻¹» `a "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Algebra.Algebra.Spectrum.termσ "σ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Algebra.Algebra.Spectrum.termσ', expected 'spectrum.Algebra.Algebra.Spectrum.termσ._@.Algebra.Algebra.Spectrum._hyg.600'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  inv_mem_iff
  { r : R ˣ } { a : A ˣ } : ( r : R ) ∈ σ ( a : A ) ↔ ( ↑ r ⁻¹ : R ) ∈ σ ( ↑ a ⁻¹ : A )
  := not_iff_not . 2 <| ⟨ inv_mem_resolvent_set , inv_mem_resolvent_set ⟩
#align spectrum.inv_mem_iff spectrum.inv_mem_iff

theorem zero_mem_resolvent_set_of_unit (a : Aˣ) : 0 ∈ resolventSet R (a : A) := by
  simpa only [mem_resolvent_set_iff, ← not_mem_iff, zero_not_mem_iff] using a.is_unit
#align spectrum.zero_mem_resolvent_set_of_unit spectrum.zero_mem_resolvent_set_of_unit

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `ne_zero_of_mem_of_unit [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a] [":" (Algebra.Group.Units.«term_ˣ» `A "ˣ")] "}")
        (Term.implicitBinder "{" [`r] [":" `R] "}")
        (Term.explicitBinder
         "("
         [`hr]
         [":"
          («term_∈_»
           `r
           "∈"
           (Term.app
            (spectrum.Algebra.Algebra.Spectrum.termσ "σ")
            [(Term.typeAscription "(" `a ":" [`A] ")")]))]
         []
         ")")]
       (Term.typeSpec ":" («term_≠_» `r "≠" (num "0"))))
      (Command.declValSimple
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [`hn]
         []
         "=>"
         (Term.app (Term.subst `hn "▸" [`hr]) [(Term.app `zero_mem_resolvent_set_of_unit [`a])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`hn]
        []
        "=>"
        (Term.app (Term.subst `hn "▸" [`hr]) [(Term.app `zero_mem_resolvent_set_of_unit [`a])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.subst `hn "▸" [`hr]) [(Term.app `zero_mem_resolvent_set_of_unit [`a])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `zero_mem_resolvent_set_of_unit [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `zero_mem_resolvent_set_of_unit
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `zero_mem_resolvent_set_of_unit [`a])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.subst `hn "▸" [`hr])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hr
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 75, term))
      `hn
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 75, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 75, (some 75, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.subst `hn "▸" [`hr]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hn
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≠_» `r "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_»
       `r
       "∈"
       (Term.app
        (spectrum.Algebra.Algebra.Spectrum.termσ "σ")
        [(Term.typeAscription "(" `a ":" [`A] ")")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (spectrum.Algebra.Algebra.Spectrum.termσ "σ")
       [(Term.typeAscription "(" `a ":" [`A] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" `a ":" [`A] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Algebra.Algebra.Spectrum.termσ "σ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Algebra.Algebra.Spectrum.termσ', expected 'spectrum.Algebra.Algebra.Spectrum.termσ._@.Algebra.Algebra.Spectrum._hyg.600'
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
  ne_zero_of_mem_of_unit
  { a : A ˣ } { r : R } ( hr : r ∈ σ ( a : A ) ) : r ≠ 0
  := fun hn => hn ▸ hr zero_mem_resolvent_set_of_unit a
#align spectrum.ne_zero_of_mem_of_unit spectrum.ne_zero_of_mem_of_unit

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `add_mem_iff [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a] [":" `A] "}") (Term.implicitBinder "{" [`r `s] [":" `R] "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_∈_»
          («term_+_» `r "+" `s)
          "∈"
          (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [`a]))
         "↔"
         («term_∈_»
          `r
          "∈"
          (Term.app
           (spectrum.Algebra.Algebra.Spectrum.termσ "σ")
           [(«term_+_»
             («term-_» "-" (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`s]))
             "+"
             `a)])))))
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
             [(Tactic.simpLemma [] [] `mem_iff)
              ","
              (Tactic.simpLemma [] [] `sub_neg_eq_add)
              ","
              (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `sub_sub)
              ","
              (Tactic.simpLemma [] [] `map_add)]
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
            [(Tactic.simpLemma [] [] `mem_iff)
             ","
             (Tactic.simpLemma [] [] `sub_neg_eq_add)
             ","
             (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `sub_sub)
             ","
             (Tactic.simpLemma [] [] `map_add)]
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
        [(Tactic.simpLemma [] [] `mem_iff)
         ","
         (Tactic.simpLemma [] [] `sub_neg_eq_add)
         ","
         (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `sub_sub)
         ","
         (Tactic.simpLemma [] [] `map_add)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_neg_eq_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_∈_»
        («term_+_» `r "+" `s)
        "∈"
        (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [`a]))
       "↔"
       («term_∈_»
        `r
        "∈"
        (Term.app
         (spectrum.Algebra.Algebra.Spectrum.termσ "σ")
         [(«term_+_»
           («term-_» "-" (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`s]))
           "+"
           `a)])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_»
       `r
       "∈"
       (Term.app
        (spectrum.Algebra.Algebra.Spectrum.termσ "σ")
        [(«term_+_»
          («term-_» "-" (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`s]))
          "+"
          `a)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (spectrum.Algebra.Algebra.Spectrum.termσ "σ")
       [(«term_+_»
         («term-_» "-" (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`s]))
         "+"
         `a)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       («term-_» "-" (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`s]))
       "+"
       `a)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term-_» "-" (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`s]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Algebra.Algebra.Spectrum.«term↑ₐ»', expected 'spectrum.Algebra.Algebra.Spectrum.term↑ₐ._@.Algebra.Algebra.Spectrum._hyg.1096'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  add_mem_iff
  { a : A } { r s : R } : r + s ∈ σ a ↔ r ∈ σ - ↑ₐ s + a
  := by simp only [ mem_iff , sub_neg_eq_add , ← sub_sub , map_add ]
#align spectrum.add_mem_iff spectrum.add_mem_iff

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `add_mem_add_iff [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a] [":" `A] "}") (Term.implicitBinder "{" [`r `s] [":" `R] "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_∈_»
          («term_+_» `r "+" `s)
          "∈"
          (Term.app
           (spectrum.Algebra.Algebra.Spectrum.termσ "σ")
           [(«term_+_» (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`s]) "+" `a)]))
         "↔"
         («term_∈_» `r "∈" (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [`a])))))
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
             [(Tactic.rwRule [] `add_mem_iff) "," (Tactic.rwRule [] `neg_add_cancel_left)]
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
            [(Tactic.rwRule [] `add_mem_iff) "," (Tactic.rwRule [] `neg_add_cancel_left)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `add_mem_iff) "," (Tactic.rwRule [] `neg_add_cancel_left)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `neg_add_cancel_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_mem_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_∈_»
        («term_+_» `r "+" `s)
        "∈"
        (Term.app
         (spectrum.Algebra.Algebra.Spectrum.termσ "σ")
         [(«term_+_» (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ» "↑ₐ") [`s]) "+" `a)]))
       "↔"
       («term_∈_» `r "∈" (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [`a])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_» `r "∈" (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [`a]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Algebra.Algebra.Spectrum.termσ "σ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Algebra.Algebra.Spectrum.termσ', expected 'spectrum.Algebra.Algebra.Spectrum.termσ._@.Algebra.Algebra.Spectrum._hyg.600'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  add_mem_add_iff
  { a : A } { r s : R } : r + s ∈ σ ↑ₐ s + a ↔ r ∈ σ a
  := by rw [ add_mem_iff , neg_add_cancel_left ]
#align spectrum.add_mem_add_iff spectrum.add_mem_add_iff

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `smul_mem_smul_iff [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a] [":" `A] "}")
        (Term.implicitBinder "{" [`s] [":" `R] "}")
        (Term.implicitBinder "{" [`r] [":" (Algebra.Group.Units.«term_ˣ» `R "ˣ")] "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_∈_»
          (Algebra.Group.Defs.«term_•_» `r " • " `s)
          "∈"
          (Term.app
           (spectrum.Algebra.Algebra.Spectrum.termσ "σ")
           [(Algebra.Group.Defs.«term_•_» `r " • " `a)]))
         "↔"
         («term_∈_» `s "∈" (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [`a])))))
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
             [(Tactic.simpLemma [] [] `mem_iff)
              ","
              (Tactic.simpLemma [] [] `not_iff_not)
              ","
              (Tactic.simpLemma [] [] `Algebra.algebra_map_eq_smul_one)
              ","
              (Tactic.simpLemma [] [] `smul_assoc)
              ","
              (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `smul_sub)
              ","
              (Tactic.simpLemma [] [] `isUnit_smul_iff)]
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
            [(Tactic.simpLemma [] [] `mem_iff)
             ","
             (Tactic.simpLemma [] [] `not_iff_not)
             ","
             (Tactic.simpLemma [] [] `Algebra.algebra_map_eq_smul_one)
             ","
             (Tactic.simpLemma [] [] `smul_assoc)
             ","
             (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `smul_sub)
             ","
             (Tactic.simpLemma [] [] `isUnit_smul_iff)]
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
        [(Tactic.simpLemma [] [] `mem_iff)
         ","
         (Tactic.simpLemma [] [] `not_iff_not)
         ","
         (Tactic.simpLemma [] [] `Algebra.algebra_map_eq_smul_one)
         ","
         (Tactic.simpLemma [] [] `smul_assoc)
         ","
         (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `smul_sub)
         ","
         (Tactic.simpLemma [] [] `isUnit_smul_iff)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `isUnit_smul_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `smul_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `smul_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Algebra.algebra_map_eq_smul_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `not_iff_not
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_∈_»
        (Algebra.Group.Defs.«term_•_» `r " • " `s)
        "∈"
        (Term.app
         (spectrum.Algebra.Algebra.Spectrum.termσ "σ")
         [(Algebra.Group.Defs.«term_•_» `r " • " `a)]))
       "↔"
       («term_∈_» `s "∈" (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [`a])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_» `s "∈" (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [`a]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Algebra.Algebra.Spectrum.termσ "σ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Algebra.Algebra.Spectrum.termσ', expected 'spectrum.Algebra.Algebra.Spectrum.termσ._@.Algebra.Algebra.Spectrum._hyg.600'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  smul_mem_smul_iff
  { a : A } { s : R } { r : R ˣ } : r • s ∈ σ r • a ↔ s ∈ σ a
  :=
    by
      simp
        only
        [
          mem_iff
            ,
            not_iff_not
            ,
            Algebra.algebra_map_eq_smul_one
            ,
            smul_assoc
            ,
            ← smul_sub
            ,
            isUnit_smul_iff
          ]
#align spectrum.smul_mem_smul_iff spectrum.smul_mem_smul_iff

open Polynomial

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `unit_smul_eq_smul [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" `A] [] ")")
        (Term.explicitBinder "(" [`r] [":" (Algebra.Group.Units.«term_ˣ» `R "ˣ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (spectrum.Algebra.Algebra.Spectrum.termσ "σ")
          [(Algebra.Group.Defs.«term_•_» `r " • " `a)])
         "="
         (Algebra.Group.Defs.«term_•_»
          `r
          " • "
          (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [`a])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`x_eq []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 `x
                 "="
                 (Algebra.Group.Defs.«term_•_»
                  `r
                  " • "
                  (Algebra.Group.Defs.«term_•_» («term_⁻¹» `r "⁻¹") " • " `x))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])]))))))
           []
           (Mathlib.Tactic.nthRwSeq
            "nth_rw"
            []
            (num "1")
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `x_eq)] "]")
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `smul_mem_smul_iff)] "]")
            [])
           []
           (Tactic.constructor "constructor")
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.exact
              "exact"
              (Term.fun
               "fun"
               (Term.basicFun
                [`h]
                []
                "=>"
                (Term.anonymousCtor
                 "⟨"
                 [(Algebra.Group.Defs.«term_•_» («term_⁻¹» `r "⁻¹") " • " `x)
                  ","
                  (Term.anonymousCtor
                   "⟨"
                   [`h
                    ","
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]
                   "⟩")]
                 "⟩"))))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.rintro
              "rintro"
              [(Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x'_eq)])
                   [])]
                 "⟩"))]
              [])
             []
             (Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest
               []
               []
               []
               [(Tactic.simpArgs
                 "["
                 [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `x'_eq)]
                 "]")]
               []))])])))
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
         [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`x_eq []]
             [(Term.typeSpec
               ":"
               («term_=_»
                `x
                "="
                (Algebra.Group.Defs.«term_•_»
                 `r
                 " • "
                 (Algebra.Group.Defs.«term_•_» («term_⁻¹» `r "⁻¹") " • " `x))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])]))))))
          []
          (Mathlib.Tactic.nthRwSeq
           "nth_rw"
           []
           (num "1")
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `x_eq)] "]")
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `smul_mem_smul_iff)] "]")
           [])
          []
          (Tactic.constructor "constructor")
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact
             "exact"
             (Term.fun
              "fun"
              (Term.basicFun
               [`h]
               []
               "=>"
               (Term.anonymousCtor
                "⟨"
                [(Algebra.Group.Defs.«term_•_» («term_⁻¹» `r "⁻¹") " • " `x)
                 ","
                 (Term.anonymousCtor
                  "⟨"
                  [`h
                   ","
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]
                  "⟩")]
                "⟩"))))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.rintro
             "rintro"
             [(Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x'_eq)])
                  [])]
                "⟩"))]
             [])
            []
            (Std.Tactic.Simpa.simpa
             "simpa"
             []
             []
             (Std.Tactic.Simpa.simpaArgsRest
              []
              []
              []
              [(Tactic.simpArgs
                "["
                [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `x'_eq)]
                "]")]
              []))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.rintro
         "rintro"
         [(Std.Tactic.RCases.rintroPat.one
           (Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x'_eq)])
              [])]
            "⟩"))]
         [])
        []
        (Std.Tactic.Simpa.simpa
         "simpa"
         []
         []
         (Std.Tactic.Simpa.simpaArgsRest
          []
          []
          []
          [(Tactic.simpArgs
            "["
            [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `x'_eq)]
            "]")]
          []))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        []
        [(Tactic.simpArgs
          "["
          [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `x'_eq)]
          "]")]
        []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x'_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rintro
       "rintro"
       [(Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x'_eq)])
            [])]
          "⟩"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact
         "exact"
         (Term.fun
          "fun"
          (Term.basicFun
           [`h]
           []
           "=>"
           (Term.anonymousCtor
            "⟨"
            [(Algebra.Group.Defs.«term_•_» («term_⁻¹» `r "⁻¹") " • " `x)
             ","
             (Term.anonymousCtor
              "⟨"
              [`h
               ","
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]
              "⟩")]
            "⟩"))))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.fun
        "fun"
        (Term.basicFun
         [`h]
         []
         "=>"
         (Term.anonymousCtor
          "⟨"
          [(Algebra.Group.Defs.«term_•_» («term_⁻¹» `r "⁻¹") " • " `x)
           ","
           (Term.anonymousCtor
            "⟨"
            [`h
             ","
             (Term.byTactic
              "by"
              (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]
            "⟩")]
          "⟩"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`h]
        []
        "=>"
        (Term.anonymousCtor
         "⟨"
         [(Algebra.Group.Defs.«term_•_» («term_⁻¹» `r "⁻¹") " • " `x)
          ","
          (Term.anonymousCtor
           "⟨"
           [`h
            ","
            (Term.byTactic
             "by"
             (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]
           "⟩")]
         "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Algebra.Group.Defs.«term_•_» («term_⁻¹» `r "⁻¹") " • " `x)
        ","
        (Term.anonymousCtor
         "⟨"
         [`h
          ","
          (Term.byTactic
           "by"
           (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]
         "⟩")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`h
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))]
       "⟩")
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
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_» («term_⁻¹» `r "⁻¹") " • " `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      («term_⁻¹» `r "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 73, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.constructor "constructor")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `smul_mem_smul_iff)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `smul_mem_smul_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.nthRwSeq
       "nth_rw"
       []
       (num "1")
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `x_eq)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`x_eq []]
         [(Term.typeSpec
           ":"
           («term_=_»
            `x
            "="
            (Algebra.Group.Defs.«term_•_»
             `r
             " • "
             (Algebra.Group.Defs.«term_•_» («term_⁻¹» `r "⁻¹") " • " `x))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])]))))))
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
       `x
       "="
       (Algebra.Group.Defs.«term_•_»
        `r
        " • "
        (Algebra.Group.Defs.«term_•_» («term_⁻¹» `r "⁻¹") " • " `x)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_»
       `r
       " • "
       (Algebra.Group.Defs.«term_•_» («term_⁻¹» `r "⁻¹") " • " `x))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_» («term_⁻¹» `r "⁻¹") " • " `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      («term_⁻¹» `r "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 73 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (spectrum.Algebra.Algebra.Spectrum.termσ "σ")
        [(Algebra.Group.Defs.«term_•_» `r " • " `a)])
       "="
       (Algebra.Group.Defs.«term_•_»
        `r
        " • "
        (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [`a])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_»
       `r
       " • "
       (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [`a]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Algebra.Algebra.Spectrum.termσ "σ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Algebra.Algebra.Spectrum.termσ', expected 'spectrum.Algebra.Algebra.Spectrum.termσ._@.Algebra.Algebra.Spectrum._hyg.600'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  unit_smul_eq_smul
  ( a : A ) ( r : R ˣ ) : σ r • a = r • σ a
  :=
    by
      ext
        have x_eq : x = r • r ⁻¹ • x := by simp
        nth_rw 1 [ x_eq ]
        rw [ smul_mem_smul_iff ]
        constructor
        · exact fun h => ⟨ r ⁻¹ • x , ⟨ h , by simp ⟩ ⟩
        · rintro ⟨ _ , _ , x'_eq ⟩ simpa [ ← x'_eq ]
#align spectrum.unit_smul_eq_smul spectrum.unit_smul_eq_smul

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `unit_mem_mul_iff_mem_swap_mul [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a `b] [":" `A] "}")
        (Term.implicitBinder "{" [`r] [":" (Algebra.Group.Units.«term_ˣ» `R "ˣ")] "}")]
       (Term.typeSpec
        ":"
        («term_↔_»
         («term_∈_»
          (coeNotation "↑" `r)
          "∈"
          (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [(«term_*_» `a "*" `b)]))
         "↔"
         («term_∈_»
          (coeNotation "↑" `r)
          "∈"
          (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [(«term_*_» `b "*" `a)])))))
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
              [`h₁ []]
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [`x `y]
                 [(Term.typeSpec ":" `A)]
                 ","
                 (Term.arrow
                  (Term.app `IsUnit [(«term_-_» (num "1") "-" («term_*_» `x "*" `y))])
                  "→"
                  (Term.app `IsUnit [(«term_-_» (num "1") "-" («term_*_» `y "*" `x))]))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.refine'
                   "refine'"
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [`x `y `h]
                     []
                     "=>"
                     (Term.anonymousCtor
                      "⟨"
                      [(Term.anonymousCtor
                        "⟨"
                        [(«term_-_» (num "1") "-" («term_*_» `y "*" `x))
                         ","
                         («term_+_» (num "1") "+" («term_*_» («term_*_» `y "*" `h.unit.inv) "*" `x))
                         ","
                         (Term.hole "_")
                         ","
                         (Term.hole "_")]
                        "⟩")
                       ","
                       `rfl]
                      "⟩"))))
                  []
                  (calcTactic
                   "calc"
                   (calcStep
                    («term_=_»
                     («term_*_»
                      («term_-_» (num "1") "-" («term_*_» `y "*" `x))
                      "*"
                      («term_+_»
                       (num "1")
                       "+"
                       («term_*_»
                        («term_*_» `y "*" (Term.proj (Term.app `IsUnit.unit [`h]) "." `inv))
                        "*"
                        `x)))
                     "="
                     («term_+_»
                      («term_-_» (num "1") "-" («term_*_» `y "*" `x))
                      "+"
                      («term_*_»
                       («term_*_»
                        `y
                        "*"
                        («term_*_» («term_-_» (num "1") "-" («term_*_» `x "*" `y)) "*" `h.unit.inv))
                       "*"
                       `x)))
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented [(Tactic.noncommRing "noncomm_ring")]))))
                   [(calcStep
                     («term_=_» (Term.hole "_") "=" (num "1"))
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
                           [(Tactic.simpLemma [] [] `Units.inv_eq_val_inv)
                            ","
                            (Tactic.simpLemma [] [] `IsUnit.mul_val_inv)
                            ","
                            (Tactic.simpLemma [] [] `mul_one)
                            ","
                            (Tactic.simpLemma [] [] `sub_add_cancel)]
                           "]"]
                          [])]))))])
                  []
                  (calcTactic
                   "calc"
                   (calcStep
                    («term_=_»
                     («term_*_»
                      («term_+_»
                       (num "1")
                       "+"
                       («term_*_»
                        («term_*_» `y "*" (Term.proj (Term.app `IsUnit.unit [`h]) "." `inv))
                        "*"
                        `x))
                      "*"
                      («term_-_» (num "1") "-" («term_*_» `y "*" `x)))
                     "="
                     («term_+_»
                      («term_-_» (num "1") "-" («term_*_» `y "*" `x))
                      "+"
                      («term_*_»
                       («term_*_»
                        `y
                        "*"
                        («term_*_» `h.unit.inv "*" («term_-_» (num "1") "-" («term_*_» `x "*" `y))))
                       "*"
                       `x)))
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented [(Tactic.noncommRing "noncomm_ring")]))))
                   [(calcStep
                     («term_=_» (Term.hole "_") "=" (num "1"))
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
                           [(Tactic.simpLemma [] [] `Units.inv_eq_val_inv)
                            ","
                            (Tactic.simpLemma [] [] `IsUnit.val_inv_mul)
                            ","
                            (Tactic.simpLemma [] [] `mul_one)
                            ","
                            (Tactic.simpLemma [] [] `sub_add_cancel)]
                           "]"]
                          [])]))))])]))))))
           []
           (Std.Tactic.Simpa.simpa
            "simpa"
            []
            []
            (Std.Tactic.Simpa.simpaArgsRest
             []
             []
             ["only"]
             [(Tactic.simpArgs
               "["
               [(Tactic.simpLemma [] [] `mem_iff)
                ","
                (Tactic.simpLemma [] [] `not_iff_not)
                ","
                (Tactic.simpLemma [] [] `Algebra.algebra_map_eq_smul_one)
                ","
                (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Units.smul_def)
                ","
                (Tactic.simpLemma [] [] `IsUnit.smul_sub_iff_sub_inv_smul)
                ","
                (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `smul_mul_assoc)
                ","
                (Tactic.simpLemma
                 []
                 [(patternIgnore (token.«← » "←"))]
                 (Term.app `mul_smul_comm [(«term_⁻¹» `r "⁻¹") `b `a]))]
               "]")]
             ["using"
              (Term.app
               `Iff.intro
               [(Term.app `h₁ [(Algebra.Group.Defs.«term_•_» («term_⁻¹» `r "⁻¹") " • " `a) `b])
                (Term.app
                 `h₁
                 [`b (Algebra.Group.Defs.«term_•_» («term_⁻¹» `r "⁻¹") " • " `a)])])]))])))
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
             [`h₁ []]
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [`x `y]
                [(Term.typeSpec ":" `A)]
                ","
                (Term.arrow
                 (Term.app `IsUnit [(«term_-_» (num "1") "-" («term_*_» `x "*" `y))])
                 "→"
                 (Term.app `IsUnit [(«term_-_» (num "1") "-" («term_*_» `y "*" `x))]))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.refine'
                  "refine'"
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [`x `y `h]
                    []
                    "=>"
                    (Term.anonymousCtor
                     "⟨"
                     [(Term.anonymousCtor
                       "⟨"
                       [(«term_-_» (num "1") "-" («term_*_» `y "*" `x))
                        ","
                        («term_+_» (num "1") "+" («term_*_» («term_*_» `y "*" `h.unit.inv) "*" `x))
                        ","
                        (Term.hole "_")
                        ","
                        (Term.hole "_")]
                       "⟩")
                      ","
                      `rfl]
                     "⟩"))))
                 []
                 (calcTactic
                  "calc"
                  (calcStep
                   («term_=_»
                    («term_*_»
                     («term_-_» (num "1") "-" («term_*_» `y "*" `x))
                     "*"
                     («term_+_»
                      (num "1")
                      "+"
                      («term_*_»
                       («term_*_» `y "*" (Term.proj (Term.app `IsUnit.unit [`h]) "." `inv))
                       "*"
                       `x)))
                    "="
                    («term_+_»
                     («term_-_» (num "1") "-" («term_*_» `y "*" `x))
                     "+"
                     («term_*_»
                      («term_*_»
                       `y
                       "*"
                       («term_*_» («term_-_» (num "1") "-" («term_*_» `x "*" `y)) "*" `h.unit.inv))
                      "*"
                      `x)))
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented [(Tactic.noncommRing "noncomm_ring")]))))
                  [(calcStep
                    («term_=_» (Term.hole "_") "=" (num "1"))
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
                          [(Tactic.simpLemma [] [] `Units.inv_eq_val_inv)
                           ","
                           (Tactic.simpLemma [] [] `IsUnit.mul_val_inv)
                           ","
                           (Tactic.simpLemma [] [] `mul_one)
                           ","
                           (Tactic.simpLemma [] [] `sub_add_cancel)]
                          "]"]
                         [])]))))])
                 []
                 (calcTactic
                  "calc"
                  (calcStep
                   («term_=_»
                    («term_*_»
                     («term_+_»
                      (num "1")
                      "+"
                      («term_*_»
                       («term_*_» `y "*" (Term.proj (Term.app `IsUnit.unit [`h]) "." `inv))
                       "*"
                       `x))
                     "*"
                     («term_-_» (num "1") "-" («term_*_» `y "*" `x)))
                    "="
                    («term_+_»
                     («term_-_» (num "1") "-" («term_*_» `y "*" `x))
                     "+"
                     («term_*_»
                      («term_*_»
                       `y
                       "*"
                       («term_*_» `h.unit.inv "*" («term_-_» (num "1") "-" («term_*_» `x "*" `y))))
                      "*"
                      `x)))
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented [(Tactic.noncommRing "noncomm_ring")]))))
                  [(calcStep
                    («term_=_» (Term.hole "_") "=" (num "1"))
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
                          [(Tactic.simpLemma [] [] `Units.inv_eq_val_inv)
                           ","
                           (Tactic.simpLemma [] [] `IsUnit.val_inv_mul)
                           ","
                           (Tactic.simpLemma [] [] `mul_one)
                           ","
                           (Tactic.simpLemma [] [] `sub_add_cancel)]
                          "]"]
                         [])]))))])]))))))
          []
          (Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            ["only"]
            [(Tactic.simpArgs
              "["
              [(Tactic.simpLemma [] [] `mem_iff)
               ","
               (Tactic.simpLemma [] [] `not_iff_not)
               ","
               (Tactic.simpLemma [] [] `Algebra.algebra_map_eq_smul_one)
               ","
               (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Units.smul_def)
               ","
               (Tactic.simpLemma [] [] `IsUnit.smul_sub_iff_sub_inv_smul)
               ","
               (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `smul_mul_assoc)
               ","
               (Tactic.simpLemma
                []
                [(patternIgnore (token.«← » "←"))]
                (Term.app `mul_smul_comm [(«term_⁻¹» `r "⁻¹") `b `a]))]
              "]")]
            ["using"
             (Term.app
              `Iff.intro
              [(Term.app `h₁ [(Algebra.Group.Defs.«term_•_» («term_⁻¹» `r "⁻¹") " • " `a) `b])
               (Term.app
                `h₁
                [`b (Algebra.Group.Defs.«term_•_» («term_⁻¹» `r "⁻¹") " • " `a)])])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        ["only"]
        [(Tactic.simpArgs
          "["
          [(Tactic.simpLemma [] [] `mem_iff)
           ","
           (Tactic.simpLemma [] [] `not_iff_not)
           ","
           (Tactic.simpLemma [] [] `Algebra.algebra_map_eq_smul_one)
           ","
           (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Units.smul_def)
           ","
           (Tactic.simpLemma [] [] `IsUnit.smul_sub_iff_sub_inv_smul)
           ","
           (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `smul_mul_assoc)
           ","
           (Tactic.simpLemma
            []
            [(patternIgnore (token.«← » "←"))]
            (Term.app `mul_smul_comm [(«term_⁻¹» `r "⁻¹") `b `a]))]
          "]")]
        ["using"
         (Term.app
          `Iff.intro
          [(Term.app `h₁ [(Algebra.Group.Defs.«term_•_» («term_⁻¹» `r "⁻¹") " • " `a) `b])
           (Term.app `h₁ [`b (Algebra.Group.Defs.«term_•_» («term_⁻¹» `r "⁻¹") " • " `a)])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Iff.intro
       [(Term.app `h₁ [(Algebra.Group.Defs.«term_•_» («term_⁻¹» `r "⁻¹") " • " `a) `b])
        (Term.app `h₁ [`b (Algebra.Group.Defs.«term_•_» («term_⁻¹» `r "⁻¹") " • " `a)])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h₁ [`b (Algebra.Group.Defs.«term_•_» («term_⁻¹» `r "⁻¹") " • " `a)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_» («term_⁻¹» `r "⁻¹") " • " `a)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      («term_⁻¹» `r "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Group.Defs.«term_•_» («term_⁻¹» `r "⁻¹") " • " `a)
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `h₁
      [`b (Term.paren "(" (Algebra.Group.Defs.«term_•_» («term_⁻¹» `r "⁻¹") " • " `a) ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `h₁ [(Algebra.Group.Defs.«term_•_» («term_⁻¹» `r "⁻¹") " • " `a) `b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Algebra.Group.Defs.«term_•_» («term_⁻¹» `r "⁻¹") " • " `a)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      («term_⁻¹» `r "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 73, (some 73, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Group.Defs.«term_•_» («term_⁻¹» `r "⁻¹") " • " `a)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `h₁
      [(Term.paren "(" (Algebra.Group.Defs.«term_•_» («term_⁻¹» `r "⁻¹") " • " `a) ")") `b])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Iff.intro
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_smul_comm [(«term_⁻¹» `r "⁻¹") `b `a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_⁻¹»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_⁻¹»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_⁻¹» `r "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_smul_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `smul_mul_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `IsUnit.smul_sub_iff_sub_inv_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Units.smul_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Algebra.algebra_map_eq_smul_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `not_iff_not
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`h₁ []]
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            [`x `y]
            [(Term.typeSpec ":" `A)]
            ","
            (Term.arrow
             (Term.app `IsUnit [(«term_-_» (num "1") "-" («term_*_» `x "*" `y))])
             "→"
             (Term.app `IsUnit [(«term_-_» (num "1") "-" («term_*_» `y "*" `x))]))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.refine'
              "refine'"
              (Term.fun
               "fun"
               (Term.basicFun
                [`x `y `h]
                []
                "=>"
                (Term.anonymousCtor
                 "⟨"
                 [(Term.anonymousCtor
                   "⟨"
                   [(«term_-_» (num "1") "-" («term_*_» `y "*" `x))
                    ","
                    («term_+_» (num "1") "+" («term_*_» («term_*_» `y "*" `h.unit.inv) "*" `x))
                    ","
                    (Term.hole "_")
                    ","
                    (Term.hole "_")]
                   "⟩")
                  ","
                  `rfl]
                 "⟩"))))
             []
             (calcTactic
              "calc"
              (calcStep
               («term_=_»
                («term_*_»
                 («term_-_» (num "1") "-" («term_*_» `y "*" `x))
                 "*"
                 («term_+_»
                  (num "1")
                  "+"
                  («term_*_»
                   («term_*_» `y "*" (Term.proj (Term.app `IsUnit.unit [`h]) "." `inv))
                   "*"
                   `x)))
                "="
                («term_+_»
                 («term_-_» (num "1") "-" («term_*_» `y "*" `x))
                 "+"
                 («term_*_»
                  («term_*_»
                   `y
                   "*"
                   («term_*_» («term_-_» (num "1") "-" («term_*_» `x "*" `y)) "*" `h.unit.inv))
                  "*"
                  `x)))
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented [(Tactic.noncommRing "noncomm_ring")]))))
              [(calcStep
                («term_=_» (Term.hole "_") "=" (num "1"))
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
                      [(Tactic.simpLemma [] [] `Units.inv_eq_val_inv)
                       ","
                       (Tactic.simpLemma [] [] `IsUnit.mul_val_inv)
                       ","
                       (Tactic.simpLemma [] [] `mul_one)
                       ","
                       (Tactic.simpLemma [] [] `sub_add_cancel)]
                      "]"]
                     [])]))))])
             []
             (calcTactic
              "calc"
              (calcStep
               («term_=_»
                («term_*_»
                 («term_+_»
                  (num "1")
                  "+"
                  («term_*_»
                   («term_*_» `y "*" (Term.proj (Term.app `IsUnit.unit [`h]) "." `inv))
                   "*"
                   `x))
                 "*"
                 («term_-_» (num "1") "-" («term_*_» `y "*" `x)))
                "="
                («term_+_»
                 («term_-_» (num "1") "-" («term_*_» `y "*" `x))
                 "+"
                 («term_*_»
                  («term_*_»
                   `y
                   "*"
                   («term_*_» `h.unit.inv "*" («term_-_» (num "1") "-" («term_*_» `x "*" `y))))
                  "*"
                  `x)))
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented [(Tactic.noncommRing "noncomm_ring")]))))
              [(calcStep
                («term_=_» (Term.hole "_") "=" (num "1"))
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
                      [(Tactic.simpLemma [] [] `Units.inv_eq_val_inv)
                       ","
                       (Tactic.simpLemma [] [] `IsUnit.val_inv_mul)
                       ","
                       (Tactic.simpLemma [] [] `mul_one)
                       ","
                       (Tactic.simpLemma [] [] `sub_add_cancel)]
                      "]"]
                     [])]))))])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.refine'
           "refine'"
           (Term.fun
            "fun"
            (Term.basicFun
             [`x `y `h]
             []
             "=>"
             (Term.anonymousCtor
              "⟨"
              [(Term.anonymousCtor
                "⟨"
                [(«term_-_» (num "1") "-" («term_*_» `y "*" `x))
                 ","
                 («term_+_» (num "1") "+" («term_*_» («term_*_» `y "*" `h.unit.inv) "*" `x))
                 ","
                 (Term.hole "_")
                 ","
                 (Term.hole "_")]
                "⟩")
               ","
               `rfl]
              "⟩"))))
          []
          (calcTactic
           "calc"
           (calcStep
            («term_=_»
             («term_*_»
              («term_-_» (num "1") "-" («term_*_» `y "*" `x))
              "*"
              («term_+_»
               (num "1")
               "+"
               («term_*_»
                («term_*_» `y "*" (Term.proj (Term.app `IsUnit.unit [`h]) "." `inv))
                "*"
                `x)))
             "="
             («term_+_»
              («term_-_» (num "1") "-" («term_*_» `y "*" `x))
              "+"
              («term_*_»
               («term_*_»
                `y
                "*"
                («term_*_» («term_-_» (num "1") "-" («term_*_» `x "*" `y)) "*" `h.unit.inv))
               "*"
               `x)))
            ":="
            (Term.byTactic
             "by"
             (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.noncommRing "noncomm_ring")]))))
           [(calcStep
             («term_=_» (Term.hole "_") "=" (num "1"))
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
                   [(Tactic.simpLemma [] [] `Units.inv_eq_val_inv)
                    ","
                    (Tactic.simpLemma [] [] `IsUnit.mul_val_inv)
                    ","
                    (Tactic.simpLemma [] [] `mul_one)
                    ","
                    (Tactic.simpLemma [] [] `sub_add_cancel)]
                   "]"]
                  [])]))))])
          []
          (calcTactic
           "calc"
           (calcStep
            («term_=_»
             («term_*_»
              («term_+_»
               (num "1")
               "+"
               («term_*_»
                («term_*_» `y "*" (Term.proj (Term.app `IsUnit.unit [`h]) "." `inv))
                "*"
                `x))
              "*"
              («term_-_» (num "1") "-" («term_*_» `y "*" `x)))
             "="
             («term_+_»
              («term_-_» (num "1") "-" («term_*_» `y "*" `x))
              "+"
              («term_*_»
               («term_*_»
                `y
                "*"
                («term_*_» `h.unit.inv "*" («term_-_» (num "1") "-" («term_*_» `x "*" `y))))
               "*"
               `x)))
            ":="
            (Term.byTactic
             "by"
             (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.noncommRing "noncomm_ring")]))))
           [(calcStep
             («term_=_» (Term.hole "_") "=" (num "1"))
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
                   [(Tactic.simpLemma [] [] `Units.inv_eq_val_inv)
                    ","
                    (Tactic.simpLemma [] [] `IsUnit.val_inv_mul)
                    ","
                    (Tactic.simpLemma [] [] `mul_one)
                    ","
                    (Tactic.simpLemma [] [] `sub_add_cancel)]
                   "]"]
                  [])]))))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_=_»
         («term_*_»
          («term_+_»
           (num "1")
           "+"
           («term_*_» («term_*_» `y "*" (Term.proj (Term.app `IsUnit.unit [`h]) "." `inv)) "*" `x))
          "*"
          («term_-_» (num "1") "-" («term_*_» `y "*" `x)))
         "="
         («term_+_»
          («term_-_» (num "1") "-" («term_*_» `y "*" `x))
          "+"
          («term_*_»
           («term_*_»
            `y
            "*"
            («term_*_» `h.unit.inv "*" («term_-_» (num "1") "-" («term_*_» `x "*" `y))))
           "*"
           `x)))
        ":="
        (Term.byTactic
         "by"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.noncommRing "noncomm_ring")]))))
       [(calcStep
         («term_=_» (Term.hole "_") "=" (num "1"))
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
               [(Tactic.simpLemma [] [] `Units.inv_eq_val_inv)
                ","
                (Tactic.simpLemma [] [] `IsUnit.val_inv_mul)
                ","
                (Tactic.simpLemma [] [] `mul_one)
                ","
                (Tactic.simpLemma [] [] `sub_add_cancel)]
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
            [(Tactic.simpLemma [] [] `Units.inv_eq_val_inv)
             ","
             (Tactic.simpLemma [] [] `IsUnit.val_inv_mul)
             ","
             (Tactic.simpLemma [] [] `mul_one)
             ","
             (Tactic.simpLemma [] [] `sub_add_cancel)]
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
        [(Tactic.simpLemma [] [] `Units.inv_eq_val_inv)
         ","
         (Tactic.simpLemma [] [] `IsUnit.val_inv_mul)
         ","
         (Tactic.simpLemma [] [] `mul_one)
         ","
         (Tactic.simpLemma [] [] `sub_add_cancel)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_add_cancel
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
      `IsUnit.val_inv_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Units.inv_eq_val_inv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.hole "_") "=" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.noncommRing "noncomm_ring")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.noncommRing "noncomm_ring")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       («term_*_»
        («term_+_»
         (num "1")
         "+"
         («term_*_» («term_*_» `y "*" (Term.proj (Term.app `IsUnit.unit [`h]) "." `inv)) "*" `x))
        "*"
        («term_-_» (num "1") "-" («term_*_» `y "*" `x)))
       "="
       («term_+_»
        («term_-_» (num "1") "-" («term_*_» `y "*" `x))
        "+"
        («term_*_»
         («term_*_»
          `y
          "*"
          («term_*_» `h.unit.inv "*" («term_-_» (num "1") "-" («term_*_» `x "*" `y))))
         "*"
         `x)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       («term_-_» (num "1") "-" («term_*_» `y "*" `x))
       "+"
       («term_*_»
        («term_*_»
         `y
         "*"
         («term_*_» `h.unit.inv "*" («term_-_» (num "1") "-" («term_*_» `x "*" `y))))
        "*"
        `x))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_*_»
        `y
        "*"
        («term_*_» `h.unit.inv "*" («term_-_» (num "1") "-" («term_*_» `x "*" `y))))
       "*"
       `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_*_» `y "*" («term_*_» `h.unit.inv "*" («term_-_» (num "1") "-" («term_*_» `x "*" `y))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `h.unit.inv "*" («term_-_» (num "1") "-" («term_*_» `x "*" `y)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» (num "1") "-" («term_*_» `x "*" `y))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `x "*" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_-_» (num "1") "-" («term_*_» `x "*" `y))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `h.unit.inv
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_*_»
      `h.unit.inv
      "*"
      (Term.paren "(" («term_-_» (num "1") "-" («term_*_» `x "*" `y)) ")"))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_-_» (num "1") "-" («term_*_» `y "*" `x))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `y "*" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 65, (some 66, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_*_»
       («term_+_»
        (num "1")
        "+"
        («term_*_» («term_*_» `y "*" (Term.proj (Term.app `IsUnit.unit [`h]) "." `inv)) "*" `x))
       "*"
       («term_-_» (num "1") "-" («term_*_» `y "*" `x)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» (num "1") "-" («term_*_» `y "*" `x))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `y "*" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_-_» (num "1") "-" («term_*_» `y "*" `x))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_+_»
       (num "1")
       "+"
       («term_*_» («term_*_» `y "*" (Term.proj (Term.app `IsUnit.unit [`h]) "." `inv)) "*" `x))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» («term_*_» `y "*" (Term.proj (Term.app `IsUnit.unit [`h]) "." `inv)) "*" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_*_» `y "*" (Term.proj (Term.app `IsUnit.unit [`h]) "." `inv))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `IsUnit.unit [`h]) "." `inv)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `IsUnit.unit [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsUnit.unit
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `IsUnit.unit [`h]) ")")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 65, (some 66, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_+_»
      (num "1")
      "+"
      («term_*_»
       («term_*_» `y "*" (Term.proj (Term.paren "(" (Term.app `IsUnit.unit [`h]) ")") "." `inv))
       "*"
       `x))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_=_»
         («term_*_»
          («term_-_» (num "1") "-" («term_*_» `y "*" `x))
          "*"
          («term_+_»
           (num "1")
           "+"
           («term_*_» («term_*_» `y "*" (Term.proj (Term.app `IsUnit.unit [`h]) "." `inv)) "*" `x)))
         "="
         («term_+_»
          («term_-_» (num "1") "-" («term_*_» `y "*" `x))
          "+"
          («term_*_»
           («term_*_»
            `y
            "*"
            («term_*_» («term_-_» (num "1") "-" («term_*_» `x "*" `y)) "*" `h.unit.inv))
           "*"
           `x)))
        ":="
        (Term.byTactic
         "by"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.noncommRing "noncomm_ring")]))))
       [(calcStep
         («term_=_» (Term.hole "_") "=" (num "1"))
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
               [(Tactic.simpLemma [] [] `Units.inv_eq_val_inv)
                ","
                (Tactic.simpLemma [] [] `IsUnit.mul_val_inv)
                ","
                (Tactic.simpLemma [] [] `mul_one)
                ","
                (Tactic.simpLemma [] [] `sub_add_cancel)]
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
            [(Tactic.simpLemma [] [] `Units.inv_eq_val_inv)
             ","
             (Tactic.simpLemma [] [] `IsUnit.mul_val_inv)
             ","
             (Tactic.simpLemma [] [] `mul_one)
             ","
             (Tactic.simpLemma [] [] `sub_add_cancel)]
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
        [(Tactic.simpLemma [] [] `Units.inv_eq_val_inv)
         ","
         (Tactic.simpLemma [] [] `IsUnit.mul_val_inv)
         ","
         (Tactic.simpLemma [] [] `mul_one)
         ","
         (Tactic.simpLemma [] [] `sub_add_cancel)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_add_cancel
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
      `IsUnit.mul_val_inv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Units.inv_eq_val_inv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.hole "_") "=" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.noncommRing "noncomm_ring")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.noncommRing "noncomm_ring")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       («term_*_»
        («term_-_» (num "1") "-" («term_*_» `y "*" `x))
        "*"
        («term_+_»
         (num "1")
         "+"
         («term_*_» («term_*_» `y "*" (Term.proj (Term.app `IsUnit.unit [`h]) "." `inv)) "*" `x)))
       "="
       («term_+_»
        («term_-_» (num "1") "-" («term_*_» `y "*" `x))
        "+"
        («term_*_»
         («term_*_»
          `y
          "*"
          («term_*_» («term_-_» (num "1") "-" («term_*_» `x "*" `y)) "*" `h.unit.inv))
         "*"
         `x)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       («term_-_» (num "1") "-" («term_*_» `y "*" `x))
       "+"
       («term_*_»
        («term_*_»
         `y
         "*"
         («term_*_» («term_-_» (num "1") "-" («term_*_» `x "*" `y)) "*" `h.unit.inv))
        "*"
        `x))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_*_»
        `y
        "*"
        («term_*_» («term_-_» (num "1") "-" («term_*_» `x "*" `y)) "*" `h.unit.inv))
       "*"
       `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_*_» `y "*" («term_*_» («term_-_» (num "1") "-" («term_*_» `x "*" `y)) "*" `h.unit.inv))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» («term_-_» (num "1") "-" («term_*_» `x "*" `y)) "*" `h.unit.inv)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h.unit.inv
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_-_» (num "1") "-" («term_*_» `x "*" `y))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `x "*" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 65, (some 66, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_-_» (num "1") "-" («term_*_» `x "*" `y))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_*_»
      (Term.paren "(" («term_-_» (num "1") "-" («term_*_» `x "*" `y)) ")")
      "*"
      `h.unit.inv)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_-_» (num "1") "-" («term_*_» `y "*" `x))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `y "*" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 65, (some 66, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_*_»
       («term_-_» (num "1") "-" («term_*_» `y "*" `x))
       "*"
       («term_+_»
        (num "1")
        "+"
        («term_*_» («term_*_» `y "*" (Term.proj (Term.app `IsUnit.unit [`h]) "." `inv)) "*" `x)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       (num "1")
       "+"
       («term_*_» («term_*_» `y "*" (Term.proj (Term.app `IsUnit.unit [`h]) "." `inv)) "*" `x))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» («term_*_» `y "*" (Term.proj (Term.app `IsUnit.unit [`h]) "." `inv)) "*" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_*_» `y "*" (Term.proj (Term.app `IsUnit.unit [`h]) "." `inv))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `IsUnit.unit [`h]) "." `inv)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `IsUnit.unit [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsUnit.unit
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `IsUnit.unit [`h]) ")")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_+_»
      (num "1")
      "+"
      («term_*_»
       («term_*_» `y "*" (Term.proj (Term.paren "(" (Term.app `IsUnit.unit [`h]) ")") "." `inv))
       "*"
       `x))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_-_» (num "1") "-" («term_*_» `y "*" `x))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `y "*" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 65, (some 66, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_-_» (num "1") "-" («term_*_» `y "*" `x))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.fun
        "fun"
        (Term.basicFun
         [`x `y `h]
         []
         "=>"
         (Term.anonymousCtor
          "⟨"
          [(Term.anonymousCtor
            "⟨"
            [(«term_-_» (num "1") "-" («term_*_» `y "*" `x))
             ","
             («term_+_» (num "1") "+" («term_*_» («term_*_» `y "*" `h.unit.inv) "*" `x))
             ","
             (Term.hole "_")
             ","
             (Term.hole "_")]
            "⟩")
           ","
           `rfl]
          "⟩"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x `y `h]
        []
        "=>"
        (Term.anonymousCtor
         "⟨"
         [(Term.anonymousCtor
           "⟨"
           [(«term_-_» (num "1") "-" («term_*_» `y "*" `x))
            ","
            («term_+_» (num "1") "+" («term_*_» («term_*_» `y "*" `h.unit.inv) "*" `x))
            ","
            (Term.hole "_")
            ","
            (Term.hole "_")]
           "⟩")
          ","
          `rfl]
         "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.anonymousCtor
         "⟨"
         [(«term_-_» (num "1") "-" («term_*_» `y "*" `x))
          ","
          («term_+_» (num "1") "+" («term_*_» («term_*_» `y "*" `h.unit.inv) "*" `x))
          ","
          (Term.hole "_")
          ","
          (Term.hole "_")]
         "⟩")
        ","
        `rfl]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(«term_-_» (num "1") "-" («term_*_» `y "*" `x))
        ","
        («term_+_» (num "1") "+" («term_*_» («term_*_» `y "*" `h.unit.inv) "*" `x))
        ","
        (Term.hole "_")
        ","
        (Term.hole "_")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» (num "1") "+" («term_*_» («term_*_» `y "*" `h.unit.inv) "*" `x))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» («term_*_» `y "*" `h.unit.inv) "*" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_*_» `y "*" `h.unit.inv)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h.unit.inv
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» (num "1") "-" («term_*_» `y "*" `x))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `y "*" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`x `y]
       [(Term.typeSpec ":" `A)]
       ","
       (Term.arrow
        (Term.app `IsUnit [(«term_-_» (num "1") "-" («term_*_» `x "*" `y))])
        "→"
        (Term.app `IsUnit [(«term_-_» (num "1") "-" («term_*_» `y "*" `x))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       (Term.app `IsUnit [(«term_-_» (num "1") "-" («term_*_» `x "*" `y))])
       "→"
       (Term.app `IsUnit [(«term_-_» (num "1") "-" («term_*_» `y "*" `x))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsUnit [(«term_-_» (num "1") "-" («term_*_» `y "*" `x))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» (num "1") "-" («term_*_» `y "*" `x))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `y "*" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_-_» (num "1") "-" («term_*_» `y "*" `x))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsUnit
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app `IsUnit [(«term_-_» (num "1") "-" («term_*_» `x "*" `y))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» (num "1") "-" («term_*_» `x "*" `y))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `x "*" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_-_» (num "1") "-" («term_*_» `x "*" `y))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsUnit
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_↔_»
       («term_∈_»
        (coeNotation "↑" `r)
        "∈"
        (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [(«term_*_» `a "*" `b)]))
       "↔"
       («term_∈_»
        (coeNotation "↑" `r)
        "∈"
        (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [(«term_*_» `b "*" `a)])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_»
       (coeNotation "↑" `r)
       "∈"
       (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [(«term_*_» `b "*" `a)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [(«term_*_» `b "*" `a)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `b "*" `a)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_*_» `b "*" `a) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Algebra.Algebra.Spectrum.termσ "σ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Algebra.Algebra.Spectrum.termσ', expected 'spectrum.Algebra.Algebra.Spectrum.termσ._@.Algebra.Algebra.Spectrum._hyg.600'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  unit_mem_mul_iff_mem_swap_mul
  { a b : A } { r : R ˣ } : ↑ r ∈ σ a * b ↔ ↑ r ∈ σ b * a
  :=
    by
      have
          h₁
            : ∀ x y : A , IsUnit 1 - x * y → IsUnit 1 - y * x
            :=
            by
              refine' fun x y h => ⟨ ⟨ 1 - y * x , 1 + y * h.unit.inv * x , _ , _ ⟩ , rfl ⟩
                calc
                  1 - y * x * 1 + y * IsUnit.unit h . inv * x
                      =
                      1 - y * x + y * 1 - x * y * h.unit.inv * x
                    :=
                    by noncomm_ring
                  _ = 1
                    :=
                    by
                      simp
                        only
                        [ Units.inv_eq_val_inv , IsUnit.mul_val_inv , mul_one , sub_add_cancel ]
                calc
                  1 + y * IsUnit.unit h . inv * x * 1 - y * x
                      =
                      1 - y * x + y * h.unit.inv * 1 - x * y * x
                    :=
                    by noncomm_ring
                  _ = 1
                    :=
                    by
                      simp
                        only
                        [ Units.inv_eq_val_inv , IsUnit.val_inv_mul , mul_one , sub_add_cancel ]
        simpa
          only
            [
              mem_iff
                ,
                not_iff_not
                ,
                Algebra.algebra_map_eq_smul_one
                ,
                ← Units.smul_def
                ,
                IsUnit.smul_sub_iff_sub_inv_smul
                ,
                ← smul_mul_assoc
                ,
                ← mul_smul_comm r ⁻¹ b a
              ]
            using Iff.intro h₁ r ⁻¹ • a b h₁ b r ⁻¹ • a
#align spectrum.unit_mem_mul_iff_mem_swap_mul spectrum.unit_mem_mul_iff_mem_swap_mul

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `preimage_units_mul_eq_swap_mul [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a `b] [":" `A] "}")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Set.Data.Set.Image.«term_⁻¹'_»
          (Term.typeAscription
           "("
           `coe
           ":"
           [(Term.arrow (Algebra.Group.Units.«term_ˣ» `R "ˣ") "→" `R)]
           ")")
          " ⁻¹' "
          (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [(«term_*_» `a "*" `b)]))
         "="
         (Set.Data.Set.Image.«term_⁻¹'_»
          `coe
          " ⁻¹' "
          (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [(«term_*_» `b "*" `a)])))))
      (Command.declValSimple
       ":="
       (Term.app
        `Set.ext
        [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `unit_mem_mul_iff_mem_swap_mul))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Set.ext
       [(Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `unit_mem_mul_iff_mem_swap_mul))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `unit_mem_mul_iff_mem_swap_mul))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `unit_mem_mul_iff_mem_swap_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Set.ext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Set.Data.Set.Image.«term_⁻¹'_»
        (Term.typeAscription
         "("
         `coe
         ":"
         [(Term.arrow (Algebra.Group.Units.«term_ˣ» `R "ˣ") "→" `R)]
         ")")
        " ⁻¹' "
        (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [(«term_*_» `a "*" `b)]))
       "="
       (Set.Data.Set.Image.«term_⁻¹'_»
        `coe
        " ⁻¹' "
        (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [(«term_*_» `b "*" `a)])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Data.Set.Image.«term_⁻¹'_»
       `coe
       " ⁻¹' "
       (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [(«term_*_» `b "*" `a)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [(«term_*_» `b "*" `a)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `b "*" `a)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_*_» `b "*" `a) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Algebra.Algebra.Spectrum.termσ "σ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Algebra.Algebra.Spectrum.termσ', expected 'spectrum.Algebra.Algebra.Spectrum.termσ._@.Algebra.Algebra.Spectrum._hyg.600'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  preimage_units_mul_eq_swap_mul
  { a b : A } : ( coe : R ˣ → R ) ⁻¹' σ a * b = coe ⁻¹' σ b * a
  := Set.ext fun _ => unit_mem_mul_iff_mem_swap_mul
#align spectrum.preimage_units_mul_eq_swap_mul spectrum.preimage_units_mul_eq_swap_mul

section Star

variable [HasInvolutiveStar R] [StarRing A] [StarModule R A]

theorem star_mem_resolvent_set_iff {r : R} {a : A} :
    star r ∈ resolventSet R a ↔ r ∈ resolventSet R (star a) := by
  refine' ⟨fun h => _, fun h => _⟩ <;>
    simpa only [mem_resolvent_set_iff, Algebra.algebra_map_eq_smul_one, star_sub, star_smul,
      star_star, star_one] using IsUnit.star h
#align spectrum.star_mem_resolvent_set_iff spectrum.star_mem_resolvent_set_iff

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `map_star [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" `A] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [(Term.app `star [`a])])
         "="
         (Term.app `star [(Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [`a])]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
           []
           (Std.Tactic.Simpa.simpa
            "simpa"
            []
            []
            (Std.Tactic.Simpa.simpaArgsRest
             []
             []
             ["only"]
             [(Tactic.simpArgs
               "["
               [(Tactic.simpLemma [] [] `Set.mem_star)
                ","
                (Tactic.simpLemma [] [] `mem_iff)
                ","
                (Tactic.simpLemma [] [] `not_iff_not)]
               "]")]
             ["using" `star_mem_resolvent_set_iff.symm]))])))
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
         [(Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
          []
          (Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            ["only"]
            [(Tactic.simpArgs
              "["
              [(Tactic.simpLemma [] [] `Set.mem_star)
               ","
               (Tactic.simpLemma [] [] `mem_iff)
               ","
               (Tactic.simpLemma [] [] `not_iff_not)]
              "]")]
            ["using" `star_mem_resolvent_set_iff.symm]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        ["only"]
        [(Tactic.simpArgs
          "["
          [(Tactic.simpLemma [] [] `Set.mem_star)
           ","
           (Tactic.simpLemma [] [] `mem_iff)
           ","
           (Tactic.simpLemma [] [] `not_iff_not)]
          "]")]
        ["using" `star_mem_resolvent_set_iff.symm]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `star_mem_resolvent_set_iff.symm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `not_iff_not
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.mem_star
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [(Term.app `star [`a])])
       "="
       (Term.app `star [(Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [`a])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `star [(Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [`a])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ "σ") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Algebra.Algebra.Spectrum.termσ "σ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Algebra.Algebra.Spectrum.termσ', expected 'spectrum.Algebra.Algebra.Spectrum.termσ._@.Algebra.Algebra.Spectrum._hyg.600'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected
  theorem
    map_star
    ( a : A ) : σ star a = star σ a
    :=
      by
        ext
          simpa only [ Set.mem_star , mem_iff , not_iff_not ] using star_mem_resolvent_set_iff.symm
#align spectrum.map_star spectrum.map_star

end Star

end ScalarSemiring

section ScalarRing

variable {R : Type u} {A : Type v}

variable [CommRing R] [Ring A] [Algebra R A]

-- mathport name: exprσ
local notation "σ" => spectrum R

-- mathport name: «expr↑ₐ»
local notation "↑ₐ" => algebraMap R A

-- it would be nice to state this for `subalgebra_class`, but we don't have such a thing yet
theorem subset_subalgebra {S : Subalgebra R A} (a : S) : spectrum R (a : A) ⊆ spectrum R a :=
  compl_subset_compl.2 fun _ => IsUnit.map S.val
#align spectrum.subset_subalgebra spectrum.subset_subalgebra

-- this is why it would be nice if `subset_subalgebra` was registered for `subalgebra_class`.
theorem subset_star_subalgebra [StarRing R] [StarRing A] [StarModule R A] {S : StarSubalgebra R A}
    (a : S) : spectrum R (a : A) ⊆ spectrum R a :=
  compl_subset_compl.2 fun _ => IsUnit.map S.Subtype
#align spectrum.subset_star_subalgebra spectrum.subset_star_subalgebra

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `singleton_add_eq [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" `A] [] ")")
        (Term.explicitBinder "(" [`r] [":" `R] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_+_»
          («term{_}» "{" [`r] "}")
          "+"
          (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ") [`a]))
         "="
         (Term.app
          (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ")
          [(«term_+_»
            (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_1» "↑ₐ") [`r])
            "+"
            `a)]))))
      (Command.declValSimple
       ":="
       (Term.app
        `ext
        [(Term.fun
          "fun"
          (Term.basicFun
           [`x]
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
                 [(Tactic.rwRule [] `singleton_add)
                  ","
                  (Tactic.rwRule [] `image_add_left)
                  ","
                  (Tactic.rwRule [] `mem_preimage)
                  ","
                  (Tactic.rwRule [] `add_comm)
                  ","
                  (Tactic.rwRule [] `add_mem_iff)
                  ","
                  (Tactic.rwRule [] `map_neg)
                  ","
                  (Tactic.rwRule [] `neg_neg)]
                 "]")
                [])])))))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `ext
       [(Term.fun
         "fun"
         (Term.basicFun
          [`x]
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
                [(Tactic.rwRule [] `singleton_add)
                 ","
                 (Tactic.rwRule [] `image_add_left)
                 ","
                 (Tactic.rwRule [] `mem_preimage)
                 ","
                 (Tactic.rwRule [] `add_comm)
                 ","
                 (Tactic.rwRule [] `add_mem_iff)
                 ","
                 (Tactic.rwRule [] `map_neg)
                 ","
                 (Tactic.rwRule [] `neg_neg)]
                "]")
               [])])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
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
              [(Tactic.rwRule [] `singleton_add)
               ","
               (Tactic.rwRule [] `image_add_left)
               ","
               (Tactic.rwRule [] `mem_preimage)
               ","
               (Tactic.rwRule [] `add_comm)
               ","
               (Tactic.rwRule [] `add_mem_iff)
               ","
               (Tactic.rwRule [] `map_neg)
               ","
               (Tactic.rwRule [] `neg_neg)]
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
            [(Tactic.rwRule [] `singleton_add)
             ","
             (Tactic.rwRule [] `image_add_left)
             ","
             (Tactic.rwRule [] `mem_preimage)
             ","
             (Tactic.rwRule [] `add_comm)
             ","
             (Tactic.rwRule [] `add_mem_iff)
             ","
             (Tactic.rwRule [] `map_neg)
             ","
             (Tactic.rwRule [] `neg_neg)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `singleton_add)
         ","
         (Tactic.rwRule [] `image_add_left)
         ","
         (Tactic.rwRule [] `mem_preimage)
         ","
         (Tactic.rwRule [] `add_comm)
         ","
         (Tactic.rwRule [] `add_mem_iff)
         ","
         (Tactic.rwRule [] `map_neg)
         ","
         (Tactic.rwRule [] `neg_neg)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `neg_neg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_neg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_mem_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_preimage
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `image_add_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `singleton_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       («term_+_»
        («term{_}» "{" [`r] "}")
        "+"
        (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ") [`a]))
       "="
       (Term.app
        (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ")
        [(«term_+_» (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_1» "↑ₐ") [`r]) "+" `a)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ")
       [(«term_+_» (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_1» "↑ₐ") [`r]) "+" `a)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_1» "↑ₐ") [`r]) "+" `a)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_1» "↑ₐ") [`r])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_1» "↑ₐ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_1»', expected 'spectrum.Algebra.Algebra.Spectrum.term↑ₐ_1._@.Algebra.Algebra.Spectrum._hyg.2176'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  singleton_add_eq
  ( a : A ) ( r : R ) : { r } + σ a = σ ↑ₐ r + a
  :=
    ext
      fun
        x
          =>
          by
            rw
              [
                singleton_add
                  ,
                  image_add_left
                  ,
                  mem_preimage
                  ,
                  add_comm
                  ,
                  add_mem_iff
                  ,
                  map_neg
                  ,
                  neg_neg
                ]
#align spectrum.singleton_add_eq spectrum.singleton_add_eq

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `add_singleton_eq [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" `A] [] ")")
        (Term.explicitBinder "(" [`r] [":" `R] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_+_»
          (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ") [`a])
          "+"
          («term{_}» "{" [`r] "}"))
         "="
         (Term.app
          (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ")
          [(«term_+_»
            `a
            "+"
            (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_1» "↑ₐ") [`r]))]))))
      (Command.declValSimple
       ":="
       (Term.subst
        (Term.app
         `add_comm
         [(«term{_}» "{" [`r] "}") (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ") [`a])])
        "▸"
        [(Term.subst
          (Term.app `add_comm [(Term.app `algebraMap [`R `A `r]) `a])
          "▸"
          [(Term.app `singleton_add_eq [`a `r])])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.subst
       (Term.app
        `add_comm
        [(«term{_}» "{" [`r] "}") (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ") [`a])])
       "▸"
       [(Term.subst
         (Term.app `add_comm [(Term.app `algebraMap [`R `A `r]) `a])
         "▸"
         [(Term.app `singleton_add_eq [`a `r])])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.subst
       (Term.app `add_comm [(Term.app `algebraMap [`R `A `r]) `a])
       "▸"
       [(Term.app `singleton_add_eq [`a `r])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `singleton_add_eq [`a `r])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `singleton_add_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 75, term))
      (Term.app `add_comm [(Term.app `algebraMap [`R `A `r]) `a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `algebraMap [`R `A `r])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `algebraMap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `algebraMap [`R `A `r]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `add_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 75, term)
[PrettyPrinter.parenthesize] ...precedences are 75 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 75, term))
      (Term.app
       `add_comm
       [(«term{_}» "{" [`r] "}") (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ") [`a])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Algebra.Algebra.Spectrum.termσ_1', expected 'spectrum.Algebra.Algebra.Spectrum.termσ_1._@.Algebra.Algebra.Spectrum._hyg.1680'
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
  add_singleton_eq
  ( a : A ) ( r : R ) : σ a + { r } = σ a + ↑ₐ r
  := add_comm { r } σ a ▸ add_comm algebraMap R A r a ▸ singleton_add_eq a r
#align spectrum.add_singleton_eq spectrum.add_singleton_eq

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `vadd_eq [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" `A] [] ")")
        (Term.explicitBinder "(" [`r] [":" `R] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Algebra.Group.Defs.«term_+ᵥ_»
          `r
          " +ᵥ "
          (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ") [`a]))
         "="
         (Term.app
          (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ")
          [(«term_+_»
            (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_1» "↑ₐ") [`r])
            "+"
            `a)]))))
      (Command.declValSimple
       ":="
       («term_<|_»
        (Term.proj (Term.proj `singleton_add "." `symm) "." `trans)
        "<|"
        (Term.app `singleton_add_eq [`a `r]))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj (Term.proj `singleton_add "." `symm) "." `trans)
       "<|"
       (Term.app `singleton_add_eq [`a `r]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `singleton_add_eq [`a `r])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `singleton_add_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj (Term.proj `singleton_add "." `symm) "." `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `singleton_add "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `singleton_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Algebra.Group.Defs.«term_+ᵥ_»
        `r
        " +ᵥ "
        (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ") [`a]))
       "="
       (Term.app
        (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ")
        [(«term_+_» (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_1» "↑ₐ") [`r]) "+" `a)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ")
       [(«term_+_» (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_1» "↑ₐ") [`r]) "+" `a)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_1» "↑ₐ") [`r]) "+" `a)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_1» "↑ₐ") [`r])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_1» "↑ₐ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_1»', expected 'spectrum.Algebra.Algebra.Spectrum.term↑ₐ_1._@.Algebra.Algebra.Spectrum._hyg.2176'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  vadd_eq
  ( a : A ) ( r : R ) : r +ᵥ σ a = σ ↑ₐ r + a
  := singleton_add . symm . trans <| singleton_add_eq a r
#align spectrum.vadd_eq spectrum.vadd_eq

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `neg_eq [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" `A] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term-_» "-" (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ") [`a]))
         "="
         (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ") [(«term-_» "-" `a)]))))
      (Command.declValSimple
       ":="
       (Term.app
        `Set.ext
        [(Term.fun
          "fun"
          (Term.basicFun
           [`x]
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
                 [(Tactic.simpLemma [] [] `mem_neg)
                  ","
                  (Tactic.simpLemma [] [] `mem_iff)
                  ","
                  (Tactic.simpLemma [] [] `map_neg)
                  ","
                  (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `neg_add')
                  ","
                  (Tactic.simpLemma [] [] `IsUnit.neg_iff)
                  ","
                  (Tactic.simpLemma [] [] `sub_neg_eq_add)]
                 "]"]
                [])])))))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Set.ext
       [(Term.fun
         "fun"
         (Term.basicFun
          [`x]
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
                [(Tactic.simpLemma [] [] `mem_neg)
                 ","
                 (Tactic.simpLemma [] [] `mem_iff)
                 ","
                 (Tactic.simpLemma [] [] `map_neg)
                 ","
                 (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `neg_add')
                 ","
                 (Tactic.simpLemma [] [] `IsUnit.neg_iff)
                 ","
                 (Tactic.simpLemma [] [] `sub_neg_eq_add)]
                "]"]
               [])])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
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
              [(Tactic.simpLemma [] [] `mem_neg)
               ","
               (Tactic.simpLemma [] [] `mem_iff)
               ","
               (Tactic.simpLemma [] [] `map_neg)
               ","
               (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `neg_add')
               ","
               (Tactic.simpLemma [] [] `IsUnit.neg_iff)
               ","
               (Tactic.simpLemma [] [] `sub_neg_eq_add)]
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
            [(Tactic.simpLemma [] [] `mem_neg)
             ","
             (Tactic.simpLemma [] [] `mem_iff)
             ","
             (Tactic.simpLemma [] [] `map_neg)
             ","
             (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `neg_add')
             ","
             (Tactic.simpLemma [] [] `IsUnit.neg_iff)
             ","
             (Tactic.simpLemma [] [] `sub_neg_eq_add)]
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
        [(Tactic.simpLemma [] [] `mem_neg)
         ","
         (Tactic.simpLemma [] [] `mem_iff)
         ","
         (Tactic.simpLemma [] [] `map_neg)
         ","
         (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `neg_add')
         ","
         (Tactic.simpLemma [] [] `IsUnit.neg_iff)
         ","
         (Tactic.simpLemma [] [] `sub_neg_eq_add)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_neg_eq_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `IsUnit.neg_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `neg_add'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_neg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_neg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Set.ext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       («term-_» "-" (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ") [`a]))
       "="
       (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ") [(«term-_» "-" `a)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ") [(«term-_» "-" `a)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" `a)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term-_» "-" `a) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Algebra.Algebra.Spectrum.termσ_1', expected 'spectrum.Algebra.Algebra.Spectrum.termσ_1._@.Algebra.Algebra.Spectrum._hyg.1680'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  neg_eq
  ( a : A ) : - σ a = σ - a
  :=
    Set.ext
      fun
        x
          =>
          by
            simp only [ mem_neg , mem_iff , map_neg , ← neg_add' , IsUnit.neg_iff , sub_neg_eq_add ]
#align spectrum.neg_eq spectrum.neg_eq

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `singleton_sub_eq [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" `A] [] ")")
        (Term.explicitBinder "(" [`r] [":" `R] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_-_»
          («term{_}» "{" [`r] "}")
          "-"
          (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ") [`a]))
         "="
         (Term.app
          (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ")
          [(«term_-_»
            (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_1» "↑ₐ") [`r])
            "-"
            `a)]))))
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
             [(Tactic.rwRule [] `sub_eq_add_neg)
              ","
              (Tactic.rwRule [] `neg_eq)
              ","
              (Tactic.rwRule [] `singleton_add_eq)
              ","
              (Tactic.rwRule [] `sub_eq_add_neg)]
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
            [(Tactic.rwRule [] `sub_eq_add_neg)
             ","
             (Tactic.rwRule [] `neg_eq)
             ","
             (Tactic.rwRule [] `singleton_add_eq)
             ","
             (Tactic.rwRule [] `sub_eq_add_neg)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `sub_eq_add_neg)
         ","
         (Tactic.rwRule [] `neg_eq)
         ","
         (Tactic.rwRule [] `singleton_add_eq)
         ","
         (Tactic.rwRule [] `sub_eq_add_neg)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_eq_add_neg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `singleton_add_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `neg_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_eq_add_neg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       («term_-_»
        («term{_}» "{" [`r] "}")
        "-"
        (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ") [`a]))
       "="
       (Term.app
        (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ")
        [(«term_-_» (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_1» "↑ₐ") [`r]) "-" `a)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ")
       [(«term_-_» (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_1» "↑ₐ") [`r]) "-" `a)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_1» "↑ₐ") [`r]) "-" `a)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_1» "↑ₐ") [`r])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_1» "↑ₐ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_1»', expected 'spectrum.Algebra.Algebra.Spectrum.term↑ₐ_1._@.Algebra.Algebra.Spectrum._hyg.2176'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  singleton_sub_eq
  ( a : A ) ( r : R ) : { r } - σ a = σ ↑ₐ r - a
  := by rw [ sub_eq_add_neg , neg_eq , singleton_add_eq , sub_eq_add_neg ]
#align spectrum.singleton_sub_eq spectrum.singleton_sub_eq

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `sub_singleton_eq [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" `A] [] ")")
        (Term.explicitBinder "(" [`r] [":" `R] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_-_»
          (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ") [`a])
          "-"
          («term{_}» "{" [`r] "}"))
         "="
         (Term.app
          (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ")
          [(«term_-_»
            `a
            "-"
            (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_1» "↑ₐ") [`r]))]))))
      (Command.declValSimple
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
             ["only"]
             [(Tactic.simpArgs
               "["
               [(Tactic.simpLemma [] [] `neg_sub) "," (Tactic.simpLemma [] [] `neg_eq)]
               "]")]
             ["using" (Term.app `congr_arg [`Neg.neg (Term.app `singleton_sub_eq [`a `r])])]))])))
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
              [(Tactic.simpLemma [] [] `neg_sub) "," (Tactic.simpLemma [] [] `neg_eq)]
              "]")]
            ["using" (Term.app `congr_arg [`Neg.neg (Term.app `singleton_sub_eq [`a `r])])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        ["only"]
        [(Tactic.simpArgs
          "["
          [(Tactic.simpLemma [] [] `neg_sub) "," (Tactic.simpLemma [] [] `neg_eq)]
          "]")]
        ["using" (Term.app `congr_arg [`Neg.neg (Term.app `singleton_sub_eq [`a `r])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `congr_arg [`Neg.neg (Term.app `singleton_sub_eq [`a `r])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `singleton_sub_eq [`a `r])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `singleton_sub_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `singleton_sub_eq [`a `r])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Neg.neg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `congr_arg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `neg_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `neg_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       («term_-_»
        (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ") [`a])
        "-"
        («term{_}» "{" [`r] "}"))
       "="
       (Term.app
        (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ")
        [(«term_-_» `a "-" (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_1» "↑ₐ") [`r]))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ")
       [(«term_-_» `a "-" (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_1» "↑ₐ") [`r]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» `a "-" (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_1» "↑ₐ") [`r]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_1» "↑ₐ") [`r])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_1» "↑ₐ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_1»', expected 'spectrum.Algebra.Algebra.Spectrum.term↑ₐ_1._@.Algebra.Algebra.Spectrum._hyg.2176'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  sub_singleton_eq
  ( a : A ) ( r : R ) : σ a - { r } = σ a - ↑ₐ r
  := by simpa only [ neg_sub , neg_eq ] using congr_arg Neg.neg singleton_sub_eq a r
#align spectrum.sub_singleton_eq spectrum.sub_singleton_eq

open Polynomial

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `exists_mem_of_not_is_unit_aeval_prod [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `IsDomain [`R]) "]")
        (Term.implicitBinder
         "{"
         [`p]
         [":" (Polynomial.Data.Polynomial.Basic.polynomial `R "[X]")]
         "}")
        (Term.implicitBinder "{" [`a] [":" `A] "}")
        (Term.explicitBinder "(" [`hp] [":" («term_≠_» `p "≠" (num "0"))] [] ")")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          («term¬_»
           "¬"
           (Term.app
            `IsUnit
            [(Term.app
              `aeval
              [`a
               (Term.proj
                (Term.app
                 `Multiset.map
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [`x]
                    [(Term.typeSpec ":" `R)]
                    "=>"
                    («term_-_» `X "-" (Term.app `c [`x]))))
                  (Term.proj `p "." `roots)])
                "."
                `Prod)])]))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] [":" `R]))
         ","
         («term_∧_»
          («term_∈_» `k "∈" (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ") [`a]))
          "∧"
          («term_=_» (Term.app `eval [`k `p]) "=" (num "0"))))))
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
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Multiset.prod_to_list)
              ","
              (Tactic.rwRule [] `AlgHom.map_list_prod)]
             "]")
            [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
           []
           (Mathlib.Tactic.tacticReplace_
            "replace"
            (Term.haveDecl
             (Term.haveIdDecl [`h []] [] ":=" (Term.app `mt [`List.prod_is_unit `h]))))
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `not_forall)
              ","
              (Tactic.simpLemma [] [] `exists_prop)
              ","
              (Tactic.simpLemma [] [] `aeval_C)
              ","
              (Tactic.simpLemma [] [] `Multiset.mem_to_list)
              ","
              (Tactic.simpLemma [] [] `List.mem_map')
              ","
              (Tactic.simpLemma [] [] `aeval_X)
              ","
              (Tactic.simpLemma [] [] `exists_exists_and_eq_and)
              ","
              (Tactic.simpLemma [] [] `Multiset.mem_map)
              ","
              (Tactic.simpLemma [] [] `AlgHom.map_sub)]
             "]"]
            [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
           []
           (Std.Tactic.rcases
            "rcases"
            [(Tactic.casesTarget [] `h)]
            ["with"
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r_mem)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r_nu)])
                   [])]
                 "⟩")])
              [])])
           []
           (Tactic.exact
            "exact"
            (Term.anonymousCtor
             "⟨"
             [`r
              ","
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Std.Tactic.tacticRwa__
                   "rwa"
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `mem_iff)
                     ","
                     (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `IsUnit.sub_iff)]
                    "]")
                   [])])))
              ","
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Std.Tactic.tacticRwa__
                   "rwa"
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `is_root.def)
                     ","
                     (Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `mem_roots [`hp]))]
                    "]")
                   [])])))]
             "⟩"))])))
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
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Multiset.prod_to_list)
             ","
             (Tactic.rwRule [] `AlgHom.map_list_prod)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
          []
          (Mathlib.Tactic.tacticReplace_
           "replace"
           (Term.haveDecl (Term.haveIdDecl [`h []] [] ":=" (Term.app `mt [`List.prod_is_unit `h]))))
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `not_forall)
             ","
             (Tactic.simpLemma [] [] `exists_prop)
             ","
             (Tactic.simpLemma [] [] `aeval_C)
             ","
             (Tactic.simpLemma [] [] `Multiset.mem_to_list)
             ","
             (Tactic.simpLemma [] [] `List.mem_map')
             ","
             (Tactic.simpLemma [] [] `aeval_X)
             ","
             (Tactic.simpLemma [] [] `exists_exists_and_eq_and)
             ","
             (Tactic.simpLemma [] [] `Multiset.mem_map)
             ","
             (Tactic.simpLemma [] [] `AlgHom.map_sub)]
            "]"]
           [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
          []
          (Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] `h)]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r_mem)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r_nu)])
                  [])]
                "⟩")])
             [])])
          []
          (Tactic.exact
           "exact"
           (Term.anonymousCtor
            "⟨"
            [`r
             ","
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.tacticRwa__
                  "rwa"
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `mem_iff)
                    ","
                    (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `IsUnit.sub_iff)]
                   "]")
                  [])])))
             ","
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.tacticRwa__
                  "rwa"
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `is_root.def)
                    ","
                    (Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `mem_roots [`hp]))]
                   "]")
                  [])])))]
            "⟩"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.anonymousCtor
        "⟨"
        [`r
         ","
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Std.Tactic.tacticRwa__
              "rwa"
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `mem_iff)
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `IsUnit.sub_iff)]
               "]")
              [])])))
         ","
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Std.Tactic.tacticRwa__
              "rwa"
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `is_root.def)
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `mem_roots [`hp]))]
               "]")
              [])])))]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`r
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Std.Tactic.tacticRwa__
             "rwa"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `mem_iff)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `IsUnit.sub_iff)]
              "]")
             [])])))
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Std.Tactic.tacticRwa__
             "rwa"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `is_root.def)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `mem_roots [`hp]))]
              "]")
             [])])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.tacticRwa__
           "rwa"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `is_root.def)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `mem_roots [`hp]))]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `is_root.def)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `mem_roots [`hp]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mem_roots [`hp])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mem_roots
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `is_root.def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.tacticRwa__
           "rwa"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `mem_iff)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `IsUnit.sub_iff)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `mem_iff)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `IsUnit.sub_iff)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `IsUnit.sub_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] `h)]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r_mem)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r_nu)])
              [])]
            "⟩")])
         [])])
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
        [(Tactic.simpLemma [] [] `not_forall)
         ","
         (Tactic.simpLemma [] [] `exists_prop)
         ","
         (Tactic.simpLemma [] [] `aeval_C)
         ","
         (Tactic.simpLemma [] [] `Multiset.mem_to_list)
         ","
         (Tactic.simpLemma [] [] `List.mem_map')
         ","
         (Tactic.simpLemma [] [] `aeval_X)
         ","
         (Tactic.simpLemma [] [] `exists_exists_and_eq_and)
         ","
         (Tactic.simpLemma [] [] `Multiset.mem_map)
         ","
         (Tactic.simpLemma [] [] `AlgHom.map_sub)]
        "]"]
       [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `AlgHom.map_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Multiset.mem_map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `exists_exists_and_eq_and
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `aeval_X
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `List.mem_map'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Multiset.mem_to_list
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `aeval_C
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `exists_prop
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `not_forall
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticReplace_
       "replace"
       (Term.haveDecl (Term.haveIdDecl [`h []] [] ":=" (Term.app `mt [`List.prod_is_unit `h]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mt [`List.prod_is_unit `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `List.prod_is_unit
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mt
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
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Multiset.prod_to_list)
         ","
         (Tactic.rwRule [] `AlgHom.map_list_prod)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `AlgHom.map_list_prod
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Multiset.prod_to_list
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] [":" `R]))
       ","
       («term_∧_»
        («term_∈_» `k "∈" (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ") [`a]))
        "∧"
        («term_=_» (Term.app `eval [`k `p]) "=" (num "0"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∧_»
       («term_∈_» `k "∈" (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ") [`a]))
       "∧"
       («term_=_» (Term.app `eval [`k `p]) "=" (num "0")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.app `eval [`k `p]) "=" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `eval [`k `p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eval
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 35 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      («term_∈_» `k "∈" (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ") [`a]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Algebra.Algebra.Spectrum.termσ_1 "σ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Algebra.Algebra.Spectrum.termσ_1', expected 'spectrum.Algebra.Algebra.Spectrum.termσ_1._@.Algebra.Algebra.Spectrum._hyg.1680'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  exists_mem_of_not_is_unit_aeval_prod
  [ IsDomain R ]
      { p : R [X] }
      { a : A }
      ( hp : p ≠ 0 )
      ( h : ¬ IsUnit aeval a Multiset.map fun x : R => X - c x p . roots . Prod )
    : ∃ k : R , k ∈ σ a ∧ eval k p = 0
  :=
    by
      rw [ ← Multiset.prod_to_list , AlgHom.map_list_prod ] at h
        replace h := mt List.prod_is_unit h
        simp
          only
          [
            not_forall
              ,
              exists_prop
              ,
              aeval_C
              ,
              Multiset.mem_to_list
              ,
              List.mem_map'
              ,
              aeval_X
              ,
              exists_exists_and_eq_and
              ,
              Multiset.mem_map
              ,
              AlgHom.map_sub
            ]
          at h
        rcases h with ⟨ r , r_mem , r_nu ⟩
        exact
          ⟨ r , by rwa [ mem_iff , ← IsUnit.sub_iff ] , by rwa [ ← is_root.def , ← mem_roots hp ] ⟩
#align spectrum.exists_mem_of_not_is_unit_aeval_prod spectrum.exists_mem_of_not_is_unit_aeval_prod

end ScalarRing

section ScalarField

variable {𝕜 : Type u} {A : Type v}

variable [Field 𝕜] [Ring A] [Algebra 𝕜 A]

-- mathport name: exprσ
local notation "σ" => spectrum 𝕜

-- mathport name: «expr↑ₐ»
local notation "↑ₐ" => algebraMap 𝕜 A

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Without the assumption `nontrivial A`, then `0 : A` would be invertible. -/")]
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `zero_eq [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `Nontrivial [`A]) "]")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ")
          [(Term.typeAscription "(" (num "0") ":" [`A] ")")])
         "="
         («term{_}» "{" [(num "0")] "}"))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.app
             `Set.Subset.antisymm
             [(Term.hole "_")
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
                    [(Tactic.simpLemma [] [] `Algebra.algebra_map_eq_smul_one)
                     ","
                     (Tactic.simpLemma [] [] `mem_iff)]
                    "]"]
                   [])])))]))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `spectrum) "," (Tactic.rwRule [] `Set.compl_subset_comm)]
             "]")
            [])
           []
           (Tactic.intro "intro" [`k `hk])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.mem_compl_singleton_iff)] "]")
            [(Tactic.location "at" (Tactic.locationHyp [`hk] []))])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                (Term.app
                 `IsUnit
                 [(Algebra.Group.Defs.«term_•_»
                   (Term.app `Units.mk0 [`k `hk])
                   " • "
                   (Term.typeAscription "(" (num "1") ":" [`A] ")"))]))]
              ":="
              (Term.app `IsUnit.smul [(Term.app `Units.mk0 [`k `hk]) `isUnit_one]))))
           []
           (Std.Tactic.Simpa.simpa
            "simpa"
            []
            []
            (Std.Tactic.Simpa.simpaArgsRest
             []
             []
             []
             [(Tactic.simpArgs
               "["
               [(Tactic.simpLemma [] [] `mem_resolvent_set_iff)
                ","
                (Tactic.simpLemma [] [] `Algebra.algebra_map_eq_smul_one)]
               "]")]
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
         [(Tactic.refine'
           "refine'"
           (Term.app
            `Set.Subset.antisymm
            [(Term.hole "_")
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
                   [(Tactic.simpLemma [] [] `Algebra.algebra_map_eq_smul_one)
                    ","
                    (Tactic.simpLemma [] [] `mem_iff)]
                   "]"]
                  [])])))]))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `spectrum) "," (Tactic.rwRule [] `Set.compl_subset_comm)]
            "]")
           [])
          []
          (Tactic.intro "intro" [`k `hk])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.mem_compl_singleton_iff)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`hk] []))])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               (Term.app
                `IsUnit
                [(Algebra.Group.Defs.«term_•_»
                  (Term.app `Units.mk0 [`k `hk])
                  " • "
                  (Term.typeAscription "(" (num "1") ":" [`A] ")"))]))]
             ":="
             (Term.app `IsUnit.smul [(Term.app `Units.mk0 [`k `hk]) `isUnit_one]))))
          []
          (Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            []
            [(Tactic.simpArgs
              "["
              [(Tactic.simpLemma [] [] `mem_resolvent_set_iff)
               ","
               (Tactic.simpLemma [] [] `Algebra.algebra_map_eq_smul_one)]
              "]")]
            []))])))
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
        [(Tactic.simpArgs
          "["
          [(Tactic.simpLemma [] [] `mem_resolvent_set_iff)
           ","
           (Tactic.simpLemma [] [] `Algebra.algebra_map_eq_smul_one)]
          "]")]
        []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Algebra.algebra_map_eq_smul_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_resolvent_set_iff
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
           (Term.app
            `IsUnit
            [(Algebra.Group.Defs.«term_•_»
              (Term.app `Units.mk0 [`k `hk])
              " • "
              (Term.typeAscription "(" (num "1") ":" [`A] ")"))]))]
         ":="
         (Term.app `IsUnit.smul [(Term.app `Units.mk0 [`k `hk]) `isUnit_one]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsUnit.smul [(Term.app `Units.mk0 [`k `hk]) `isUnit_one])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `isUnit_one
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Units.mk0 [`k `hk])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hk
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Units.mk0
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Units.mk0 [`k `hk]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsUnit.smul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `IsUnit
       [(Algebra.Group.Defs.«term_•_»
         (Term.app `Units.mk0 [`k `hk])
         " • "
         (Term.typeAscription "(" (num "1") ":" [`A] ")"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_»
       (Term.app `Units.mk0 [`k `hk])
       " • "
       (Term.typeAscription "(" (num "1") ":" [`A] ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" (num "1") ":" [`A] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      (Term.app `Units.mk0 [`k `hk])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hk
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Units.mk0
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1022, (some 1023, term) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Group.Defs.«term_•_»
      (Term.app `Units.mk0 [`k `hk])
      " • "
      (Term.typeAscription "(" (num "1") ":" [`A] ")"))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsUnit
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.mem_compl_singleton_iff)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`hk] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.mem_compl_singleton_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`k `hk])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `spectrum) "," (Tactic.rwRule [] `Set.compl_subset_comm)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.compl_subset_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `spectrum
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `Set.Subset.antisymm
        [(Term.hole "_")
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
               [(Tactic.simpLemma [] [] `Algebra.algebra_map_eq_smul_one)
                ","
                (Tactic.simpLemma [] [] `mem_iff)]
               "]"]
              [])])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Set.Subset.antisymm
       [(Term.hole "_")
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
              [(Tactic.simpLemma [] [] `Algebra.algebra_map_eq_smul_one)
               ","
               (Tactic.simpLemma [] [] `mem_iff)]
              "]"]
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
           ["["
            [(Tactic.simpLemma [] [] `Algebra.algebra_map_eq_smul_one)
             ","
             (Tactic.simpLemma [] [] `mem_iff)]
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
        [(Tactic.simpLemma [] [] `Algebra.algebra_map_eq_smul_one)
         ","
         (Tactic.simpLemma [] [] `mem_iff)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Algebra.algebra_map_eq_smul_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
          ["["
           [(Tactic.simpLemma [] [] `Algebra.algebra_map_eq_smul_one)
            ","
            (Tactic.simpLemma [] [] `mem_iff)]
           "]"]
          [])])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Set.Subset.antisymm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ")
        [(Term.typeAscription "(" (num "0") ":" [`A] ")")])
       "="
       («term{_}» "{" [(num "0")] "}"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term{_}» "{" [(num "0")] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ")
       [(Term.typeAscription "(" (num "0") ":" [`A] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" (num "0") ":" [`A] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Algebra.Algebra.Spectrum.termσ_2', expected 'spectrum.Algebra.Algebra.Spectrum.termσ_2._@.Algebra.Algebra.Spectrum._hyg.2759'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Without the assumption `nontrivial A`, then `0 : A` would be invertible. -/ @[ simp ]
  theorem
    zero_eq
    [ Nontrivial A ] : σ ( 0 : A ) = { 0 }
    :=
      by
        refine' Set.Subset.antisymm _ by simp [ Algebra.algebra_map_eq_smul_one , mem_iff ]
          rw [ spectrum , Set.compl_subset_comm ]
          intro k hk
          rw [ Set.mem_compl_singleton_iff ] at hk
          have : IsUnit Units.mk0 k hk • ( 1 : A ) := IsUnit.smul Units.mk0 k hk isUnit_one
          simpa [ mem_resolvent_set_iff , Algebra.algebra_map_eq_smul_one ]
#align spectrum.zero_eq spectrum.zero_eq

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
      (Command.declId `scalar_eq [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `Nontrivial [`A]) "]")
        (Term.explicitBinder "(" [`k] [":" `𝕜] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ")
          [(Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_2» "↑ₐ") [`k])])
         "="
         («term{_}» "{" [`k] "}"))))
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
               (Term.app
                `add_zero
                [(Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_2» "↑ₐ") [`k])]))
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `singleton_add_eq)
              ","
              (Tactic.rwRule [] `zero_eq)
              ","
              (Tactic.rwRule [] `Set.singleton_add_singleton)
              ","
              (Tactic.rwRule [] `add_zero)]
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
              (Term.app
               `add_zero
               [(Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_2» "↑ₐ") [`k])]))
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `singleton_add_eq)
             ","
             (Tactic.rwRule [] `zero_eq)
             ","
             (Tactic.rwRule [] `Set.singleton_add_singleton)
             ","
             (Tactic.rwRule [] `add_zero)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app
           `add_zero
           [(Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_2» "↑ₐ") [`k])]))
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `singleton_add_eq)
         ","
         (Tactic.rwRule [] `zero_eq)
         ","
         (Tactic.rwRule [] `Set.singleton_add_singleton)
         ","
         (Tactic.rwRule [] `add_zero)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.singleton_add_singleton
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `singleton_add_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `add_zero [(Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_2» "↑ₐ") [`k])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_2» "↑ₐ") [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_2» "↑ₐ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_2»', expected 'spectrum.Algebra.Algebra.Spectrum.term↑ₐ_2._@.Algebra.Algebra.Spectrum._hyg.3255'
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
    scalar_eq
    [ Nontrivial A ] ( k : 𝕜 ) : σ ↑ₐ k = { k }
    :=
      by
        rw
          [
            ← add_zero ↑ₐ k , ← singleton_add_eq , zero_eq , Set.singleton_add_singleton , add_zero
            ]
#align spectrum.scalar_eq spectrum.scalar_eq

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
      (Command.declId `one_eq [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `Nontrivial [`A]) "]")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ")
          [(Term.typeAscription "(" (num "1") ":" [`A] ")")])
         "="
         («term{_}» "{" [(num "1")] "}"))))
      (Command.declValSimple
       ":="
       (calc
        "calc"
        (calcStep
         («term_=_»
          (Term.app
           (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ")
           [(Term.typeAscription "(" (num "1") ":" [`A] ")")])
          "="
          (Term.app
           (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ")
           [(Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_2» "↑ₐ") [(num "1")])]))
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
               [(Tactic.rwRule [] `Algebra.algebra_map_eq_smul_one)
                ","
                (Tactic.rwRule [] `one_smul)]
               "]")
              [])]))))
        [(calcStep
          («term_=_» (Term.hole "_") "=" («term{_}» "{" [(num "1")] "}"))
          ":="
          (Term.app `scalar_eq [(num "1")]))])
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
         (Term.app
          (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ")
          [(Term.typeAscription "(" (num "1") ":" [`A] ")")])
         "="
         (Term.app
          (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ")
          [(Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_2» "↑ₐ") [(num "1")])]))
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
              [(Tactic.rwRule [] `Algebra.algebra_map_eq_smul_one) "," (Tactic.rwRule [] `one_smul)]
              "]")
             [])]))))
       [(calcStep
         («term_=_» (Term.hole "_") "=" («term{_}» "{" [(num "1")] "}"))
         ":="
         (Term.app `scalar_eq [(num "1")]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `scalar_eq [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `scalar_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.hole "_") "=" («term{_}» "{" [(num "1")] "}"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term{_}» "{" [(num "1")] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `Algebra.algebra_map_eq_smul_one) "," (Tactic.rwRule [] `one_smul)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `Algebra.algebra_map_eq_smul_one) "," (Tactic.rwRule [] `one_smul)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Algebra.algebra_map_eq_smul_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app
        (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ")
        [(Term.typeAscription "(" (num "1") ":" [`A] ")")])
       "="
       (Term.app
        (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ")
        [(Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_2» "↑ₐ") [(num "1")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ")
       [(Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_2» "↑ₐ") [(num "1")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_2» "↑ₐ") [(num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_2» "↑ₐ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_2»', expected 'spectrum.Algebra.Algebra.Spectrum.term↑ₐ_2._@.Algebra.Algebra.Spectrum._hyg.3255'
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
    one_eq
    [ Nontrivial A ] : σ ( 1 : A ) = { 1 }
    :=
      calc
        σ ( 1 : A ) = σ ↑ₐ 1 := by rw [ Algebra.algebra_map_eq_smul_one , one_smul ]
        _ = { 1 } := scalar_eq 1
#align spectrum.one_eq spectrum.one_eq

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "the assumption `(σ a).nonempty` is necessary and cannot be removed without\n    further conditions on the algebra `A` and scalar field `𝕜`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `smul_eq_smul [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `Nontrivial [`A]) "]")
        (Term.explicitBinder "(" [`k] [":" `𝕜] [] ")")
        (Term.explicitBinder "(" [`a] [":" `A] [] ")")
        (Term.explicitBinder
         "("
         [`ha]
         [":"
          (Term.proj (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [`a]) "." `Nonempty)]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ")
          [(Algebra.Group.Defs.«term_•_» `k " • " `a)])
         "="
         (Algebra.Group.Defs.«term_•_»
          `k
          " • "
          (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [`a])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.rcases
            "rcases"
            [(Tactic.casesTarget [] (Term.app `eq_or_ne [`k (num "0")]))]
            ["with"
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.paren
                 "("
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.one `rfl)
                    "|"
                    (Std.Tactic.RCases.rcasesPat.one `h)])
                  [])
                 ")")])
              [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest
               []
               []
               []
               [(Tactic.simpArgs
                 "["
                 [(Tactic.simpLemma [] [] `ha) "," (Tactic.simpLemma [] [] `zero_smul_set)]
                 "]")]
               []))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.exact
              "exact"
              (Term.app `unit_smul_eq_smul [`a (Term.app `Units.mk0 [`k `h])]))])])))
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
         [(Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] (Term.app `eq_or_ne [`k (num "0")]))]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.paren
                "("
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.one `rfl) "|" (Std.Tactic.RCases.rcasesPat.one `h)])
                 [])
                ")")])
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.Simpa.simpa
             "simpa"
             []
             []
             (Std.Tactic.Simpa.simpaArgsRest
              []
              []
              []
              [(Tactic.simpArgs
                "["
                [(Tactic.simpLemma [] [] `ha) "," (Tactic.simpLemma [] [] `zero_smul_set)]
                "]")]
              []))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact
             "exact"
             (Term.app `unit_smul_eq_smul [`a (Term.app `Units.mk0 [`k `h])]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact "exact" (Term.app `unit_smul_eq_smul [`a (Term.app `Units.mk0 [`k `h])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `unit_smul_eq_smul [`a (Term.app `Units.mk0 [`k `h])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `unit_smul_eq_smul [`a (Term.app `Units.mk0 [`k `h])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Units.mk0 [`k `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Units.mk0
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Units.mk0 [`k `h]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `unit_smul_eq_smul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.Simpa.simpa
         "simpa"
         []
         []
         (Std.Tactic.Simpa.simpaArgsRest
          []
          []
          []
          [(Tactic.simpArgs
            "["
            [(Tactic.simpLemma [] [] `ha) "," (Tactic.simpLemma [] [] `zero_smul_set)]
            "]")]
          []))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        []
        [(Tactic.simpArgs
          "["
          [(Tactic.simpLemma [] [] `ha) "," (Tactic.simpLemma [] [] `zero_smul_set)]
          "]")]
        []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zero_smul_set
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] (Term.app `eq_or_ne [`k (num "0")]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.paren
            "("
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.one `rfl) "|" (Std.Tactic.RCases.rcasesPat.one `h)])
             [])
            ")")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `eq_or_ne [`k (num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eq_or_ne
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ")
        [(Algebra.Group.Defs.«term_•_» `k " • " `a)])
       "="
       (Algebra.Group.Defs.«term_•_»
        `k
        " • "
        (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [`a])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_»
       `k
       " • "
       (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [`a]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Algebra.Algebra.Spectrum.termσ_2', expected 'spectrum.Algebra.Algebra.Spectrum.termσ_2._@.Algebra.Algebra.Spectrum._hyg.2759'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    the assumption `(σ a).nonempty` is necessary and cannot be removed without
        further conditions on the algebra `A` and scalar field `𝕜`. -/
  theorem
    smul_eq_smul
    [ Nontrivial A ] ( k : 𝕜 ) ( a : A ) ( ha : σ a . Nonempty ) : σ k • a = k • σ a
    :=
      by
        rcases eq_or_ne k 0 with ( rfl | h )
          · simpa [ ha , zero_smul_set ]
          · exact unit_smul_eq_smul a Units.mk0 k h
#align spectrum.smul_eq_smul spectrum.smul_eq_smul

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `nonzero_mul_eq_swap_mul [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a `b] [":" `A] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_\_»
          (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [(«term_*_» `a "*" `b)])
          "\\"
          («term{_}» "{" [(num "0")] "}"))
         "="
         («term_\_»
          (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [(«term_*_» `b "*" `a)])
          "\\"
          («term{_}» "{" [(num "0")] "}")))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Mathlib.Tactic.tacticSuffices_
            "suffices"
            [`h []]
            [(Term.typeSpec
              ":"
              (Term.forall
               "∀"
               [`x `y]
               [(Term.typeSpec ":" `A)]
               ","
               («term_⊆_»
                («term_\_»
                 (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [(«term_*_» `x "*" `y)])
                 "\\"
                 («term{_}» "{" [(num "0")] "}"))
                "⊆"
                («term_\_»
                 (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [(«term_*_» `y "*" `x)])
                 "\\"
                 («term{_}» "{" [(num "0")] "}")))))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.exact
              "exact"
              (Term.app
               `Set.eq_of_subset_of_subset
               [(Term.app `h [`a `b]) (Term.app `h [`b `a])]))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.rintro
              "rintro"
              [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.ignore "_"))
               (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.ignore "_"))
               (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `k))
               (Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k_mem)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k_neq)])
                   [])]
                 "⟩"))]
              [])
             []
             (Tactic.changeWith
              "change"
              `k
              "with"
              (coeNotation "↑" (Term.app `Units.mk0 [`k `k_neq]))
              [(Tactic.location "at" (Tactic.locationHyp [`k_mem] []))])
             []
             (Tactic.exact
              "exact"
              (Term.anonymousCtor
               "⟨"
               [(Term.app `unit_mem_mul_iff_mem_swap_mul.mp [`k_mem]) "," `k_neq]
               "⟩"))])])))
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
         [(Mathlib.Tactic.tacticSuffices_
           "suffices"
           [`h []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [`x `y]
              [(Term.typeSpec ":" `A)]
              ","
              («term_⊆_»
               («term_\_»
                (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [(«term_*_» `x "*" `y)])
                "\\"
                («term{_}» "{" [(num "0")] "}"))
               "⊆"
               («term_\_»
                (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [(«term_*_» `y "*" `x)])
                "\\"
                («term{_}» "{" [(num "0")] "}")))))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact
             "exact"
             (Term.app `Set.eq_of_subset_of_subset [(Term.app `h [`a `b]) (Term.app `h [`b `a])]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.rintro
             "rintro"
             [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.ignore "_"))
              (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.ignore "_"))
              (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `k))
              (Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k_mem)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k_neq)])
                  [])]
                "⟩"))]
             [])
            []
            (Tactic.changeWith
             "change"
             `k
             "with"
             (coeNotation "↑" (Term.app `Units.mk0 [`k `k_neq]))
             [(Tactic.location "at" (Tactic.locationHyp [`k_mem] []))])
            []
            (Tactic.exact
             "exact"
             (Term.anonymousCtor
              "⟨"
              [(Term.app `unit_mem_mul_iff_mem_swap_mul.mp [`k_mem]) "," `k_neq]
              "⟩"))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.rintro
         "rintro"
         [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.ignore "_"))
          (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.ignore "_"))
          (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `k))
          (Std.Tactic.RCases.rintroPat.one
           (Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k_mem)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k_neq)])
              [])]
            "⟩"))]
         [])
        []
        (Tactic.changeWith
         "change"
         `k
         "with"
         (coeNotation "↑" (Term.app `Units.mk0 [`k `k_neq]))
         [(Tactic.location "at" (Tactic.locationHyp [`k_mem] []))])
        []
        (Tactic.exact
         "exact"
         (Term.anonymousCtor
          "⟨"
          [(Term.app `unit_mem_mul_iff_mem_swap_mul.mp [`k_mem]) "," `k_neq]
          "⟩"))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.anonymousCtor
        "⟨"
        [(Term.app `unit_mem_mul_iff_mem_swap_mul.mp [`k_mem]) "," `k_neq]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app `unit_mem_mul_iff_mem_swap_mul.mp [`k_mem]) "," `k_neq]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k_neq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `unit_mem_mul_iff_mem_swap_mul.mp [`k_mem])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k_mem
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `unit_mem_mul_iff_mem_swap_mul.mp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.changeWith
       "change"
       `k
       "with"
       (coeNotation "↑" (Term.app `Units.mk0 [`k `k_neq]))
       [(Tactic.location "at" (Tactic.locationHyp [`k_mem] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (coeNotation "↑" (Term.app `Units.mk0 [`k `k_neq]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Units.mk0 [`k `k_neq])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k_neq
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Units.mk0
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Units.mk0 [`k `k_neq]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rintro
       "rintro"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.ignore "_"))
        (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.ignore "_"))
        (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `k))
        (Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k_mem)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k_neq)])
            [])]
          "⟩"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact
         "exact"
         (Term.app `Set.eq_of_subset_of_subset [(Term.app `h [`a `b]) (Term.app `h [`b `a])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app `Set.eq_of_subset_of_subset [(Term.app `h [`a `b]) (Term.app `h [`b `a])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Set.eq_of_subset_of_subset [(Term.app `h [`a `b]) (Term.app `h [`b `a])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h [`b `a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `h [`b `a]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `h [`a `b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `h [`a `b]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Set.eq_of_subset_of_subset
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSuffices_
       "suffices"
       [`h []]
       [(Term.typeSpec
         ":"
         (Term.forall
          "∀"
          [`x `y]
          [(Term.typeSpec ":" `A)]
          ","
          («term_⊆_»
           («term_\_»
            (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [(«term_*_» `x "*" `y)])
            "\\"
            («term{_}» "{" [(num "0")] "}"))
           "⊆"
           («term_\_»
            (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [(«term_*_» `y "*" `x)])
            "\\"
            («term{_}» "{" [(num "0")] "}")))))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`x `y]
       [(Term.typeSpec ":" `A)]
       ","
       («term_⊆_»
        («term_\_»
         (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [(«term_*_» `x "*" `y)])
         "\\"
         («term{_}» "{" [(num "0")] "}"))
        "⊆"
        («term_\_»
         (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [(«term_*_» `y "*" `x)])
         "\\"
         («term{_}» "{" [(num "0")] "}"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⊆_»
       («term_\_»
        (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [(«term_*_» `x "*" `y)])
        "\\"
        («term{_}» "{" [(num "0")] "}"))
       "⊆"
       («term_\_»
        (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [(«term_*_» `y "*" `x)])
        "\\"
        («term{_}» "{" [(num "0")] "}")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_\_»
       (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [(«term_*_» `y "*" `x)])
       "\\"
       («term{_}» "{" [(num "0")] "}"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term{_}» "{" [(num "0")] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [(«term_*_» `y "*" `x)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `y "*" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_*_» `y "*" `x) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Algebra.Algebra.Spectrum.termσ_2', expected 'spectrum.Algebra.Algebra.Spectrum.termσ_2._@.Algebra.Algebra.Spectrum._hyg.2759'
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
  nonzero_mul_eq_swap_mul
  ( a b : A ) : σ a * b \ { 0 } = σ b * a \ { 0 }
  :=
    by
      suffices h : ∀ x y : A , σ x * y \ { 0 } ⊆ σ y * x \ { 0 }
        · exact Set.eq_of_subset_of_subset h a b h b a
        ·
          rintro _ _ k ⟨ k_mem , k_neq ⟩
            change k with ↑ Units.mk0 k k_neq at k_mem
            exact ⟨ unit_mem_mul_iff_mem_swap_mul.mp k_mem , k_neq ⟩
#align spectrum.nonzero_mul_eq_swap_mul spectrum.nonzero_mul_eq_swap_mul

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `map_inv [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" (Algebra.Group.Units.«term_ˣ» `A "ˣ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         («term_⁻¹»
          (Term.app
           (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ")
           [(Term.typeAscription "(" `a ":" [`A] ")")])
          "⁻¹")
         "="
         (Term.app
          (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ")
          [(Term.typeAscription "(" (coeNotation "↑" («term_⁻¹» `a "⁻¹")) ":" [`A] ")")]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.app
             `Set.eq_of_subset_of_subset
             [(Term.fun "fun" (Term.basicFun [`k `hk] [] "=>" (Term.hole "_")))
              (Term.fun "fun" (Term.basicFun [`k `hk] [] "=>" (Term.hole "_")))]))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.mem_inv)] "]")
              [(Tactic.location "at" (Tactic.locationHyp [`hk] []))])
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec ":" («term_≠_» `k "≠" (num "0")))]
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
                      ["only"]
                      [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `inv_inv)] "]")]
                      ["using"
                       (Term.app `inv_ne_zero [(Term.app `ne_zero_of_mem_of_unit [`hk])])]))]))))))
             []
             (Tactic.lift
              "lift"
              `k
              "to"
              (Algebra.Group.Units.«term_ˣ» `𝕜 "ˣ")
              ["using" (Term.app `is_unit_iff_ne_zero.mpr [`this])]
              [])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 (Term.app `Units.val_inv_eq_inv_val [`k]))]
               "]")
              [(Tactic.location "at" (Tactic.locationHyp [`hk] []))])
             []
             (Tactic.exact "exact" (Term.app `inv_mem_iff.mp [`hk]))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.lift
              "lift"
              `k
              "to"
              (Algebra.Group.Units.«term_ˣ» `𝕜 "ˣ")
              ["using"
               (Term.app `is_unit_iff_ne_zero.mpr [(Term.app `ne_zero_of_mem_of_unit [`hk])])]
              [])
             []
             (Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest
               []
               []
               ["only"]
               [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `Units.val_inv_eq_inv_val)] "]")]
               ["using" (Term.app `inv_mem_iff.mp [`hk])]))])])))
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
            `Set.eq_of_subset_of_subset
            [(Term.fun "fun" (Term.basicFun [`k `hk] [] "=>" (Term.hole "_")))
             (Term.fun "fun" (Term.basicFun [`k `hk] [] "=>" (Term.hole "_")))]))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.mem_inv)] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`hk] []))])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec ":" («term_≠_» `k "≠" (num "0")))]
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
                     ["only"]
                     [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `inv_inv)] "]")]
                     ["using"
                      (Term.app `inv_ne_zero [(Term.app `ne_zero_of_mem_of_unit [`hk])])]))]))))))
            []
            (Tactic.lift
             "lift"
             `k
             "to"
             (Algebra.Group.Units.«term_ˣ» `𝕜 "ˣ")
             ["using" (Term.app `is_unit_iff_ne_zero.mpr [`this])]
             [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.app `Units.val_inv_eq_inv_val [`k]))]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`hk] []))])
            []
            (Tactic.exact "exact" (Term.app `inv_mem_iff.mp [`hk]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.lift
             "lift"
             `k
             "to"
             (Algebra.Group.Units.«term_ˣ» `𝕜 "ˣ")
             ["using"
              (Term.app `is_unit_iff_ne_zero.mpr [(Term.app `ne_zero_of_mem_of_unit [`hk])])]
             [])
            []
            (Std.Tactic.Simpa.simpa
             "simpa"
             []
             []
             (Std.Tactic.Simpa.simpaArgsRest
              []
              []
              ["only"]
              [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `Units.val_inv_eq_inv_val)] "]")]
              ["using" (Term.app `inv_mem_iff.mp [`hk])]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.lift
         "lift"
         `k
         "to"
         (Algebra.Group.Units.«term_ˣ» `𝕜 "ˣ")
         ["using" (Term.app `is_unit_iff_ne_zero.mpr [(Term.app `ne_zero_of_mem_of_unit [`hk])])]
         [])
        []
        (Std.Tactic.Simpa.simpa
         "simpa"
         []
         []
         (Std.Tactic.Simpa.simpaArgsRest
          []
          []
          ["only"]
          [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `Units.val_inv_eq_inv_val)] "]")]
          ["using" (Term.app `inv_mem_iff.mp [`hk])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        ["only"]
        [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `Units.val_inv_eq_inv_val)] "]")]
        ["using" (Term.app `inv_mem_iff.mp [`hk])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `inv_mem_iff.mp [`hk])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hk
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `inv_mem_iff.mp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Units.val_inv_eq_inv_val
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.lift
       "lift"
       `k
       "to"
       (Algebra.Group.Units.«term_ˣ» `𝕜 "ˣ")
       ["using" (Term.app `is_unit_iff_ne_zero.mpr [(Term.app `ne_zero_of_mem_of_unit [`hk])])]
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `is_unit_iff_ne_zero.mpr [(Term.app `ne_zero_of_mem_of_unit [`hk])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ne_zero_of_mem_of_unit [`hk])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hk
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ne_zero_of_mem_of_unit
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `ne_zero_of_mem_of_unit [`hk])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_unit_iff_ne_zero.mpr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Units.«term_ˣ» `𝕜 "ˣ")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝕜
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.mem_inv)] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`hk] []))])
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec ":" («term_≠_» `k "≠" (num "0")))]
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
                 ["only"]
                 [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `inv_inv)] "]")]
                 ["using"
                  (Term.app `inv_ne_zero [(Term.app `ne_zero_of_mem_of_unit [`hk])])]))]))))))
        []
        (Tactic.lift
         "lift"
         `k
         "to"
         (Algebra.Group.Units.«term_ˣ» `𝕜 "ˣ")
         ["using" (Term.app `is_unit_iff_ne_zero.mpr [`this])]
         [])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            [(patternIgnore (token.«← » "←"))]
            (Term.app `Units.val_inv_eq_inv_val [`k]))]
          "]")
         [(Tactic.location "at" (Tactic.locationHyp [`hk] []))])
        []
        (Tactic.exact "exact" (Term.app `inv_mem_iff.mp [`hk]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `inv_mem_iff.mp [`hk]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `inv_mem_iff.mp [`hk])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hk
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `inv_mem_iff.mp
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
          (Term.app `Units.val_inv_eq_inv_val [`k]))]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`hk] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Units.val_inv_eq_inv_val [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Units.val_inv_eq_inv_val
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.lift
       "lift"
       `k
       "to"
       (Algebra.Group.Units.«term_ˣ» `𝕜 "ˣ")
       ["using" (Term.app `is_unit_iff_ne_zero.mpr [`this])]
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `is_unit_iff_ne_zero.mpr [`this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_unit_iff_ne_zero.mpr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Units.«term_ˣ» `𝕜 "ˣ")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝕜
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec ":" («term_≠_» `k "≠" (num "0")))]
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
               ["only"]
               [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `inv_inv)] "]")]
               ["using" (Term.app `inv_ne_zero [(Term.app `ne_zero_of_mem_of_unit [`hk])])]))]))))))
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
            ["only"]
            [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `inv_inv)] "]")]
            ["using" (Term.app `inv_ne_zero [(Term.app `ne_zero_of_mem_of_unit [`hk])])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        ["only"]
        [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `inv_inv)] "]")]
        ["using" (Term.app `inv_ne_zero [(Term.app `ne_zero_of_mem_of_unit [`hk])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `inv_ne_zero [(Term.app `ne_zero_of_mem_of_unit [`hk])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ne_zero_of_mem_of_unit [`hk])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hk
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ne_zero_of_mem_of_unit
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `ne_zero_of_mem_of_unit [`hk])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `inv_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inv_inv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» `k "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.mem_inv)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`hk] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.mem_inv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `Set.eq_of_subset_of_subset
        [(Term.fun "fun" (Term.basicFun [`k `hk] [] "=>" (Term.hole "_")))
         (Term.fun "fun" (Term.basicFun [`k `hk] [] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Set.eq_of_subset_of_subset
       [(Term.fun "fun" (Term.basicFun [`k `hk] [] "=>" (Term.hole "_")))
        (Term.fun "fun" (Term.basicFun [`k `hk] [] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`k `hk] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.fun "fun" (Term.basicFun [`k `hk] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun "fun" (Term.basicFun [`k `hk] [] "=>" (Term.hole "_")))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Set.eq_of_subset_of_subset
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       («term_⁻¹»
        (Term.app
         (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ")
         [(Term.typeAscription "(" `a ":" [`A] ")")])
        "⁻¹")
       "="
       (Term.app
        (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ")
        [(Term.typeAscription "(" (coeNotation "↑" («term_⁻¹» `a "⁻¹")) ":" [`A] ")")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ")
       [(Term.typeAscription "(" (coeNotation "↑" («term_⁻¹» `a "⁻¹")) ":" [`A] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" (coeNotation "↑" («term_⁻¹» `a "⁻¹")) ":" [`A] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (coeNotation "↑" («term_⁻¹» `a "⁻¹"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⁻¹» `a "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Algebra.Algebra.Spectrum.termσ_2', expected 'spectrum.Algebra.Algebra.Spectrum.termσ_2._@.Algebra.Algebra.Spectrum._hyg.2759'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected
  theorem
    map_inv
    ( a : A ˣ ) : σ ( a : A ) ⁻¹ = σ ( ↑ a ⁻¹ : A )
    :=
      by
        refine' Set.eq_of_subset_of_subset fun k hk => _ fun k hk => _
          ·
            rw [ Set.mem_inv ] at hk
              have : k ≠ 0 := by simpa only [ inv_inv ] using inv_ne_zero ne_zero_of_mem_of_unit hk
              lift k to 𝕜 ˣ using is_unit_iff_ne_zero.mpr this
              rw [ ← Units.val_inv_eq_inv_val k ] at hk
              exact inv_mem_iff.mp hk
          ·
            lift k to 𝕜 ˣ using is_unit_iff_ne_zero.mpr ne_zero_of_mem_of_unit hk
              simpa only [ Units.val_inv_eq_inv_val ] using inv_mem_iff.mp hk
#align spectrum.map_inv spectrum.map_inv

open Polynomial

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Half of the spectral mapping theorem for polynomials. We prove it separately\nbecause it holds over any field, whereas `spectrum.map_polynomial_aeval_of_degree_pos` and\n`spectrum.map_polynomial_aeval_of_nonempty` need the field to be algebraically closed. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `subset_polynomial_aeval [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" `A] [] ")")
        (Term.explicitBinder
         "("
         [`p]
         [":" (Polynomial.Data.Polynomial.Basic.polynomial `𝕜 "[X]")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_⊆_»
         (Set.Data.Set.Image.term_''_
          (Term.fun "fun" (Term.basicFun [`k] [] "=>" (Term.app `eval [`k `p])))
          " '' "
          (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [`a]))
         "⊆"
         (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [(Term.app `aeval [`a `p])]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.rintro
            "rintro"
            [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.ignore "_"))
             (Std.Tactic.RCases.rintroPat.one
              (Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hk)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                 [])]
               "⟩"))]
            [])
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `q
              []
              []
              ":="
              («term_-_» (Term.app `C [(Term.app `eval [`k `p])]) "-" `p))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hroot []]
              [(Term.typeSpec ":" (Term.app `is_root [`q `k]))]
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
                    [(Tactic.simpLemma [] [] `eval_C)
                     ","
                     (Tactic.simpLemma [] [] `eval_sub)
                     ","
                     (Tactic.simpLemma [] [] `sub_self)
                     ","
                     (Tactic.simpLemma [] [] `is_root.def)]
                    "]"]
                   [])]))))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_div_eq_iff_is_root)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `neg_mul_neg)
              ","
              (Tactic.rwRule [] `neg_sub)]
             "]")
            [(Tactic.location "at" (Tactic.locationHyp [`hroot] []))])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`aeval_q_eq []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 («term_-_»
                  (Term.app
                   (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_2» "↑ₐ")
                   [(Term.app `eval [`k `p])])
                  "-"
                  (Term.app `aeval [`a `p]))
                 "="
                 (Term.app `aeval [`a `q])))]
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
                    [(Tactic.simpLemma [] [] `aeval_C)
                     ","
                     (Tactic.simpLemma [] [] `AlgHom.map_sub)
                     ","
                     (Tactic.simpLemma [] [] `sub_left_inj)]
                    "]"]
                   [])]))))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `mem_iff)
              ","
              (Tactic.rwRule [] `aeval_q_eq)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hroot)
              ","
              (Tactic.rwRule [] `aeval_mul)]
             "]")
            [])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hcomm []]
              []
              ":="
              (Term.app
               (Term.proj
                (Term.app
                 `Commute.all
                 [(«term_-_» (Term.app `C [`k]) "-" `X)
                  («term-_» "-" («term_/_» `q "/" («term_-_» `X "-" (Term.app `C [`k]))))])
                "."
                `map)
               [(Term.app `aeval [`a])]))))
           []
           (Tactic.apply
            "apply"
            (Term.app
             `mt
             [(Term.fun
               "fun"
               (Term.basicFun
                [`h]
                []
                "=>"
                (Term.proj (Term.app `hcomm.is_unit_mul_iff.mp [`h]) "." (fieldIdx "1"))))]))
           []
           (Std.Tactic.Simpa.simpa
            "simpa"
            []
            []
            (Std.Tactic.Simpa.simpaArgsRest
             []
             []
             ["only"]
             [(Tactic.simpArgs
               "["
               [(Tactic.simpLemma [] [] `aeval_X)
                ","
                (Tactic.simpLemma [] [] `aeval_C)
                ","
                (Tactic.simpLemma [] [] `AlgHom.map_sub)]
               "]")]
             ["using" `hk]))])))
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
         [(Std.Tactic.rintro
           "rintro"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.ignore "_"))
            (Std.Tactic.RCases.rintroPat.one
             (Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hk)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                [])]
              "⟩"))]
           [])
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `q
             []
             []
             ":="
             («term_-_» (Term.app `C [(Term.app `eval [`k `p])]) "-" `p))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hroot []]
             [(Term.typeSpec ":" (Term.app `is_root [`q `k]))]
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
                   [(Tactic.simpLemma [] [] `eval_C)
                    ","
                    (Tactic.simpLemma [] [] `eval_sub)
                    ","
                    (Tactic.simpLemma [] [] `sub_self)
                    ","
                    (Tactic.simpLemma [] [] `is_root.def)]
                   "]"]
                  [])]))))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_div_eq_iff_is_root)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `neg_mul_neg)
             ","
             (Tactic.rwRule [] `neg_sub)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`hroot] []))])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`aeval_q_eq []]
             [(Term.typeSpec
               ":"
               («term_=_»
                («term_-_»
                 (Term.app
                  (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_2» "↑ₐ")
                  [(Term.app `eval [`k `p])])
                 "-"
                 (Term.app `aeval [`a `p]))
                "="
                (Term.app `aeval [`a `q])))]
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
                   [(Tactic.simpLemma [] [] `aeval_C)
                    ","
                    (Tactic.simpLemma [] [] `AlgHom.map_sub)
                    ","
                    (Tactic.simpLemma [] [] `sub_left_inj)]
                   "]"]
                  [])]))))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `mem_iff)
             ","
             (Tactic.rwRule [] `aeval_q_eq)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hroot)
             ","
             (Tactic.rwRule [] `aeval_mul)]
            "]")
           [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hcomm []]
             []
             ":="
             (Term.app
              (Term.proj
               (Term.app
                `Commute.all
                [(«term_-_» (Term.app `C [`k]) "-" `X)
                 («term-_» "-" («term_/_» `q "/" («term_-_» `X "-" (Term.app `C [`k]))))])
               "."
               `map)
              [(Term.app `aeval [`a])]))))
          []
          (Tactic.apply
           "apply"
           (Term.app
            `mt
            [(Term.fun
              "fun"
              (Term.basicFun
               [`h]
               []
               "=>"
               (Term.proj (Term.app `hcomm.is_unit_mul_iff.mp [`h]) "." (fieldIdx "1"))))]))
          []
          (Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            ["only"]
            [(Tactic.simpArgs
              "["
              [(Tactic.simpLemma [] [] `aeval_X)
               ","
               (Tactic.simpLemma [] [] `aeval_C)
               ","
               (Tactic.simpLemma [] [] `AlgHom.map_sub)]
              "]")]
            ["using" `hk]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        ["only"]
        [(Tactic.simpArgs
          "["
          [(Tactic.simpLemma [] [] `aeval_X)
           ","
           (Tactic.simpLemma [] [] `aeval_C)
           ","
           (Tactic.simpLemma [] [] `AlgHom.map_sub)]
          "]")]
        ["using" `hk]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `AlgHom.map_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `aeval_C
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `aeval_X
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply
       "apply"
       (Term.app
        `mt
        [(Term.fun
          "fun"
          (Term.basicFun
           [`h]
           []
           "=>"
           (Term.proj (Term.app `hcomm.is_unit_mul_iff.mp [`h]) "." (fieldIdx "1"))))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mt
       [(Term.fun
         "fun"
         (Term.basicFun
          [`h]
          []
          "=>"
          (Term.proj (Term.app `hcomm.is_unit_mul_iff.mp [`h]) "." (fieldIdx "1"))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`h]
        []
        "=>"
        (Term.proj (Term.app `hcomm.is_unit_mul_iff.mp [`h]) "." (fieldIdx "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `hcomm.is_unit_mul_iff.mp [`h]) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `hcomm.is_unit_mul_iff.mp [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hcomm.is_unit_mul_iff.mp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `hcomm.is_unit_mul_iff.mp [`h])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hcomm []]
         []
         ":="
         (Term.app
          (Term.proj
           (Term.app
            `Commute.all
            [(«term_-_» (Term.app `C [`k]) "-" `X)
             («term-_» "-" («term_/_» `q "/" («term_-_» `X "-" (Term.app `C [`k]))))])
           "."
           `map)
          [(Term.app `aeval [`a])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app
         `Commute.all
         [(«term_-_» (Term.app `C [`k]) "-" `X)
          («term-_» "-" («term_/_» `q "/" («term_-_» `X "-" (Term.app `C [`k]))))])
        "."
        `map)
       [(Term.app `aeval [`a])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `aeval [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `aeval
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `aeval [`a]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        `Commute.all
        [(«term_-_» (Term.app `C [`k]) "-" `X)
         («term-_» "-" («term_/_» `q "/" («term_-_» `X "-" (Term.app `C [`k]))))])
       "."
       `map)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `Commute.all
       [(«term_-_» (Term.app `C [`k]) "-" `X)
        («term-_» "-" («term_/_» `q "/" («term_-_» `X "-" (Term.app `C [`k]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" («term_/_» `q "/" («term_-_» `X "-" (Term.app `C [`k]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» `q "/" («term_-_» `X "-" (Term.app `C [`k])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» `X "-" (Term.app `C [`k]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `C [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_-_» `X "-" (Term.app `C [`k]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `q
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 75 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_/_» `q "/" (Term.paren "(" («term_-_» `X "-" (Term.app `C [`k])) ")"))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term-_»
      "-"
      (Term.paren
       "("
       («term_/_» `q "/" (Term.paren "(" («term_-_» `X "-" (Term.app `C [`k])) ")"))
       ")"))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_-_» (Term.app `C [`k]) "-" `X)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `C [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `C
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_-_» (Term.app `C [`k]) "-" `X)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Commute.all
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `Commute.all
      [(Term.paren "(" («term_-_» (Term.app `C [`k]) "-" `X) ")")
       (Term.paren
        "("
        («term-_»
         "-"
         (Term.paren
          "("
          («term_/_» `q "/" (Term.paren "(" («term_-_» `X "-" (Term.app `C [`k])) ")"))
          ")"))
        ")")])
     ")")
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
        [(Tactic.rwRule [] `mem_iff)
         ","
         (Tactic.rwRule [] `aeval_q_eq)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hroot)
         ","
         (Tactic.rwRule [] `aeval_mul)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `aeval_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hroot
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `aeval_q_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`aeval_q_eq []]
         [(Term.typeSpec
           ":"
           («term_=_»
            («term_-_»
             (Term.app
              (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_2» "↑ₐ")
              [(Term.app `eval [`k `p])])
             "-"
             (Term.app `aeval [`a `p]))
            "="
            (Term.app `aeval [`a `q])))]
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
               [(Tactic.simpLemma [] [] `aeval_C)
                ","
                (Tactic.simpLemma [] [] `AlgHom.map_sub)
                ","
                (Tactic.simpLemma [] [] `sub_left_inj)]
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
            [(Tactic.simpLemma [] [] `aeval_C)
             ","
             (Tactic.simpLemma [] [] `AlgHom.map_sub)
             ","
             (Tactic.simpLemma [] [] `sub_left_inj)]
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
        [(Tactic.simpLemma [] [] `aeval_C)
         ","
         (Tactic.simpLemma [] [] `AlgHom.map_sub)
         ","
         (Tactic.simpLemma [] [] `sub_left_inj)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_left_inj
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `AlgHom.map_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `aeval_C
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       («term_-_»
        (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_2» "↑ₐ") [(Term.app `eval [`k `p])])
        "-"
        (Term.app `aeval [`a `p]))
       "="
       (Term.app `aeval [`a `q]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `aeval [`a `q])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `q
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `aeval
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_-_»
       (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_2» "↑ₐ") [(Term.app `eval [`k `p])])
       "-"
       (Term.app `aeval [`a `p]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `aeval [`a `p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `aeval
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_2» "↑ₐ") [(Term.app `eval [`k `p])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `eval [`k `p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eval
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `eval [`k `p]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_2» "↑ₐ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_2»', expected 'spectrum.Algebra.Algebra.Spectrum.term↑ₐ_2._@.Algebra.Algebra.Spectrum._hyg.3255'
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
    Half of the spectral mapping theorem for polynomials. We prove it separately
    because it holds over any field, whereas `spectrum.map_polynomial_aeval_of_degree_pos` and
    `spectrum.map_polynomial_aeval_of_nonempty` need the field to be algebraically closed. -/
  theorem
    subset_polynomial_aeval
    ( a : A ) ( p : 𝕜 [X] ) : fun k => eval k p '' σ a ⊆ σ aeval a p
    :=
      by
        rintro _ ⟨ k , hk , rfl ⟩
          let q := C eval k p - p
          have hroot : is_root q k := by simp only [ eval_C , eval_sub , sub_self , is_root.def ]
          rw [ ← mul_div_eq_iff_is_root , ← neg_mul_neg , neg_sub ] at hroot
          have
            aeval_q_eq
              : ↑ₐ eval k p - aeval a p = aeval a q
              :=
              by simp only [ aeval_C , AlgHom.map_sub , sub_left_inj ]
          rw [ mem_iff , aeval_q_eq , ← hroot , aeval_mul ]
          have hcomm := Commute.all C k - X - q / X - C k . map aeval a
          apply mt fun h => hcomm.is_unit_mul_iff.mp h . 1
          simpa only [ aeval_X , aeval_C , AlgHom.map_sub ] using hk
#align spectrum.subset_polynomial_aeval spectrum.subset_polynomial_aeval

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The *spectral mapping theorem* for polynomials.  Note: the assumption `degree p > 0`\nis necessary in case `σ a = ∅`, for then the left-hand side is `∅` and the right-hand side,\nassuming `[nontrivial A]`, is `{k}` where `p = polynomial.C k`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `map_polynomial_aeval_of_degree_pos [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `IsAlgClosed [`𝕜]) "]")
        (Term.explicitBinder "(" [`a] [":" `A] [] ")")
        (Term.explicitBinder
         "("
         [`p]
         [":" (Polynomial.Data.Polynomial.Basic.polynomial `𝕜 "[X]")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hdeg]
         [":" («term_<_» (num "0") "<" (Term.app `degree [`p]))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [(Term.app `aeval [`a `p])])
         "="
         (Set.Data.Set.Image.term_''_
          (Term.fun "fun" (Term.basicFun [`k] [] "=>" (Term.app `eval [`k `p])))
          " '' "
          (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [`a])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.app
             `Set.eq_of_subset_of_subset
             [(Term.fun "fun" (Term.basicFun [`k `hk] [] "=>" (Term.hole "_")))
              (Term.app `subset_polynomial_aeval [`a `p])]))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hprod []]
              []
              ":="
              (Term.app
               `eq_prod_roots_of_splits_id
               [(Term.app `IsAlgClosed.splits [(«term_-_» (Term.app `C [`k]) "-" `p)])]))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`h_ne []]
              [(Term.typeSpec ":" («term_≠_» («term_-_» (Term.app `C [`k]) "-" `p) "≠" (num "0")))]
              ":="
              (Term.app
               `ne_zero_of_degree_gt
               [(Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Std.Tactic.tacticRwa__
                     "rwa"
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule
                        []
                        (Term.app
                         `degree_sub_eq_right_of_degree_lt
                         [(Term.app `lt_of_le_of_lt [`degree_C_le `hdeg])]))]
                      "]")
                     [])])))]))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl [`lead_ne []] [] ":=" (Term.app `leading_coeff_ne_zero.mpr [`h_ne]))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`lead_unit []]
              []
              ":="
              (Term.proj
               (Term.app
                `Units.map
                [(Term.proj (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_2» "↑ₐ") "." `toMonoidHom)
                 (Term.app `Units.mk0 [(Term.hole "_") `lead_ne])])
               "."
               `IsUnit))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`p_a_eq []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Term.app `aeval [`a («term_-_» (Term.app `C [`k]) "-" `p)])
                 "="
                 («term_-_»
                  (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_2» "↑ₐ") [`k])
                  "-"
                  (Term.app `aeval [`a `p]))))]
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
                    [(Tactic.simpLemma [] [] `aeval_C)
                     ","
                     (Tactic.simpLemma [] [] `AlgHom.map_sub)
                     ","
                     (Tactic.simpLemma [] [] `sub_left_inj)]
                    "]"]
                   [])]))))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `mem_iff)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `p_a_eq)
              ","
              (Tactic.rwRule [] `hprod)
              ","
              (Tactic.rwRule [] `aeval_mul)
              ","
              (Tactic.rwRule
               []
               (Term.proj
                (Term.app
                 (Term.proj (Term.app `Commute.all [(Term.hole "_") (Term.hole "_")]) "." `map)
                 [(Term.app `aeval [`a])])
                "."
                `is_unit_mul_iff))
              ","
              (Tactic.rwRule [] `aeval_C)]
             "]")
            [(Tactic.location "at" (Tactic.locationHyp [`hk] []))])
           []
           (Mathlib.Tactic.tacticReplace_
            "replace"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hk []]
              []
              ":="
              (Term.app
               `exists_mem_of_not_is_unit_aeval_prod
               [`h_ne (Term.app `not_and.mp [`hk `lead_unit])]))))
           []
           (Std.Tactic.rcases
            "rcases"
            [(Tactic.casesTarget [] `hk)]
            ["with"
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r_mem)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r_ev)])
                   [])]
                 "⟩")])
              [])])
           []
           (Tactic.exact
            "exact"
            (Term.anonymousCtor
             "⟨"
             [`r
              ","
              `r_mem
              ","
              (Term.app
               `symm
               [(Term.byTactic
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
                      [(Tactic.simpArgs
                        "["
                        [(Tactic.simpLemma [] [] `eval_sub)
                         ","
                         (Tactic.simpLemma [] [] `eval_C)
                         ","
                         (Tactic.simpLemma [] [] `sub_eq_zero)]
                        "]")]
                      ["using" `r_ev]))])))])]
             "⟩"))])))
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
            `Set.eq_of_subset_of_subset
            [(Term.fun "fun" (Term.basicFun [`k `hk] [] "=>" (Term.hole "_")))
             (Term.app `subset_polynomial_aeval [`a `p])]))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hprod []]
             []
             ":="
             (Term.app
              `eq_prod_roots_of_splits_id
              [(Term.app `IsAlgClosed.splits [(«term_-_» (Term.app `C [`k]) "-" `p)])]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h_ne []]
             [(Term.typeSpec ":" («term_≠_» («term_-_» (Term.app `C [`k]) "-" `p) "≠" (num "0")))]
             ":="
             (Term.app
              `ne_zero_of_degree_gt
              [(Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Std.Tactic.tacticRwa__
                    "rwa"
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule
                       []
                       (Term.app
                        `degree_sub_eq_right_of_degree_lt
                        [(Term.app `lt_of_le_of_lt [`degree_C_le `hdeg])]))]
                     "]")
                    [])])))]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl [`lead_ne []] [] ":=" (Term.app `leading_coeff_ne_zero.mpr [`h_ne]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`lead_unit []]
             []
             ":="
             (Term.proj
              (Term.app
               `Units.map
               [(Term.proj (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_2» "↑ₐ") "." `toMonoidHom)
                (Term.app `Units.mk0 [(Term.hole "_") `lead_ne])])
              "."
              `IsUnit))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`p_a_eq []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.app `aeval [`a («term_-_» (Term.app `C [`k]) "-" `p)])
                "="
                («term_-_»
                 (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_2» "↑ₐ") [`k])
                 "-"
                 (Term.app `aeval [`a `p]))))]
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
                   [(Tactic.simpLemma [] [] `aeval_C)
                    ","
                    (Tactic.simpLemma [] [] `AlgHom.map_sub)
                    ","
                    (Tactic.simpLemma [] [] `sub_left_inj)]
                   "]"]
                  [])]))))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `mem_iff)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `p_a_eq)
             ","
             (Tactic.rwRule [] `hprod)
             ","
             (Tactic.rwRule [] `aeval_mul)
             ","
             (Tactic.rwRule
              []
              (Term.proj
               (Term.app
                (Term.proj (Term.app `Commute.all [(Term.hole "_") (Term.hole "_")]) "." `map)
                [(Term.app `aeval [`a])])
               "."
               `is_unit_mul_iff))
             ","
             (Tactic.rwRule [] `aeval_C)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`hk] []))])
          []
          (Mathlib.Tactic.tacticReplace_
           "replace"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hk []]
             []
             ":="
             (Term.app
              `exists_mem_of_not_is_unit_aeval_prod
              [`h_ne (Term.app `not_and.mp [`hk `lead_unit])]))))
          []
          (Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] `hk)]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r_mem)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r_ev)])
                  [])]
                "⟩")])
             [])])
          []
          (Tactic.exact
           "exact"
           (Term.anonymousCtor
            "⟨"
            [`r
             ","
             `r_mem
             ","
             (Term.app
              `symm
              [(Term.byTactic
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
                     [(Tactic.simpArgs
                       "["
                       [(Tactic.simpLemma [] [] `eval_sub)
                        ","
                        (Tactic.simpLemma [] [] `eval_C)
                        ","
                        (Tactic.simpLemma [] [] `sub_eq_zero)]
                       "]")]
                     ["using" `r_ev]))])))])]
            "⟩"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.anonymousCtor
        "⟨"
        [`r
         ","
         `r_mem
         ","
         (Term.app
          `symm
          [(Term.byTactic
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
                 [(Tactic.simpArgs
                   "["
                   [(Tactic.simpLemma [] [] `eval_sub)
                    ","
                    (Tactic.simpLemma [] [] `eval_C)
                    ","
                    (Tactic.simpLemma [] [] `sub_eq_zero)]
                   "]")]
                 ["using" `r_ev]))])))])]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`r
        ","
        `r_mem
        ","
        (Term.app
         `symm
         [(Term.byTactic
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
                [(Tactic.simpArgs
                  "["
                  [(Tactic.simpLemma [] [] `eval_sub)
                   ","
                   (Tactic.simpLemma [] [] `eval_C)
                   ","
                   (Tactic.simpLemma [] [] `sub_eq_zero)]
                  "]")]
                ["using" `r_ev]))])))])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `symm
       [(Term.byTactic
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
              [(Tactic.simpArgs
                "["
                [(Tactic.simpLemma [] [] `eval_sub)
                 ","
                 (Tactic.simpLemma [] [] `eval_C)
                 ","
                 (Tactic.simpLemma [] [] `sub_eq_zero)]
                "]")]
              ["using" `r_ev]))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
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
            [(Tactic.simpArgs
              "["
              [(Tactic.simpLemma [] [] `eval_sub)
               ","
               (Tactic.simpLemma [] [] `eval_C)
               ","
               (Tactic.simpLemma [] [] `sub_eq_zero)]
              "]")]
            ["using" `r_ev]))])))
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
        [(Tactic.simpArgs
          "["
          [(Tactic.simpLemma [] [] `eval_sub)
           ","
           (Tactic.simpLemma [] [] `eval_C)
           ","
           (Tactic.simpLemma [] [] `sub_eq_zero)]
          "]")]
        ["using" `r_ev]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r_ev
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_eq_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eval_C
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eval_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
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
           [(Tactic.simpArgs
             "["
             [(Tactic.simpLemma [] [] `eval_sub)
              ","
              (Tactic.simpLemma [] [] `eval_C)
              ","
              (Tactic.simpLemma [] [] `sub_eq_zero)]
             "]")]
           ["using" `r_ev]))])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `symm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r_mem
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] `hk)]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r_mem)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r_ev)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticReplace_
       "replace"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hk []]
         []
         ":="
         (Term.app
          `exists_mem_of_not_is_unit_aeval_prod
          [`h_ne (Term.app `not_and.mp [`hk `lead_unit])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `exists_mem_of_not_is_unit_aeval_prod
       [`h_ne (Term.app `not_and.mp [`hk `lead_unit])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `not_and.mp [`hk `lead_unit])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lead_unit
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hk
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `not_and.mp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `not_and.mp [`hk `lead_unit])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h_ne
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `exists_mem_of_not_is_unit_aeval_prod
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
        [(Tactic.rwRule [] `mem_iff)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `p_a_eq)
         ","
         (Tactic.rwRule [] `hprod)
         ","
         (Tactic.rwRule [] `aeval_mul)
         ","
         (Tactic.rwRule
          []
          (Term.proj
           (Term.app
            (Term.proj (Term.app `Commute.all [(Term.hole "_") (Term.hole "_")]) "." `map)
            [(Term.app `aeval [`a])])
           "."
           `is_unit_mul_iff))
         ","
         (Tactic.rwRule [] `aeval_C)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`hk] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `aeval_C
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        (Term.proj (Term.app `Commute.all [(Term.hole "_") (Term.hole "_")]) "." `map)
        [(Term.app `aeval [`a])])
       "."
       `is_unit_mul_iff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj (Term.app `Commute.all [(Term.hole "_") (Term.hole "_")]) "." `map)
       [(Term.app `aeval [`a])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `aeval [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `aeval
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `aeval [`a]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `Commute.all [(Term.hole "_") (Term.hole "_")]) "." `map)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Commute.all [(Term.hole "_") (Term.hole "_")])
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
      `Commute.all
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Commute.all [(Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj
       (Term.paren "(" (Term.app `Commute.all [(Term.hole "_") (Term.hole "_")]) ")")
       "."
       `map)
      [(Term.paren "(" (Term.app `aeval [`a]) ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `aeval_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hprod
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p_a_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`p_a_eq []]
         [(Term.typeSpec
           ":"
           («term_=_»
            (Term.app `aeval [`a («term_-_» (Term.app `C [`k]) "-" `p)])
            "="
            («term_-_»
             (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_2» "↑ₐ") [`k])
             "-"
             (Term.app `aeval [`a `p]))))]
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
               [(Tactic.simpLemma [] [] `aeval_C)
                ","
                (Tactic.simpLemma [] [] `AlgHom.map_sub)
                ","
                (Tactic.simpLemma [] [] `sub_left_inj)]
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
            [(Tactic.simpLemma [] [] `aeval_C)
             ","
             (Tactic.simpLemma [] [] `AlgHom.map_sub)
             ","
             (Tactic.simpLemma [] [] `sub_left_inj)]
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
        [(Tactic.simpLemma [] [] `aeval_C)
         ","
         (Tactic.simpLemma [] [] `AlgHom.map_sub)
         ","
         (Tactic.simpLemma [] [] `sub_left_inj)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_left_inj
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `AlgHom.map_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `aeval_C
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app `aeval [`a («term_-_» (Term.app `C [`k]) "-" `p)])
       "="
       («term_-_»
        (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_2» "↑ₐ") [`k])
        "-"
        (Term.app `aeval [`a `p])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_»
       (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_2» "↑ₐ") [`k])
       "-"
       (Term.app `aeval [`a `p]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `aeval [`a `p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `aeval
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_2» "↑ₐ") [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_2» "↑ₐ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Algebra.Algebra.Spectrum.«term↑ₐ_2»', expected 'spectrum.Algebra.Algebra.Spectrum.term↑ₐ_2._@.Algebra.Algebra.Spectrum._hyg.3255'
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
    The *spectral mapping theorem* for polynomials.  Note: the assumption `degree p > 0`
    is necessary in case `σ a = ∅`, for then the left-hand side is `∅` and the right-hand side,
    assuming `[nontrivial A]`, is `{k}` where `p = polynomial.C k`. -/
  theorem
    map_polynomial_aeval_of_degree_pos
    [ IsAlgClosed 𝕜 ] ( a : A ) ( p : 𝕜 [X] ) ( hdeg : 0 < degree p )
      : σ aeval a p = fun k => eval k p '' σ a
    :=
      by
        refine' Set.eq_of_subset_of_subset fun k hk => _ subset_polynomial_aeval a p
          have hprod := eq_prod_roots_of_splits_id IsAlgClosed.splits C k - p
          have
            h_ne
              : C k - p ≠ 0
              :=
              ne_zero_of_degree_gt
                by rwa [ degree_sub_eq_right_of_degree_lt lt_of_le_of_lt degree_C_le hdeg ]
          have lead_ne := leading_coeff_ne_zero.mpr h_ne
          have lead_unit := Units.map ↑ₐ . toMonoidHom Units.mk0 _ lead_ne . IsUnit
          have
            p_a_eq
              : aeval a C k - p = ↑ₐ k - aeval a p
              :=
              by simp only [ aeval_C , AlgHom.map_sub , sub_left_inj ]
          rw
            [
              mem_iff
                ,
                ← p_a_eq
                ,
                hprod
                ,
                aeval_mul
                ,
                Commute.all _ _ . map aeval a . is_unit_mul_iff
                ,
                aeval_C
              ]
            at hk
          replace hk := exists_mem_of_not_is_unit_aeval_prod h_ne not_and.mp hk lead_unit
          rcases hk with ⟨ r , r_mem , r_ev ⟩
          exact ⟨ r , r_mem , symm by simpa [ eval_sub , eval_C , sub_eq_zero ] using r_ev ⟩
#align spectrum.map_polynomial_aeval_of_degree_pos spectrum.map_polynomial_aeval_of_degree_pos

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "In this version of the spectral mapping theorem, we assume the spectrum\nis nonempty instead of assuming the degree of the polynomial is positive. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `map_polynomial_aeval_of_nonempty [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `IsAlgClosed [`𝕜]) "]")
        (Term.explicitBinder "(" [`a] [":" `A] [] ")")
        (Term.explicitBinder
         "("
         [`p]
         [":" (Polynomial.Data.Polynomial.Basic.polynomial `𝕜 "[X]")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hnon]
         [":"
          (Term.proj (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [`a]) "." `Nonempty)]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [(Term.app `aeval [`a `p])])
         "="
         (Set.Data.Set.Image.term_''_
          (Term.fun "fun" (Term.basicFun [`k] [] "=>" (Term.app `eval [`k `p])))
          " '' "
          (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [`a])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Mathlib.Tactic.Nontriviality.nontriviality "nontriviality" [`A] [])
           []
           (Tactic.refine'
            "refine'"
            (Term.app
             `Or.elim
             [(Term.app `le_or_gt [(Term.app `degree [`p]) (num "0")])
              (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
              (Term.app `map_polynomial_aeval_of_degree_pos [`a `p])]))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] (Term.app `eq_C_of_degree_le_zero [`h]))]
               "]")
              [])
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `Set.image_congr)
                ","
                (Tactic.simpLemma [] [] `eval_C)
                ","
                (Tactic.simpLemma [] [] `aeval_C)
                ","
                (Tactic.simpLemma [] [] `scalar_eq)
                ","
                (Tactic.simpLemma [] [] (Term.app `Set.Nonempty.image_const [`hnon]))]
               "]"]
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
         [(Mathlib.Tactic.Nontriviality.nontriviality "nontriviality" [`A] [])
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            `Or.elim
            [(Term.app `le_or_gt [(Term.app `degree [`p]) (num "0")])
             (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
             (Term.app `map_polynomial_aeval_of_degree_pos [`a `p])]))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `eq_C_of_degree_le_zero [`h]))] "]")
             [])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `Set.image_congr)
               ","
               (Tactic.simpLemma [] [] `eval_C)
               ","
               (Tactic.simpLemma [] [] `aeval_C)
               ","
               (Tactic.simpLemma [] [] `scalar_eq)
               ","
               (Tactic.simpLemma [] [] (Term.app `Set.Nonempty.image_const [`hnon]))]
              "]"]
             [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `eq_C_of_degree_le_zero [`h]))] "]")
         [])
        []
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `Set.image_congr)
           ","
           (Tactic.simpLemma [] [] `eval_C)
           ","
           (Tactic.simpLemma [] [] `aeval_C)
           ","
           (Tactic.simpLemma [] [] `scalar_eq)
           ","
           (Tactic.simpLemma [] [] (Term.app `Set.Nonempty.image_const [`hnon]))]
          "]"]
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `Set.image_congr)
         ","
         (Tactic.simpLemma [] [] `eval_C)
         ","
         (Tactic.simpLemma [] [] `aeval_C)
         ","
         (Tactic.simpLemma [] [] `scalar_eq)
         ","
         (Tactic.simpLemma [] [] (Term.app `Set.Nonempty.image_const [`hnon]))]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Set.Nonempty.image_const [`hnon])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hnon
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Set.Nonempty.image_const
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `scalar_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `aeval_C
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eval_C
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.image_congr
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `eq_C_of_degree_le_zero [`h]))] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `eq_C_of_degree_le_zero [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eq_C_of_degree_le_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `Or.elim
        [(Term.app `le_or_gt [(Term.app `degree [`p]) (num "0")])
         (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
         (Term.app `map_polynomial_aeval_of_degree_pos [`a `p])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Or.elim
       [(Term.app `le_or_gt [(Term.app `degree [`p]) (num "0")])
        (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
        (Term.app `map_polynomial_aeval_of_degree_pos [`a `p])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `map_polynomial_aeval_of_degree_pos [`a `p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `map_polynomial_aeval_of_degree_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `map_polynomial_aeval_of_degree_pos [`a `p])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun "fun" (Term.basicFun [`h] [] "=>" (Term.hole "_")))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `le_or_gt [(Term.app `degree [`p]) (num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `degree [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `degree
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `degree [`p]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_or_gt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `le_or_gt [(Term.paren "(" (Term.app `degree [`p]) ")") (num "0")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Or.elim
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.Nontriviality.nontriviality "nontriviality" [`A] [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [(Term.app `aeval [`a `p])])
       "="
       (Set.Data.Set.Image.term_''_
        (Term.fun "fun" (Term.basicFun [`k] [] "=>" (Term.app `eval [`k `p])))
        " '' "
        (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [`a])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Data.Set.Image.term_''_
       (Term.fun "fun" (Term.basicFun [`k] [] "=>" (Term.app `eval [`k `p])))
       " '' "
       (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [`a]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Algebra.Algebra.Spectrum.termσ_2', expected 'spectrum.Algebra.Algebra.Spectrum.termσ_2._@.Algebra.Algebra.Spectrum._hyg.2759'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    In this version of the spectral mapping theorem, we assume the spectrum
    is nonempty instead of assuming the degree of the polynomial is positive. -/
  theorem
    map_polynomial_aeval_of_nonempty
    [ IsAlgClosed 𝕜 ] ( a : A ) ( p : 𝕜 [X] ) ( hnon : σ a . Nonempty )
      : σ aeval a p = fun k => eval k p '' σ a
    :=
      by
        nontriviality A
          refine' Or.elim le_or_gt degree p 0 fun h => _ map_polynomial_aeval_of_degree_pos a p
          ·
            rw [ eq_C_of_degree_le_zero h ]
              simp
                only
                [ Set.image_congr , eval_C , aeval_C , scalar_eq , Set.Nonempty.image_const hnon ]
#align spectrum.map_polynomial_aeval_of_nonempty spectrum.map_polynomial_aeval_of_nonempty

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "A specialization of `spectrum.subset_polynomial_aeval` to monic monomials for convenience. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `pow_image_subset [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" `A] [] ")")
        (Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_⊆_»
         (Set.Data.Set.Image.term_''_
          (Term.fun "fun" (Term.basicFun [`x] [] "=>" («term_^_» `x "^" `n)))
          " '' "
          (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [`a]))
         "⊆"
         (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [(«term_^_» `a "^" `n)]))))
      (Command.declValSimple
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
             ["only"]
             [(Tactic.simpArgs
               "["
               [(Tactic.simpLemma [] [] `eval_pow)
                ","
                (Tactic.simpLemma [] [] `eval_X)
                ","
                (Tactic.simpLemma [] [] `aeval_X_pow)]
               "]")]
             ["using"
              (Term.app
               `subset_polynomial_aeval
               [`a
                (Term.typeAscription
                 "("
                 («term_^_» `X "^" `n)
                 ":"
                 [(Polynomial.Data.Polynomial.Basic.polynomial `𝕜 "[X]")]
                 ")")])]))])))
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
              [(Tactic.simpLemma [] [] `eval_pow)
               ","
               (Tactic.simpLemma [] [] `eval_X)
               ","
               (Tactic.simpLemma [] [] `aeval_X_pow)]
              "]")]
            ["using"
             (Term.app
              `subset_polynomial_aeval
              [`a
               (Term.typeAscription
                "("
                («term_^_» `X "^" `n)
                ":"
                [(Polynomial.Data.Polynomial.Basic.polynomial `𝕜 "[X]")]
                ")")])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        ["only"]
        [(Tactic.simpArgs
          "["
          [(Tactic.simpLemma [] [] `eval_pow)
           ","
           (Tactic.simpLemma [] [] `eval_X)
           ","
           (Tactic.simpLemma [] [] `aeval_X_pow)]
          "]")]
        ["using"
         (Term.app
          `subset_polynomial_aeval
          [`a
           (Term.typeAscription
            "("
            («term_^_» `X "^" `n)
            ":"
            [(Polynomial.Data.Polynomial.Basic.polynomial `𝕜 "[X]")]
            ")")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `subset_polynomial_aeval
       [`a
        (Term.typeAscription
         "("
         («term_^_» `X "^" `n)
         ":"
         [(Polynomial.Data.Polynomial.Basic.polynomial `𝕜 "[X]")]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       («term_^_» `X "^" `n)
       ":"
       [(Polynomial.Data.Polynomial.Basic.polynomial `𝕜 "[X]")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Polynomial.Data.Polynomial.Basic.polynomial `𝕜 "[X]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 9000, term))
      `𝕜
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 9000, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 9000, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `X "^" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `subset_polynomial_aeval
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `aeval_X_pow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eval_X
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eval_pow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_⊆_»
       (Set.Data.Set.Image.term_''_
        (Term.fun "fun" (Term.basicFun [`x] [] "=>" («term_^_» `x "^" `n)))
        " '' "
        (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [`a]))
       "⊆"
       (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [(«term_^_» `a "^" `n)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [(«term_^_» `a "^" `n)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `a "^" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_^_» `a "^" `n) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Algebra.Algebra.Spectrum.termσ_2', expected 'spectrum.Algebra.Algebra.Spectrum.termσ_2._@.Algebra.Algebra.Spectrum._hyg.2759'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- A specialization of `spectrum.subset_polynomial_aeval` to monic monomials for convenience. -/
  theorem
    pow_image_subset
    ( a : A ) ( n : ℕ ) : fun x => x ^ n '' σ a ⊆ σ a ^ n
    :=
      by
        simpa
          only [ eval_pow , eval_X , aeval_X_pow ] using subset_polynomial_aeval a ( X ^ n : 𝕜 [X] )
#align spectrum.pow_image_subset spectrum.pow_image_subset

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "A specialization of `spectrum.map_polynomial_aeval_of_nonempty` to monic monomials for\nconvenience. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `map_pow_of_pos [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `IsAlgClosed [`𝕜]) "]")
        (Term.explicitBinder "(" [`a] [":" `A] [] ")")
        (Term.implicitBinder "{" [`n] [":" (termℕ "ℕ")] "}")
        (Term.explicitBinder "(" [`hn] [":" («term_<_» (num "0") "<" `n)] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [(«term_^_» `a "^" `n)])
         "="
         (Set.Data.Set.Image.term_''_
          (Term.fun "fun" (Term.basicFun [`x] [] "=>" («term_^_» `x "^" `n)))
          " '' "
          (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [`a])))))
      (Command.declValSimple
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
             ["only"]
             [(Tactic.simpArgs
               "["
               [(Tactic.simpLemma [] [] `aeval_X_pow)
                ","
                (Tactic.simpLemma [] [] `eval_pow)
                ","
                (Tactic.simpLemma [] [] `eval_X)]
               "]")]
             ["using"
              (Term.app
               `map_polynomial_aeval_of_degree_pos
               [`a
                (Term.typeAscription
                 "("
                 («term_^_» `X "^" `n)
                 ":"
                 [(Polynomial.Data.Polynomial.Basic.polynomial `𝕜 "[X]")]
                 ")")
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.NormCast.tacticRw_mod_cast____
                     "rw_mod_cast"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `degree_X_pow)] "]")
                     [])
                    []
                    (Tactic.exact "exact" `hn)])))])]))])))
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
              [(Tactic.simpLemma [] [] `aeval_X_pow)
               ","
               (Tactic.simpLemma [] [] `eval_pow)
               ","
               (Tactic.simpLemma [] [] `eval_X)]
              "]")]
            ["using"
             (Term.app
              `map_polynomial_aeval_of_degree_pos
              [`a
               (Term.typeAscription
                "("
                («term_^_» `X "^" `n)
                ":"
                [(Polynomial.Data.Polynomial.Basic.polynomial `𝕜 "[X]")]
                ")")
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.NormCast.tacticRw_mod_cast____
                    "rw_mod_cast"
                    []
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `degree_X_pow)] "]")
                    [])
                   []
                   (Tactic.exact "exact" `hn)])))])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        ["only"]
        [(Tactic.simpArgs
          "["
          [(Tactic.simpLemma [] [] `aeval_X_pow)
           ","
           (Tactic.simpLemma [] [] `eval_pow)
           ","
           (Tactic.simpLemma [] [] `eval_X)]
          "]")]
        ["using"
         (Term.app
          `map_polynomial_aeval_of_degree_pos
          [`a
           (Term.typeAscription
            "("
            («term_^_» `X "^" `n)
            ":"
            [(Polynomial.Data.Polynomial.Basic.polynomial `𝕜 "[X]")]
            ")")
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.NormCast.tacticRw_mod_cast____
                "rw_mod_cast"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `degree_X_pow)] "]")
                [])
               []
               (Tactic.exact "exact" `hn)])))])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `map_polynomial_aeval_of_degree_pos
       [`a
        (Term.typeAscription
         "("
         («term_^_» `X "^" `n)
         ":"
         [(Polynomial.Data.Polynomial.Basic.polynomial `𝕜 "[X]")]
         ")")
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.NormCast.tacticRw_mod_cast____
             "rw_mod_cast"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `degree_X_pow)] "]")
             [])
            []
            (Tactic.exact "exact" `hn)])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.NormCast.tacticRw_mod_cast____
           "rw_mod_cast"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `degree_X_pow)] "]")
           [])
          []
          (Tactic.exact "exact" `hn)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `hn)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hn
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.NormCast.tacticRw_mod_cast____
       "rw_mod_cast"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `degree_X_pow)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `degree_X_pow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(Tactic.NormCast.tacticRw_mod_cast____
          "rw_mod_cast"
          []
          (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `degree_X_pow)] "]")
          [])
         []
         (Tactic.exact "exact" `hn)])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription
       "("
       («term_^_» `X "^" `n)
       ":"
       [(Polynomial.Data.Polynomial.Basic.polynomial `𝕜 "[X]")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Polynomial.Data.Polynomial.Basic.polynomial `𝕜 "[X]")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 9000, term))
      `𝕜
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 9000, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 9000, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `X "^" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `map_polynomial_aeval_of_degree_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eval_X
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eval_pow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `aeval_X_pow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [(«term_^_» `a "^" `n)])
       "="
       (Set.Data.Set.Image.term_''_
        (Term.fun "fun" (Term.basicFun [`x] [] "=>" («term_^_» `x "^" `n)))
        " '' "
        (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [`a])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Data.Set.Image.term_''_
       (Term.fun "fun" (Term.basicFun [`x] [] "=>" («term_^_» `x "^" `n)))
       " '' "
       (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [`a]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Algebra.Algebra.Spectrum.termσ_2', expected 'spectrum.Algebra.Algebra.Spectrum.termσ_2._@.Algebra.Algebra.Spectrum._hyg.2759'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    A specialization of `spectrum.map_polynomial_aeval_of_nonempty` to monic monomials for
    convenience. -/
  theorem
    map_pow_of_pos
    [ IsAlgClosed 𝕜 ] ( a : A ) { n : ℕ } ( hn : 0 < n ) : σ a ^ n = fun x => x ^ n '' σ a
    :=
      by
        simpa
          only
            [ aeval_X_pow , eval_pow , eval_X ]
            using
              map_polynomial_aeval_of_degree_pos
                a ( X ^ n : 𝕜 [X] ) by rw_mod_cast [ degree_X_pow ] exact hn
#align spectrum.map_pow_of_pos spectrum.map_pow_of_pos

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "A specialization of `spectrum.map_polynomial_aeval_of_nonempty` to monic monomials for\nconvenience. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `map_pow_of_nonempty [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `IsAlgClosed [`𝕜]) "]")
        (Term.implicitBinder "{" [`a] [":" `A] "}")
        (Term.explicitBinder
         "("
         [`ha]
         [":"
          (Term.proj (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [`a]) "." `Nonempty)]
         []
         ")")
        (Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [(«term_^_» `a "^" `n)])
         "="
         (Set.Data.Set.Image.term_''_
          (Term.fun "fun" (Term.basicFun [`x] [] "=>" («term_^_» `x "^" `n)))
          " '' "
          (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [`a])))))
      (Command.declValSimple
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
             ["only"]
             [(Tactic.simpArgs
               "["
               [(Tactic.simpLemma [] [] `aeval_X_pow)
                ","
                (Tactic.simpLemma [] [] `eval_pow)
                ","
                (Tactic.simpLemma [] [] `eval_X)]
               "]")]
             ["using"
              (Term.app `map_polynomial_aeval_of_nonempty [`a («term_^_» `X "^" `n) `ha])]))])))
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
              [(Tactic.simpLemma [] [] `aeval_X_pow)
               ","
               (Tactic.simpLemma [] [] `eval_pow)
               ","
               (Tactic.simpLemma [] [] `eval_X)]
              "]")]
            ["using"
             (Term.app `map_polynomial_aeval_of_nonempty [`a («term_^_» `X "^" `n) `ha])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        ["only"]
        [(Tactic.simpArgs
          "["
          [(Tactic.simpLemma [] [] `aeval_X_pow)
           ","
           (Tactic.simpLemma [] [] `eval_pow)
           ","
           (Tactic.simpLemma [] [] `eval_X)]
          "]")]
        ["using" (Term.app `map_polynomial_aeval_of_nonempty [`a («term_^_» `X "^" `n) `ha])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `map_polynomial_aeval_of_nonempty [`a («term_^_» `X "^" `n) `ha])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_^_» `X "^" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_^_» `X "^" `n) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `map_polynomial_aeval_of_nonempty
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eval_X
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eval_pow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `aeval_X_pow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [(«term_^_» `a "^" `n)])
       "="
       (Set.Data.Set.Image.term_''_
        (Term.fun "fun" (Term.basicFun [`x] [] "=>" («term_^_» `x "^" `n)))
        " '' "
        (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [`a])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Data.Set.Image.term_''_
       (Term.fun "fun" (Term.basicFun [`x] [] "=>" («term_^_» `x "^" `n)))
       " '' "
       (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [`a]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Algebra.Algebra.Spectrum.termσ_2', expected 'spectrum.Algebra.Algebra.Spectrum.termσ_2._@.Algebra.Algebra.Spectrum._hyg.2759'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    A specialization of `spectrum.map_polynomial_aeval_of_nonempty` to monic monomials for
    convenience. -/
  theorem
    map_pow_of_nonempty
    [ IsAlgClosed 𝕜 ] { a : A } ( ha : σ a . Nonempty ) ( n : ℕ ) : σ a ^ n = fun x => x ^ n '' σ a
    :=
      by
        simpa
          only [ aeval_X_pow , eval_pow , eval_X ] using map_polynomial_aeval_of_nonempty a X ^ n ha
#align spectrum.map_pow_of_nonempty spectrum.map_pow_of_nonempty

variable (𝕜)

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Every element `a` in a nontrivial finite-dimensional algebra `A`\nover an algebraically closed field `𝕜` has non-empty spectrum. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `nonempty_of_is_alg_closed_of_finite_dimensional [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `IsAlgClosed [`𝕜]) "]")
        (Term.instBinder "[" [] (Term.app `Nontrivial [`A]) "]")
        (Term.instBinder "[" [`I ":"] (Term.app `FiniteDimensional [`𝕜 `A]) "]")
        (Term.explicitBinder "(" [`a] [":" `A] [] ")")]
       (Term.typeSpec
        ":"
        («term∃_,_»
         "∃"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] [":" `𝕜]))
         ","
         («term_∈_» `k "∈" (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [`a])))))
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
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `p)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h_mon)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.one `h_eval_p)])
                       [])]
                     "⟩")])
                  [])]
                "⟩")])]
            []
            [":="
             [(Term.app
               `is_integral_of_noetherian
               [(Term.app (Term.proj `IsNoetherian.iff_fg "." (fieldIdx "2")) [`I]) `a])]])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`nu []]
              [(Term.typeSpec ":" («term¬_» "¬" (Term.app `IsUnit [(Term.app `aeval [`a `p])])))]
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
                    [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `aeval_def)]
                    "]")
                   [(Tactic.location "at" (Tactic.locationHyp [`h_eval_p] []))])
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_eval_p)] "]")
                   [])
                  []
                  (Tactic.simp "simp" [] [] [] [] [])]))))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               []
               (Term.app
                `eq_prod_roots_of_monic_of_splits_id
                [`h_mon (Term.app `IsAlgClosed.splits [`p])]))]
             "]")
            [(Tactic.location "at" (Tactic.locationHyp [`nu] []))])
           []
           (Std.Tactic.obtain
            "obtain"
            [(Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hk)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                  [])]
                "⟩")])]
            []
            [":="
             [(Term.app
               `exists_mem_of_not_is_unit_aeval_prod
               [(Term.app `monic.ne_zero [`h_mon]) `nu])]])
           []
           (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`k "," `hk] "⟩"))])))
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
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `p)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h_mon)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h_eval_p)])
                      [])]
                    "⟩")])
                 [])]
               "⟩")])]
           []
           [":="
            [(Term.app
              `is_integral_of_noetherian
              [(Term.app (Term.proj `IsNoetherian.iff_fg "." (fieldIdx "2")) [`I]) `a])]])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`nu []]
             [(Term.typeSpec ":" («term¬_» "¬" (Term.app `IsUnit [(Term.app `aeval [`a `p])])))]
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
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `aeval_def)]
                   "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`h_eval_p] []))])
                 []
                 (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_eval_p)] "]") [])
                 []
                 (Tactic.simp "simp" [] [] [] [] [])]))))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.app
               `eq_prod_roots_of_monic_of_splits_id
               [`h_mon (Term.app `IsAlgClosed.splits [`p])]))]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`nu] []))])
          []
          (Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hk)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                 [])]
               "⟩")])]
           []
           [":="
            [(Term.app
              `exists_mem_of_not_is_unit_aeval_prod
              [(Term.app `monic.ne_zero [`h_mon]) `nu])]])
          []
          (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`k "," `hk] "⟩"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`k "," `hk] "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`k "," `hk] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
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
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hk)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
             [])]
           "⟩")])]
       []
       [":="
        [(Term.app
          `exists_mem_of_not_is_unit_aeval_prod
          [(Term.app `monic.ne_zero [`h_mon]) `nu])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `exists_mem_of_not_is_unit_aeval_prod [(Term.app `monic.ne_zero [`h_mon]) `nu])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nu
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `monic.ne_zero [`h_mon])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h_mon
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `monic.ne_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `monic.ne_zero [`h_mon]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `exists_mem_of_not_is_unit_aeval_prod
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
          []
          (Term.app
           `eq_prod_roots_of_monic_of_splits_id
           [`h_mon (Term.app `IsAlgClosed.splits [`p])]))]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`nu] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nu
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `eq_prod_roots_of_monic_of_splits_id [`h_mon (Term.app `IsAlgClosed.splits [`p])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsAlgClosed.splits [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsAlgClosed.splits
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `IsAlgClosed.splits [`p]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h_mon
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eq_prod_roots_of_monic_of_splits_id
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`nu []]
         [(Term.typeSpec ":" («term¬_» "¬" (Term.app `IsUnit [(Term.app `aeval [`a `p])])))]
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
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `aeval_def)]
               "]")
              [(Tactic.location "at" (Tactic.locationHyp [`h_eval_p] []))])
             []
             (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_eval_p)] "]") [])
             []
             (Tactic.simp "simp" [] [] [] [] [])]))))))
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
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `aeval_def)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`h_eval_p] []))])
          []
          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_eval_p)] "]") [])
          []
          (Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h_eval_p)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h_eval_p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `aeval_def)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`h_eval_p] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h_eval_p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `aeval_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term¬_» "¬" (Term.app `IsUnit [(Term.app `aeval [`a `p])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsUnit [(Term.app `aeval [`a `p])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `aeval [`a `p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `aeval
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `aeval [`a `p]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsUnit
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 40 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 40, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `p)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h_mon)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h_eval_p)])
                  [])]
                "⟩")])
             [])]
           "⟩")])]
       []
       [":="
        [(Term.app
          `is_integral_of_noetherian
          [(Term.app (Term.proj `IsNoetherian.iff_fg "." (fieldIdx "2")) [`I]) `a])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `is_integral_of_noetherian
       [(Term.app (Term.proj `IsNoetherian.iff_fg "." (fieldIdx "2")) [`I]) `a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `IsNoetherian.iff_fg "." (fieldIdx "2")) [`I])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `I
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `IsNoetherian.iff_fg "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `IsNoetherian.iff_fg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `IsNoetherian.iff_fg "." (fieldIdx "2")) [`I])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_integral_of_noetherian
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term∃_,_»
       "∃"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] [":" `𝕜]))
       ","
       («term_∈_» `k "∈" (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [`a])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_» `k "∈" (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [`a]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Algebra.Algebra.Spectrum.termσ_2 "σ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Algebra.Algebra.Spectrum.termσ_2', expected 'spectrum.Algebra.Algebra.Spectrum.termσ_2._@.Algebra.Algebra.Spectrum._hyg.2759'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    Every element `a` in a nontrivial finite-dimensional algebra `A`
    over an algebraically closed field `𝕜` has non-empty spectrum. -/
  theorem
    nonempty_of_is_alg_closed_of_finite_dimensional
    [ IsAlgClosed 𝕜 ] [ Nontrivial A ] [ I : FiniteDimensional 𝕜 A ] ( a : A ) : ∃ k : 𝕜 , k ∈ σ a
    :=
      by
        obtain ⟨ p , ⟨ h_mon , h_eval_p ⟩ ⟩ := is_integral_of_noetherian IsNoetherian.iff_fg . 2 I a
          have nu : ¬ IsUnit aeval a p := by rw [ ← aeval_def ] at h_eval_p rw [ h_eval_p ] simp
          rw [ eq_prod_roots_of_monic_of_splits_id h_mon IsAlgClosed.splits p ] at nu
          obtain ⟨ k , hk , _ ⟩ := exists_mem_of_not_is_unit_aeval_prod monic.ne_zero h_mon nu
          exact ⟨ k , hk ⟩
#align
  spectrum.nonempty_of_is_alg_closed_of_finite_dimensional spectrum.nonempty_of_is_alg_closed_of_finite_dimensional

end ScalarField

end spectrum

namespace AlgHom

section CommSemiring

variable {F R A B : Type _} [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]

variable [AlgHomClass F R A B]

-- mathport name: exprσ
local notation "σ" => spectrum R

-- mathport name: «expr↑ₐ»
local notation "↑ₐ" => algebraMap R A

theorem mem_resolvent_set_apply (φ : F) {a : A} {r : R} (h : r ∈ resolventSet R a) :
    r ∈ resolventSet R ((φ : A → B) a) := by
  simpa only [map_sub, AlgHomClass.commutes] using h.map φ
#align alg_hom.mem_resolvent_set_apply AlgHom.mem_resolvent_set_apply

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `spectrum_apply_subset [])
      (Command.declSig
       [(Term.explicitBinder "(" [`φ] [":" `F] [] ")")
        (Term.explicitBinder "(" [`a] [":" `A] [] ")")]
       (Term.typeSpec
        ":"
        («term_⊆_»
         (Term.app
          (AlgHom.Algebra.Algebra.Spectrum.termσ "σ")
          [(Term.app (Term.typeAscription "(" `φ ":" [(Term.arrow `A "→" `B)] ")") [`a])])
         "⊆"
         (Term.app (AlgHom.Algebra.Algebra.Spectrum.termσ "σ") [`a]))))
      (Command.declValSimple
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.hole "_")]
         []
         "=>"
         (Term.app `mt [(Term.app `mem_resolvent_set_apply [`φ])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.hole "_")]
        []
        "=>"
        (Term.app `mt [(Term.app `mem_resolvent_set_apply [`φ])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mt [(Term.app `mem_resolvent_set_apply [`φ])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mem_resolvent_set_apply [`φ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `φ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mem_resolvent_set_apply
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `mem_resolvent_set_apply [`φ])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mt
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_⊆_»
       (Term.app
        (AlgHom.Algebra.Algebra.Spectrum.termσ "σ")
        [(Term.app (Term.typeAscription "(" `φ ":" [(Term.arrow `A "→" `B)] ")") [`a])])
       "⊆"
       (Term.app (AlgHom.Algebra.Algebra.Spectrum.termσ "σ") [`a]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (AlgHom.Algebra.Algebra.Spectrum.termσ "σ") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (AlgHom.Algebra.Algebra.Spectrum.termσ "σ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgHom.Algebra.Algebra.Spectrum.termσ', expected 'AlgHom.Algebra.Algebra.Spectrum.termσ._@.Algebra.Algebra.Spectrum._hyg.3840'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  spectrum_apply_subset
  ( φ : F ) ( a : A ) : σ ( φ : A → B ) a ⊆ σ a
  := fun _ => mt mem_resolvent_set_apply φ
#align alg_hom.spectrum_apply_subset AlgHom.spectrum_apply_subset

end CommSemiring

section CommRing

variable {F R A B : Type _} [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]

variable [AlgHomClass F R A R]

-- mathport name: exprσ
local notation "σ" => spectrum R

-- mathport name: «expr↑ₐ»
local notation "↑ₐ" => algebraMap R A

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `apply_mem_spectrum [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `Nontrivial [`R]) "]")
        (Term.explicitBinder "(" [`φ] [":" `F] [] ")")
        (Term.explicitBinder "(" [`a] [":" `A] [] ")")]
       (Term.typeSpec
        ":"
        («term_∈_»
         (Term.app `φ [`a])
         "∈"
         (Term.app (AlgHom.Algebra.Algebra.Spectrum.termσ_1 "σ") [`a]))))
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
                («term_∈_»
                 («term_-_»
                  (Term.app (AlgHom.Algebra.Algebra.Spectrum.«term↑ₐ_1» "↑ₐ") [(Term.app `φ [`a])])
                  "-"
                  `a)
                 "∈"
                 (Term.proj
                  (Term.typeAscription
                   "("
                   `φ
                   ":"
                   [(Algebra.Hom.Ring.«term_→+*_» `A " →+* " `R)]
                   ")")
                  "."
                  `ker)))]
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
                    [(Tactic.simpLemma [] [] `RingHom.mem_ker)
                     ","
                     (Tactic.simpLemma [] [] `map_sub)
                     ","
                     (Tactic.simpLemma [] [] `RingHom.coe_coe)
                     ","
                     (Tactic.simpLemma [] [] `AlgHomClass.commutes)
                     ","
                     (Tactic.simpLemma [] [] `Algebra.id.map_eq_id)
                     ","
                     (Tactic.simpLemma [] [] `RingHom.id_apply)
                     ","
                     (Tactic.simpLemma [] [] `sub_self)]
                    "]"]
                   [])]))))))
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `spectrum.mem_iff)
              ","
              (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `mem_nonunits_iff)
              ","
              (Tactic.simpLemma
               []
               []
               (Term.app
                `coe_subset_nonunits
                [(Term.proj
                  (Term.typeAscription
                   "("
                   `φ
                   ":"
                   [(Algebra.Hom.Ring.«term_→+*_» `A " →+* " `R)]
                   ")")
                  "."
                  `ker_ne_top)
                 `h]))]
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
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h []]
             [(Term.typeSpec
               ":"
               («term_∈_»
                («term_-_»
                 (Term.app (AlgHom.Algebra.Algebra.Spectrum.«term↑ₐ_1» "↑ₐ") [(Term.app `φ [`a])])
                 "-"
                 `a)
                "∈"
                (Term.proj
                 (Term.typeAscription "(" `φ ":" [(Algebra.Hom.Ring.«term_→+*_» `A " →+* " `R)] ")")
                 "."
                 `ker)))]
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
                   [(Tactic.simpLemma [] [] `RingHom.mem_ker)
                    ","
                    (Tactic.simpLemma [] [] `map_sub)
                    ","
                    (Tactic.simpLemma [] [] `RingHom.coe_coe)
                    ","
                    (Tactic.simpLemma [] [] `AlgHomClass.commutes)
                    ","
                    (Tactic.simpLemma [] [] `Algebra.id.map_eq_id)
                    ","
                    (Tactic.simpLemma [] [] `RingHom.id_apply)
                    ","
                    (Tactic.simpLemma [] [] `sub_self)]
                   "]"]
                  [])]))))))
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `spectrum.mem_iff)
             ","
             (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `mem_nonunits_iff)
             ","
             (Tactic.simpLemma
              []
              []
              (Term.app
               `coe_subset_nonunits
               [(Term.proj
                 (Term.typeAscription "(" `φ ":" [(Algebra.Hom.Ring.«term_→+*_» `A " →+* " `R)] ")")
                 "."
                 `ker_ne_top)
                `h]))]
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
        [(Tactic.simpLemma [] [] `spectrum.mem_iff)
         ","
         (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `mem_nonunits_iff)
         ","
         (Tactic.simpLemma
          []
          []
          (Term.app
           `coe_subset_nonunits
           [(Term.proj
             (Term.typeAscription "(" `φ ":" [(Algebra.Hom.Ring.«term_→+*_» `A " →+* " `R)] ")")
             "."
             `ker_ne_top)
            `h]))]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `coe_subset_nonunits
       [(Term.proj
         (Term.typeAscription "(" `φ ":" [(Algebra.Hom.Ring.«term_→+*_» `A " →+* " `R)] ")")
         "."
         `ker_ne_top)
        `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.typeAscription "(" `φ ":" [(Algebra.Hom.Ring.«term_→+*_» `A " →+* " `R)] ")")
       "."
       `ker_ne_top)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription "(" `φ ":" [(Algebra.Hom.Ring.«term_→+*_» `A " →+* " `R)] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Hom.Ring.«term_→+*_» `A " →+* " `R)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      `A
[PrettyPrinter.parenthesize] ...precedences are 26 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `φ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `coe_subset_nonunits
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_nonunits_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `spectrum.mem_iff
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
           («term_∈_»
            («term_-_»
             (Term.app (AlgHom.Algebra.Algebra.Spectrum.«term↑ₐ_1» "↑ₐ") [(Term.app `φ [`a])])
             "-"
             `a)
            "∈"
            (Term.proj
             (Term.typeAscription "(" `φ ":" [(Algebra.Hom.Ring.«term_→+*_» `A " →+* " `R)] ")")
             "."
             `ker)))]
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
               [(Tactic.simpLemma [] [] `RingHom.mem_ker)
                ","
                (Tactic.simpLemma [] [] `map_sub)
                ","
                (Tactic.simpLemma [] [] `RingHom.coe_coe)
                ","
                (Tactic.simpLemma [] [] `AlgHomClass.commutes)
                ","
                (Tactic.simpLemma [] [] `Algebra.id.map_eq_id)
                ","
                (Tactic.simpLemma [] [] `RingHom.id_apply)
                ","
                (Tactic.simpLemma [] [] `sub_self)]
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
            [(Tactic.simpLemma [] [] `RingHom.mem_ker)
             ","
             (Tactic.simpLemma [] [] `map_sub)
             ","
             (Tactic.simpLemma [] [] `RingHom.coe_coe)
             ","
             (Tactic.simpLemma [] [] `AlgHomClass.commutes)
             ","
             (Tactic.simpLemma [] [] `Algebra.id.map_eq_id)
             ","
             (Tactic.simpLemma [] [] `RingHom.id_apply)
             ","
             (Tactic.simpLemma [] [] `sub_self)]
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
        [(Tactic.simpLemma [] [] `RingHom.mem_ker)
         ","
         (Tactic.simpLemma [] [] `map_sub)
         ","
         (Tactic.simpLemma [] [] `RingHom.coe_coe)
         ","
         (Tactic.simpLemma [] [] `AlgHomClass.commutes)
         ","
         (Tactic.simpLemma [] [] `Algebra.id.map_eq_id)
         ","
         (Tactic.simpLemma [] [] `RingHom.id_apply)
         ","
         (Tactic.simpLemma [] [] `sub_self)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_self
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `RingHom.id_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Algebra.id.map_eq_id
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `AlgHomClass.commutes
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `RingHom.coe_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `RingHom.mem_ker
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_»
       («term_-_»
        (Term.app (AlgHom.Algebra.Algebra.Spectrum.«term↑ₐ_1» "↑ₐ") [(Term.app `φ [`a])])
        "-"
        `a)
       "∈"
       (Term.proj
        (Term.typeAscription "(" `φ ":" [(Algebra.Hom.Ring.«term_→+*_» `A " →+* " `R)] ")")
        "."
        `ker))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.typeAscription "(" `φ ":" [(Algebra.Hom.Ring.«term_→+*_» `A " →+* " `R)] ")")
       "."
       `ker)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription "(" `φ ":" [(Algebra.Hom.Ring.«term_→+*_» `A " →+* " `R)] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Hom.Ring.«term_→+*_» `A " →+* " `R)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `R
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      `A
[PrettyPrinter.parenthesize] ...precedences are 26 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `φ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_-_»
       (Term.app (AlgHom.Algebra.Algebra.Spectrum.«term↑ₐ_1» "↑ₐ") [(Term.app `φ [`a])])
       "-"
       `a)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app (AlgHom.Algebra.Algebra.Spectrum.«term↑ₐ_1» "↑ₐ") [(Term.app `φ [`a])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `φ [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `φ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `φ [`a]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (AlgHom.Algebra.Algebra.Spectrum.«term↑ₐ_1» "↑ₐ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'AlgHom.Algebra.Algebra.Spectrum.«term↑ₐ_1»', expected 'AlgHom.Algebra.Algebra.Spectrum.term↑ₐ_1._@.Algebra.Algebra.Spectrum._hyg.5414'
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
  apply_mem_spectrum
  [ Nontrivial R ] ( φ : F ) ( a : A ) : φ a ∈ σ a
  :=
    by
      have
          h
            : ↑ₐ φ a - a ∈ ( φ : A →+* R ) . ker
            :=
            by
              simp
                only
                [
                  RingHom.mem_ker
                    ,
                    map_sub
                    ,
                    RingHom.coe_coe
                    ,
                    AlgHomClass.commutes
                    ,
                    Algebra.id.map_eq_id
                    ,
                    RingHom.id_apply
                    ,
                    sub_self
                  ]
        simp
          only
          [
            spectrum.mem_iff
              ,
              ← mem_nonunits_iff
              ,
              coe_subset_nonunits ( φ : A →+* R ) . ker_ne_top h
            ]
#align alg_hom.apply_mem_spectrum AlgHom.apply_mem_spectrum

end CommRing

end AlgHom

