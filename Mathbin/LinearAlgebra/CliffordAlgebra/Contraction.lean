/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module linear_algebra.clifford_algebra.contraction
! leanprover-community/mathlib commit 26f081a2fb920140ed5bc5cc5344e84bcc7cb2b2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.ExteriorAlgebra.Basic
import Mathbin.LinearAlgebra.CliffordAlgebra.Fold
import Mathbin.LinearAlgebra.CliffordAlgebra.Conjugation

/-!
# Contraction in Clifford Algebras

This file contains some of the results from [grinberg_clifford_2016][].
The key result is `clifford_algebra.equiv_exterior`.

## Main definitions

* `clifford_algebra.contract_left`: contract a multivector by a `module.dual R M` on the left.
* `clifford_algebra.contract_right`: contract a multivector by a `module.dual R M` on the right.
* `clifford_algebra.change_form`: convert between two algebras of different quadratic form, sending
  vectors to vectors. The difference of the quadratic forms must be a bilinear form.
* `clifford_algebra.equiv_exterior`: in characteristic not-two, the `clifford_algebra Q` is
  isomorphic as a module to the exterior algebra.

## Implementation notes

This file somewhat follows [grinberg_clifford_2016][], although we are missing some of the induction
principles needed to prove many of the results. Here, we avoid the quotient-based approach described
in [grinberg_clifford_2016][], instead directly constructing our objects using the universal
property.

Note that [grinberg_clifford_2016][] concludes that its contents are not novel, and are in fact just
a rehash of parts of [bourbaki2007][]; we should at some point consider swapping our references to
refer to the latter.

Within this file, we use the local notation
* `x ⌊ d` for `contract_right x d`
* `d ⌋ x` for `contract_left d x`

-/


universe u1 u2 u3

variable {R : Type u1} [CommRing R]

variable {M : Type u2} [AddCommGroup M] [Module R M]

variable (Q : QuadraticForm R M)

namespace CliffordAlgebra

section ContractLeft

variable (d d' : Module.Dual R M)

/-- Auxiliary construction for `clifford_algebra.contract_left` -/
@[simps]
def contractLeftAux (d : Module.Dual R M) :
    M →ₗ[R] CliffordAlgebra Q × CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q :=
  haveI v_mul := (Algebra.lmul R (CliffordAlgebra Q)).toLinearMap ∘ₗ ι Q
  d.smul_right (LinearMap.fst _ (CliffordAlgebra Q) (CliffordAlgebra Q)) -
    v_mul.compl₂ (LinearMap.snd _ (CliffordAlgebra Q) _)
#align clifford_algebra.contract_left_aux CliffordAlgebra.contractLeftAux

theorem contract_left_aux_contract_left_aux (v : M) (x : CliffordAlgebra Q)
    (fx : CliffordAlgebra Q) :
    contractLeftAux Q d v (ι Q v * x, contractLeftAux Q d v (x, fx)) = Q v • fx :=
  by
  simp only [contract_left_aux_apply_apply]
  rw [mul_sub, ← mul_assoc, ι_sq_scalar, ← Algebra.smul_def, ← sub_add, mul_smul_comm, sub_self,
    zero_add]
#align
  clifford_algebra.contract_left_aux_contract_left_aux CliffordAlgebra.contract_left_aux_contract_left_aux

variable {Q}

/-- Contract an element of the clifford algebra with an element `d : module.dual R M` from the left.

Note that $v ⌋ x$ is spelt `contract_left (Q.associated v) x`.

This includes [grinberg_clifford_2016][] Theorem 10.75 -/
def contractLeft : Module.Dual R M →ₗ[R] CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q
    where
  toFun d := foldr' Q (contractLeftAux Q d) (contract_left_aux_contract_left_aux Q d) 0
  map_add' d₁ d₂ :=
    LinearMap.ext fun x => by
      rw [LinearMap.add_apply]
      induction' x using CliffordAlgebra.leftInduction with r x y hx hy m x hx
      · simp_rw [foldr'_algebra_map, smul_zero, zero_add]
      · rw [map_add, map_add, map_add, add_add_add_comm, hx, hy]
      · rw [foldr'_ι_mul, foldr'_ι_mul, foldr'_ι_mul, hx]
        dsimp only [contract_left_aux_apply_apply]
        rw [sub_add_sub_comm, mul_add, LinearMap.add_apply, add_smul]
  map_smul' c d :=
    LinearMap.ext fun x => by
      rw [LinearMap.smul_apply, RingHom.id_apply]
      induction' x using CliffordAlgebra.leftInduction with r x y hx hy m x hx
      · simp_rw [foldr'_algebra_map, smul_zero]
      · rw [map_add, map_add, smul_add, hx, hy]
      · rw [foldr'_ι_mul, foldr'_ι_mul, hx]
        dsimp only [contract_left_aux_apply_apply]
        rw [LinearMap.smul_apply, smul_assoc, mul_smul_comm, smul_sub]
#align clifford_algebra.contract_left CliffordAlgebra.contractLeft

/-- Contract an element of the clifford algebra with an element `d : module.dual R M` from the
right.

Note that $x ⌊ v$ is spelt `contract_right x (Q.associated v)`.

This includes [grinberg_clifford_2016][] Theorem 16.75 -/
def contractRight : CliffordAlgebra Q →ₗ[R] Module.Dual R M →ₗ[R] CliffordAlgebra Q :=
  LinearMap.flip (LinearMap.compl₂ (LinearMap.compr₂ contractLeft reverse) reverse)
#align clifford_algebra.contract_right CliffordAlgebra.contractRight

theorem contract_right_eq (x : CliffordAlgebra Q) :
    contractRight x d = reverse (contractLeft d <| reverse x) :=
  rfl
#align clifford_algebra.contract_right_eq CliffordAlgebra.contract_right_eq

-- mathport name: «expr ⌋ »
local infixl:70 "⌋" => contractLeft

-- mathport name: «expr ⌊ »
local infixl:70 "⌊" => contractRight

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "This is [grinberg_clifford_2016][] Theorem 6  -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `contract_left_ι_mul [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" `M] [] ")")
        (Term.explicitBinder "(" [`b] [":" (Term.app `CliffordAlgebra [`Q])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_»
          `d
          "⌋"
          («term_*_» (Term.app `ι [`Q `a]) "*" `b))
         "="
         («term_-_»
          (Algebra.Group.Defs.«term_•_» (Term.app `d [`a]) " • " `b)
          "-"
          («term_*_»
           (Term.app `ι [`Q `a])
           "*"
           (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_» `d "⌋" `b))))))
      (Command.declValSimple
       ":="
       (Term.app
        `foldr'_ι_mul
        [(Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `foldr'_ι_mul
       [(Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `foldr'_ι_mul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_»
        `d
        "⌋"
        («term_*_» (Term.app `ι [`Q `a]) "*" `b))
       "="
       («term_-_»
        (Algebra.Group.Defs.«term_•_» (Term.app `d [`a]) " • " `b)
        "-"
        («term_*_»
         (Term.app `ι [`Q `a])
         "*"
         (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_» `d "⌋" `b))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_»
       (Algebra.Group.Defs.«term_•_» (Term.app `d [`a]) " • " `b)
       "-"
       («term_*_»
        (Term.app `ι [`Q `a])
        "*"
        (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_» `d "⌋" `b)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.app `ι [`Q `a])
       "*"
       (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_» `d "⌋" `b))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_» `d "⌋" `b)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_»', expected 'CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.term_⌋_._@.LinearAlgebra.CliffordAlgebra.Contraction._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- This is [grinberg_clifford_2016][] Theorem 6  -/
  theorem
    contract_left_ι_mul
    ( a : M ) ( b : CliffordAlgebra Q ) : d ⌋ ι Q a * b = d a • b - ι Q a * d ⌋ b
    := foldr'_ι_mul _ _ _ _ _ _
#align clifford_algebra.contract_left_ι_mul CliffordAlgebra.contract_left_ι_mul

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "This is [grinberg_clifford_2016][] Theorem 12  -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `contract_right_mul_ι [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" `M] [] ")")
        (Term.explicitBinder "(" [`b] [":" (Term.app `CliffordAlgebra [`Q])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_»
          («term_*_» `b "*" (Term.app `ι [`Q `a]))
          "⌊"
          `d)
         "="
         («term_-_»
          (Algebra.Group.Defs.«term_•_» (Term.app `d [`a]) " • " `b)
          "-"
          («term_*_»
           (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_» `b "⌊" `d)
           "*"
           (Term.app `ι [`Q `a]))))))
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
             [(Tactic.rwRule [] `contract_right_eq)
              ","
              (Tactic.rwRule [] `reverse.map_mul)
              ","
              (Tactic.rwRule [] `reverse_ι)
              ","
              (Tactic.rwRule [] `contract_left_ι_mul)
              ","
              (Tactic.rwRule [] `map_sub)
              ","
              (Tactic.rwRule [] `map_smul)
              ","
              (Tactic.rwRule [] `reverse_reverse)
              ","
              (Tactic.rwRule [] `reverse.map_mul)
              ","
              (Tactic.rwRule [] `reverse_ι)
              ","
              (Tactic.rwRule [] `contract_right_eq)]
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
            [(Tactic.rwRule [] `contract_right_eq)
             ","
             (Tactic.rwRule [] `reverse.map_mul)
             ","
             (Tactic.rwRule [] `reverse_ι)
             ","
             (Tactic.rwRule [] `contract_left_ι_mul)
             ","
             (Tactic.rwRule [] `map_sub)
             ","
             (Tactic.rwRule [] `map_smul)
             ","
             (Tactic.rwRule [] `reverse_reverse)
             ","
             (Tactic.rwRule [] `reverse.map_mul)
             ","
             (Tactic.rwRule [] `reverse_ι)
             ","
             (Tactic.rwRule [] `contract_right_eq)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `contract_right_eq)
         ","
         (Tactic.rwRule [] `reverse.map_mul)
         ","
         (Tactic.rwRule [] `reverse_ι)
         ","
         (Tactic.rwRule [] `contract_left_ι_mul)
         ","
         (Tactic.rwRule [] `map_sub)
         ","
         (Tactic.rwRule [] `map_smul)
         ","
         (Tactic.rwRule [] `reverse_reverse)
         ","
         (Tactic.rwRule [] `reverse.map_mul)
         ","
         (Tactic.rwRule [] `reverse_ι)
         ","
         (Tactic.rwRule [] `contract_right_eq)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `contract_right_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `reverse_ι
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `reverse.map_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `reverse_reverse
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `contract_left_ι_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `reverse_ι
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `reverse.map_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `contract_right_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_»
        («term_*_» `b "*" (Term.app `ι [`Q `a]))
        "⌊"
        `d)
       "="
       («term_-_»
        (Algebra.Group.Defs.«term_•_» (Term.app `d [`a]) " • " `b)
        "-"
        («term_*_»
         (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_» `b "⌊" `d)
         "*"
         (Term.app `ι [`Q `a]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_»
       (Algebra.Group.Defs.«term_•_» (Term.app `d [`a]) " • " `b)
       "-"
       («term_*_»
        (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_» `b "⌊" `d)
        "*"
        (Term.app `ι [`Q `a])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_» `b "⌊" `d)
       "*"
       (Term.app `ι [`Q `a]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ι [`Q `a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Q
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ι
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_» `b "⌊" `d)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_»', expected 'CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.term_⌊_._@.LinearAlgebra.CliffordAlgebra.Contraction._hyg.537'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- This is [grinberg_clifford_2016][] Theorem 12  -/
  theorem
    contract_right_mul_ι
    ( a : M ) ( b : CliffordAlgebra Q ) : b * ι Q a ⌊ d = d a • b - b ⌊ d * ι Q a
    :=
      by
        rw
          [
            contract_right_eq
              ,
              reverse.map_mul
              ,
              reverse_ι
              ,
              contract_left_ι_mul
              ,
              map_sub
              ,
              map_smul
              ,
              reverse_reverse
              ,
              reverse.map_mul
              ,
              reverse_ι
              ,
              contract_right_eq
            ]
#align clifford_algebra.contract_right_mul_ι CliffordAlgebra.contract_right_mul_ι

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `contract_left_algebra_map_mul [])
      (Command.declSig
       [(Term.explicitBinder "(" [`r] [":" `R] [] ")")
        (Term.explicitBinder "(" [`b] [":" (Term.app `CliffordAlgebra [`Q])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_»
          `d
          "⌋"
          («term_*_» (Term.app `algebraMap [(Term.hole "_") (Term.hole "_") `r]) "*" `b))
         "="
         («term_*_»
          (Term.app `algebraMap [(Term.hole "_") (Term.hole "_") `r])
          "*"
          (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_» `d "⌋" `b)))))
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
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Algebra.smul_def)
              ","
              (Tactic.rwRule [] `map_smul)
              ","
              (Tactic.rwRule [] `Algebra.smul_def)]
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
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Algebra.smul_def)
             ","
             (Tactic.rwRule [] `map_smul)
             ","
             (Tactic.rwRule [] `Algebra.smul_def)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Algebra.smul_def)
         ","
         (Tactic.rwRule [] `map_smul)
         ","
         (Tactic.rwRule [] `Algebra.smul_def)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Algebra.smul_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Algebra.smul_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_»
        `d
        "⌋"
        («term_*_» (Term.app `algebraMap [(Term.hole "_") (Term.hole "_") `r]) "*" `b))
       "="
       («term_*_»
        (Term.app `algebraMap [(Term.hole "_") (Term.hole "_") `r])
        "*"
        (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_» `d "⌋" `b)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.app `algebraMap [(Term.hole "_") (Term.hole "_") `r])
       "*"
       (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_» `d "⌋" `b))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_» `d "⌋" `b)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_»', expected 'CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.term_⌋_._@.LinearAlgebra.CliffordAlgebra.Contraction._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  contract_left_algebra_map_mul
  ( r : R ) ( b : CliffordAlgebra Q ) : d ⌋ algebraMap _ _ r * b = algebraMap _ _ r * d ⌋ b
  := by rw [ ← Algebra.smul_def , map_smul , Algebra.smul_def ]
#align clifford_algebra.contract_left_algebra_map_mul CliffordAlgebra.contract_left_algebra_map_mul

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `contract_left_mul_algebra_map [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" (Term.app `CliffordAlgebra [`Q])] [] ")")
        (Term.explicitBinder "(" [`r] [":" `R] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_»
          `d
          "⌋"
          («term_*_» `a "*" (Term.app `algebraMap [(Term.hole "_") (Term.hole "_") `r])))
         "="
         («term_*_»
          (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_» `d "⌋" `a)
          "*"
          (Term.app `algebraMap [(Term.hole "_") (Term.hole "_") `r])))))
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
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Algebra.commutes)
              ","
              (Tactic.rwRule [] `contract_left_algebra_map_mul)
              ","
              (Tactic.rwRule [] `Algebra.commutes)]
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
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Algebra.commutes)
             ","
             (Tactic.rwRule [] `contract_left_algebra_map_mul)
             ","
             (Tactic.rwRule [] `Algebra.commutes)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Algebra.commutes)
         ","
         (Tactic.rwRule [] `contract_left_algebra_map_mul)
         ","
         (Tactic.rwRule [] `Algebra.commutes)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Algebra.commutes
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `contract_left_algebra_map_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Algebra.commutes
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_»
        `d
        "⌋"
        («term_*_» `a "*" (Term.app `algebraMap [(Term.hole "_") (Term.hole "_") `r])))
       "="
       («term_*_»
        (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_» `d "⌋" `a)
        "*"
        (Term.app `algebraMap [(Term.hole "_") (Term.hole "_") `r])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_» `d "⌋" `a)
       "*"
       (Term.app `algebraMap [(Term.hole "_") (Term.hole "_") `r]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `algebraMap [(Term.hole "_") (Term.hole "_") `r])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `algebraMap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_» `d "⌋" `a)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_»', expected 'CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.term_⌋_._@.LinearAlgebra.CliffordAlgebra.Contraction._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  contract_left_mul_algebra_map
  ( a : CliffordAlgebra Q ) ( r : R ) : d ⌋ a * algebraMap _ _ r = d ⌋ a * algebraMap _ _ r
  := by rw [ ← Algebra.commutes , contract_left_algebra_map_mul , Algebra.commutes ]
#align clifford_algebra.contract_left_mul_algebra_map CliffordAlgebra.contract_left_mul_algebra_map

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `contract_right_algebra_map_mul [])
      (Command.declSig
       [(Term.explicitBinder "(" [`r] [":" `R] [] ")")
        (Term.explicitBinder "(" [`b] [":" (Term.app `CliffordAlgebra [`Q])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_»
          («term_*_» (Term.app `algebraMap [(Term.hole "_") (Term.hole "_") `r]) "*" `b)
          "⌊"
          `d)
         "="
         («term_*_»
          (Term.app `algebraMap [(Term.hole "_") (Term.hole "_") `r])
          "*"
          (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_» `b "⌊" `d)))))
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
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Algebra.smul_def)
              ","
              (Tactic.rwRule [] `LinearMap.map_smul₂)
              ","
              (Tactic.rwRule [] `Algebra.smul_def)]
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
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Algebra.smul_def)
             ","
             (Tactic.rwRule [] `LinearMap.map_smul₂)
             ","
             (Tactic.rwRule [] `Algebra.smul_def)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Algebra.smul_def)
         ","
         (Tactic.rwRule [] `LinearMap.map_smul₂)
         ","
         (Tactic.rwRule [] `Algebra.smul_def)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Algebra.smul_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearMap.map_smul₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Algebra.smul_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_»
        («term_*_» (Term.app `algebraMap [(Term.hole "_") (Term.hole "_") `r]) "*" `b)
        "⌊"
        `d)
       "="
       («term_*_»
        (Term.app `algebraMap [(Term.hole "_") (Term.hole "_") `r])
        "*"
        (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_» `b "⌊" `d)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.app `algebraMap [(Term.hole "_") (Term.hole "_") `r])
       "*"
       (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_» `b "⌊" `d))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_» `b "⌊" `d)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_»', expected 'CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.term_⌊_._@.LinearAlgebra.CliffordAlgebra.Contraction._hyg.537'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  contract_right_algebra_map_mul
  ( r : R ) ( b : CliffordAlgebra Q ) : algebraMap _ _ r * b ⌊ d = algebraMap _ _ r * b ⌊ d
  := by rw [ ← Algebra.smul_def , LinearMap.map_smul₂ , Algebra.smul_def ]
#align
  clifford_algebra.contract_right_algebra_map_mul CliffordAlgebra.contract_right_algebra_map_mul

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `contract_right_mul_algebra_map [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" (Term.app `CliffordAlgebra [`Q])] [] ")")
        (Term.explicitBinder "(" [`r] [":" `R] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_»
          («term_*_» `a "*" (Term.app `algebraMap [(Term.hole "_") (Term.hole "_") `r]))
          "⌊"
          `d)
         "="
         («term_*_»
          (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_» `a "⌊" `d)
          "*"
          (Term.app `algebraMap [(Term.hole "_") (Term.hole "_") `r])))))
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
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Algebra.commutes)
              ","
              (Tactic.rwRule [] `contract_right_algebra_map_mul)
              ","
              (Tactic.rwRule [] `Algebra.commutes)]
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
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Algebra.commutes)
             ","
             (Tactic.rwRule [] `contract_right_algebra_map_mul)
             ","
             (Tactic.rwRule [] `Algebra.commutes)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Algebra.commutes)
         ","
         (Tactic.rwRule [] `contract_right_algebra_map_mul)
         ","
         (Tactic.rwRule [] `Algebra.commutes)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Algebra.commutes
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `contract_right_algebra_map_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Algebra.commutes
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_»
        («term_*_» `a "*" (Term.app `algebraMap [(Term.hole "_") (Term.hole "_") `r]))
        "⌊"
        `d)
       "="
       («term_*_»
        (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_» `a "⌊" `d)
        "*"
        (Term.app `algebraMap [(Term.hole "_") (Term.hole "_") `r])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_» `a "⌊" `d)
       "*"
       (Term.app `algebraMap [(Term.hole "_") (Term.hole "_") `r]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `algebraMap [(Term.hole "_") (Term.hole "_") `r])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `algebraMap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_» `a "⌊" `d)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_»', expected 'CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.term_⌊_._@.LinearAlgebra.CliffordAlgebra.Contraction._hyg.537'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  contract_right_mul_algebra_map
  ( a : CliffordAlgebra Q ) ( r : R ) : a * algebraMap _ _ r ⌊ d = a ⌊ d * algebraMap _ _ r
  := by rw [ ← Algebra.commutes , contract_right_algebra_map_mul , Algebra.commutes ]
#align
  clifford_algebra.contract_right_mul_algebra_map CliffordAlgebra.contract_right_mul_algebra_map

variable (Q)

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
      (Command.declId `contract_left_ι [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x] [":" `M] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_»
          `d
          "⌋"
          (Term.app `ι [`Q `x]))
         "="
         (Term.app `algebraMap [`R (Term.hole "_") (Term.app `d [`x])]))))
      (Command.declValSimple
       ":="
       («term_<|_»
        (Term.proj
         (Term.app
          `foldr'_ι
          [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
         "."
         `trans)
        "<|"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Mathlib.Tactic.tacticSimp_rw__
             "simp_rw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `contract_left_aux_apply_apply)
               ","
               (Tactic.rwRule [] `mul_zero)
               ","
               (Tactic.rwRule [] `sub_zero)
               ","
               (Tactic.rwRule [] `Algebra.algebra_map_eq_smul_one)]
              "]")
             [])]))))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj
        (Term.app
         `foldr'_ι
         [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
        "."
        `trans)
       "<|"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Mathlib.Tactic.tacticSimp_rw__
            "simp_rw"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `contract_left_aux_apply_apply)
              ","
              (Tactic.rwRule [] `mul_zero)
              ","
              (Tactic.rwRule [] `sub_zero)
              ","
              (Tactic.rwRule [] `Algebra.algebra_map_eq_smul_one)]
             "]")
            [])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `contract_left_aux_apply_apply)
             ","
             (Tactic.rwRule [] `mul_zero)
             ","
             (Tactic.rwRule [] `sub_zero)
             ","
             (Tactic.rwRule [] `Algebra.algebra_map_eq_smul_one)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `contract_left_aux_apply_apply)
         ","
         (Tactic.rwRule [] `mul_zero)
         ","
         (Tactic.rwRule [] `sub_zero)
         ","
         (Tactic.rwRule [] `Algebra.algebra_map_eq_smul_one)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Algebra.algebra_map_eq_smul_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `contract_left_aux_apply_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj
       (Term.app
        `foldr'_ι
        [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
       "."
       `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `foldr'_ι
       [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `foldr'_ι
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `foldr'_ι
      [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_»
        `d
        "⌋"
        (Term.app `ι [`Q `x]))
       "="
       (Term.app `algebraMap [`R (Term.hole "_") (Term.app `d [`x])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `algebraMap [`R (Term.hole "_") (Term.app `d [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `d [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `d
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `d [`x]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `algebraMap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_»
       `d
       "⌋"
       (Term.app `ι [`Q `x]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_»', expected 'CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.term_⌋_._@.LinearAlgebra.CliffordAlgebra.Contraction._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    contract_left_ι
    ( x : M ) : d ⌋ ι Q x = algebraMap R _ d x
    :=
      foldr'_ι _ _ _ _ _ . trans
        <|
        by
          simp_rw
            [
              contract_left_aux_apply_apply , mul_zero , sub_zero , Algebra.algebra_map_eq_smul_one
              ]
#align clifford_algebra.contract_left_ι CliffordAlgebra.contract_left_ι

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
      (Command.declId `contract_right_ι [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x] [":" `M] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_»
          (Term.app `ι [`Q `x])
          "⌊"
          `d)
         "="
         (Term.app `algebraMap [`R (Term.hole "_") (Term.app `d [`x])]))))
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
             [(Tactic.rwRule [] `contract_right_eq)
              ","
              (Tactic.rwRule [] `reverse_ι)
              ","
              (Tactic.rwRule [] `contract_left_ι)
              ","
              (Tactic.rwRule [] `reverse.commutes)]
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
            [(Tactic.rwRule [] `contract_right_eq)
             ","
             (Tactic.rwRule [] `reverse_ι)
             ","
             (Tactic.rwRule [] `contract_left_ι)
             ","
             (Tactic.rwRule [] `reverse.commutes)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `contract_right_eq)
         ","
         (Tactic.rwRule [] `reverse_ι)
         ","
         (Tactic.rwRule [] `contract_left_ι)
         ","
         (Tactic.rwRule [] `reverse.commutes)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `reverse.commutes
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `contract_left_ι
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `reverse_ι
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `contract_right_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_»
        (Term.app `ι [`Q `x])
        "⌊"
        `d)
       "="
       (Term.app `algebraMap [`R (Term.hole "_") (Term.app `d [`x])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `algebraMap [`R (Term.hole "_") (Term.app `d [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `d [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `d
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `d [`x]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `algebraMap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_»
       (Term.app `ι [`Q `x])
       "⌊"
       `d)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_»', expected 'CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.term_⌊_._@.LinearAlgebra.CliffordAlgebra.Contraction._hyg.537'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    contract_right_ι
    ( x : M ) : ι Q x ⌊ d = algebraMap R _ d x
    := by rw [ contract_right_eq , reverse_ι , contract_left_ι , reverse.commutes ]
#align clifford_algebra.contract_right_ι CliffordAlgebra.contract_right_ι

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
      (Command.declId `contract_left_algebra_map [])
      (Command.declSig
       [(Term.explicitBinder "(" [`r] [":" `R] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_»
          `d
          "⌋"
          (Term.app `algebraMap [`R (Term.app `CliffordAlgebra [`Q]) `r]))
         "="
         (num "0"))))
      (Command.declValSimple
       ":="
       («term_<|_»
        (Term.proj
         (Term.app
          `foldr'_algebra_map
          [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
         "."
         `trans)
        "<|"
        (Term.app `smul_zero [(Term.hole "_")]))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj
        (Term.app
         `foldr'_algebra_map
         [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
        "."
        `trans)
       "<|"
       (Term.app `smul_zero [(Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `smul_zero [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `smul_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj
       (Term.app
        `foldr'_algebra_map
        [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
       "."
       `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `foldr'_algebra_map
       [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `foldr'_algebra_map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `foldr'_algebra_map
      [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_»
        `d
        "⌋"
        (Term.app `algebraMap [`R (Term.app `CliffordAlgebra [`Q]) `r]))
       "="
       (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_»
       `d
       "⌋"
       (Term.app `algebraMap [`R (Term.app `CliffordAlgebra [`Q]) `r]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_»', expected 'CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.term_⌋_._@.LinearAlgebra.CliffordAlgebra.Contraction._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    contract_left_algebra_map
    ( r : R ) : d ⌋ algebraMap R CliffordAlgebra Q r = 0
    := foldr'_algebra_map _ _ _ _ _ . trans <| smul_zero _
#align clifford_algebra.contract_left_algebra_map CliffordAlgebra.contract_left_algebra_map

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
      (Command.declId `contract_right_algebra_map [])
      (Command.declSig
       [(Term.explicitBinder "(" [`r] [":" `R] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_»
          (Term.app `algebraMap [`R (Term.app `CliffordAlgebra [`Q]) `r])
          "⌊"
          `d)
         "="
         (num "0"))))
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
             [(Tactic.rwRule [] `contract_right_eq)
              ","
              (Tactic.rwRule [] `reverse.commutes)
              ","
              (Tactic.rwRule [] `contract_left_algebra_map)
              ","
              (Tactic.rwRule [] `map_zero)]
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
            [(Tactic.rwRule [] `contract_right_eq)
             ","
             (Tactic.rwRule [] `reverse.commutes)
             ","
             (Tactic.rwRule [] `contract_left_algebra_map)
             ","
             (Tactic.rwRule [] `map_zero)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `contract_right_eq)
         ","
         (Tactic.rwRule [] `reverse.commutes)
         ","
         (Tactic.rwRule [] `contract_left_algebra_map)
         ","
         (Tactic.rwRule [] `map_zero)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `contract_left_algebra_map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `reverse.commutes
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `contract_right_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_»
        (Term.app `algebraMap [`R (Term.app `CliffordAlgebra [`Q]) `r])
        "⌊"
        `d)
       "="
       (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_»
       (Term.app `algebraMap [`R (Term.app `CliffordAlgebra [`Q]) `r])
       "⌊"
       `d)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_»', expected 'CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.term_⌊_._@.LinearAlgebra.CliffordAlgebra.Contraction._hyg.537'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    contract_right_algebra_map
    ( r : R ) : algebraMap R CliffordAlgebra Q r ⌊ d = 0
    := by rw [ contract_right_eq , reverse.commutes , contract_left_algebra_map , map_zero ]
#align clifford_algebra.contract_right_algebra_map CliffordAlgebra.contract_right_algebra_map

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
      (Command.declId `contract_left_one [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term_=_»
         (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_»
          `d
          "⌋"
          (Term.typeAscription "(" (num "1") ":" [(Term.app `CliffordAlgebra [`Q])] ")"))
         "="
         (num "0"))))
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
             [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `map_one)] "]")]
             ["using" (Term.app `contract_left_algebra_map [`Q `d (num "1")])]))])))
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
            [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `map_one)] "]")]
            ["using" (Term.app `contract_left_algebra_map [`Q `d (num "1")])]))])))
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
        [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `map_one)] "]")]
        ["using" (Term.app `contract_left_algebra_map [`Q `d (num "1")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `contract_left_algebra_map [`Q `d (num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `d
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Q
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `contract_left_algebra_map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_»
        `d
        "⌋"
        (Term.typeAscription "(" (num "1") ":" [(Term.app `CliffordAlgebra [`Q])] ")"))
       "="
       (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_»
       `d
       "⌋"
       (Term.typeAscription "(" (num "1") ":" [(Term.app `CliffordAlgebra [`Q])] ")"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_»', expected 'CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.term_⌋_._@.LinearAlgebra.CliffordAlgebra.Contraction._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    contract_left_one
    : d ⌋ ( 1 : CliffordAlgebra Q ) = 0
    := by simpa only [ map_one ] using contract_left_algebra_map Q d 1
#align clifford_algebra.contract_left_one CliffordAlgebra.contract_left_one

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
      (Command.declId `contract_right_one [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term_=_»
         (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_»
          (Term.typeAscription "(" (num "1") ":" [(Term.app `CliffordAlgebra [`Q])] ")")
          "⌊"
          `d)
         "="
         (num "0"))))
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
             [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `map_one)] "]")]
             ["using" (Term.app `contract_right_algebra_map [`Q `d (num "1")])]))])))
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
            [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `map_one)] "]")]
            ["using" (Term.app `contract_right_algebra_map [`Q `d (num "1")])]))])))
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
        [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `map_one)] "]")]
        ["using" (Term.app `contract_right_algebra_map [`Q `d (num "1")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `contract_right_algebra_map [`Q `d (num "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `d
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Q
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `contract_right_algebra_map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_»
        (Term.typeAscription "(" (num "1") ":" [(Term.app `CliffordAlgebra [`Q])] ")")
        "⌊"
        `d)
       "="
       (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_»
       (Term.typeAscription "(" (num "1") ":" [(Term.app `CliffordAlgebra [`Q])] ")")
       "⌊"
       `d)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_»', expected 'CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.term_⌊_._@.LinearAlgebra.CliffordAlgebra.Contraction._hyg.537'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    contract_right_one
    : ( 1 : CliffordAlgebra Q ) ⌊ d = 0
    := by simpa only [ map_one ] using contract_right_algebra_map Q d 1
#align clifford_algebra.contract_right_one CliffordAlgebra.contract_right_one

variable {Q}

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "This is [grinberg_clifford_2016][] Theorem 7 -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `contract_left_contract_left [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x] [":" (Term.app `CliffordAlgebra [`Q])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_»
          `d
          "⌋"
          (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_» `d "⌋" `x))
         "="
         (num "0"))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.induction'
            "induction'"
            [(Tactic.casesTarget [] `x)]
            ["using" `CliffordAlgebra.leftInduction]
            ["with"
             [(Lean.binderIdent `r)
              (Lean.binderIdent `x)
              (Lean.binderIdent `y)
              (Lean.binderIdent `hx)
              (Lean.binderIdent `hy)
              (Lean.binderIdent `m)
              (Lean.binderIdent `x)
              (Lean.binderIdent `hx)]]
            [])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Mathlib.Tactic.tacticSimp_rw__
              "simp_rw"
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `contract_left_algebra_map) "," (Tactic.rwRule [] `map_zero)]
               "]")
              [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `map_add)
                ","
                (Tactic.rwRule [] `map_add)
                ","
                (Tactic.rwRule [] `hx)
                ","
                (Tactic.rwRule [] `hy)
                ","
                (Tactic.rwRule [] `add_zero)]
               "]")
              [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `contract_left_ι_mul)
                ","
                (Tactic.rwRule [] `map_sub)
                ","
                (Tactic.rwRule [] `contract_left_ι_mul)
                ","
                (Tactic.rwRule [] `hx)
                ","
                (Tactic.rwRule [] `LinearMap.map_smul)
                ","
                (Tactic.rwRule [] `mul_zero)
                ","
                (Tactic.rwRule [] `sub_zero)
                ","
                (Tactic.rwRule [] `sub_self)]
               "]")
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
         [(Tactic.induction'
           "induction'"
           [(Tactic.casesTarget [] `x)]
           ["using" `CliffordAlgebra.leftInduction]
           ["with"
            [(Lean.binderIdent `r)
             (Lean.binderIdent `x)
             (Lean.binderIdent `y)
             (Lean.binderIdent `hx)
             (Lean.binderIdent `hy)
             (Lean.binderIdent `m)
             (Lean.binderIdent `x)
             (Lean.binderIdent `hx)]]
           [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Mathlib.Tactic.tacticSimp_rw__
             "simp_rw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `contract_left_algebra_map) "," (Tactic.rwRule [] `map_zero)]
              "]")
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `map_add)
               ","
               (Tactic.rwRule [] `map_add)
               ","
               (Tactic.rwRule [] `hx)
               ","
               (Tactic.rwRule [] `hy)
               ","
               (Tactic.rwRule [] `add_zero)]
              "]")
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `contract_left_ι_mul)
               ","
               (Tactic.rwRule [] `map_sub)
               ","
               (Tactic.rwRule [] `contract_left_ι_mul)
               ","
               (Tactic.rwRule [] `hx)
               ","
               (Tactic.rwRule [] `LinearMap.map_smul)
               ","
               (Tactic.rwRule [] `mul_zero)
               ","
               (Tactic.rwRule [] `sub_zero)
               ","
               (Tactic.rwRule [] `sub_self)]
              "]")
             [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `contract_left_ι_mul)
           ","
           (Tactic.rwRule [] `map_sub)
           ","
           (Tactic.rwRule [] `contract_left_ι_mul)
           ","
           (Tactic.rwRule [] `hx)
           ","
           (Tactic.rwRule [] `LinearMap.map_smul)
           ","
           (Tactic.rwRule [] `mul_zero)
           ","
           (Tactic.rwRule [] `sub_zero)
           ","
           (Tactic.rwRule [] `sub_self)]
          "]")
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `contract_left_ι_mul)
         ","
         (Tactic.rwRule [] `map_sub)
         ","
         (Tactic.rwRule [] `contract_left_ι_mul)
         ","
         (Tactic.rwRule [] `hx)
         ","
         (Tactic.rwRule [] `LinearMap.map_smul)
         ","
         (Tactic.rwRule [] `mul_zero)
         ","
         (Tactic.rwRule [] `sub_zero)
         ","
         (Tactic.rwRule [] `sub_self)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_self
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearMap.map_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `contract_left_ι_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `contract_left_ι_mul
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
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `map_add)
           ","
           (Tactic.rwRule [] `map_add)
           ","
           (Tactic.rwRule [] `hx)
           ","
           (Tactic.rwRule [] `hy)
           ","
           (Tactic.rwRule [] `add_zero)]
          "]")
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `map_add)
         ","
         (Tactic.rwRule [] `map_add)
         ","
         (Tactic.rwRule [] `hx)
         ","
         (Tactic.rwRule [] `hy)
         ","
         (Tactic.rwRule [] `add_zero)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Mathlib.Tactic.tacticSimp_rw__
         "simp_rw"
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `contract_left_algebra_map) "," (Tactic.rwRule [] `map_zero)]
          "]")
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `contract_left_algebra_map) "," (Tactic.rwRule [] `map_zero)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `contract_left_algebra_map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.induction'
       "induction'"
       [(Tactic.casesTarget [] `x)]
       ["using" `CliffordAlgebra.leftInduction]
       ["with"
        [(Lean.binderIdent `r)
         (Lean.binderIdent `x)
         (Lean.binderIdent `y)
         (Lean.binderIdent `hx)
         (Lean.binderIdent `hy)
         (Lean.binderIdent `m)
         (Lean.binderIdent `x)
         (Lean.binderIdent `hx)]]
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_»
        `d
        "⌋"
        (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_» `d "⌋" `x))
       "="
       (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_»
       `d
       "⌋"
       (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_» `d "⌋" `x))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_»', expected 'CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.term_⌋_._@.LinearAlgebra.CliffordAlgebra.Contraction._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- This is [grinberg_clifford_2016][] Theorem 7 -/
  theorem
    contract_left_contract_left
    ( x : CliffordAlgebra Q ) : d ⌋ d ⌋ x = 0
    :=
      by
        induction' x using CliffordAlgebra.leftInduction with r x y hx hy m x hx
          · simp_rw [ contract_left_algebra_map , map_zero ]
          · rw [ map_add , map_add , hx , hy , add_zero ]
          ·
            rw
              [
                contract_left_ι_mul
                  ,
                  map_sub
                  ,
                  contract_left_ι_mul
                  ,
                  hx
                  ,
                  LinearMap.map_smul
                  ,
                  mul_zero
                  ,
                  sub_zero
                  ,
                  sub_self
                ]
#align clifford_algebra.contract_left_contract_left CliffordAlgebra.contract_left_contract_left

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "This is [grinberg_clifford_2016][] Theorem 13 -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `contract_right_contract_right [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x] [":" (Term.app `CliffordAlgebra [`Q])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_»
          (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_» `x "⌊" `d)
          "⌊"
          `d)
         "="
         (num "0"))))
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
             [(Tactic.rwRule [] `contract_right_eq)
              ","
              (Tactic.rwRule [] `contract_right_eq)
              ","
              (Tactic.rwRule [] `reverse_reverse)
              ","
              (Tactic.rwRule [] `contract_left_contract_left)
              ","
              (Tactic.rwRule [] `map_zero)]
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
            [(Tactic.rwRule [] `contract_right_eq)
             ","
             (Tactic.rwRule [] `contract_right_eq)
             ","
             (Tactic.rwRule [] `reverse_reverse)
             ","
             (Tactic.rwRule [] `contract_left_contract_left)
             ","
             (Tactic.rwRule [] `map_zero)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `contract_right_eq)
         ","
         (Tactic.rwRule [] `contract_right_eq)
         ","
         (Tactic.rwRule [] `reverse_reverse)
         ","
         (Tactic.rwRule [] `contract_left_contract_left)
         ","
         (Tactic.rwRule [] `map_zero)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `contract_left_contract_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `reverse_reverse
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `contract_right_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `contract_right_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_»
        (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_» `x "⌊" `d)
        "⌊"
        `d)
       "="
       (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_»
       (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_» `x "⌊" `d)
       "⌊"
       `d)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_»', expected 'CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.term_⌊_._@.LinearAlgebra.CliffordAlgebra.Contraction._hyg.537'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- This is [grinberg_clifford_2016][] Theorem 13 -/
  theorem
    contract_right_contract_right
    ( x : CliffordAlgebra Q ) : x ⌊ d ⌊ d = 0
    :=
      by
        rw
          [
            contract_right_eq
              ,
              contract_right_eq
              ,
              reverse_reverse
              ,
              contract_left_contract_left
              ,
              map_zero
            ]
#align clifford_algebra.contract_right_contract_right CliffordAlgebra.contract_right_contract_right

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "This is [grinberg_clifford_2016][] Theorem 8 -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `contract_left_comm [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x] [":" (Term.app `CliffordAlgebra [`Q])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_»
          `d
          "⌋"
          (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_» `d' "⌋" `x))
         "="
         («term-_»
          "-"
          (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_»
           `d'
           "⌋"
           (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_» `d "⌋" `x))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.induction'
            "induction'"
            [(Tactic.casesTarget [] `x)]
            ["using" `CliffordAlgebra.leftInduction]
            ["with"
             [(Lean.binderIdent `r)
              (Lean.binderIdent `x)
              (Lean.binderIdent `y)
              (Lean.binderIdent `hx)
              (Lean.binderIdent `hy)
              (Lean.binderIdent `m)
              (Lean.binderIdent `x)
              (Lean.binderIdent `hx)]]
            [])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Mathlib.Tactic.tacticSimp_rw__
              "simp_rw"
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `contract_left_algebra_map)
                ","
                (Tactic.rwRule [] `map_zero)
                ","
                (Tactic.rwRule [] `neg_zero)]
               "]")
              [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `map_add)
                ","
                (Tactic.rwRule [] `map_add)
                ","
                (Tactic.rwRule [] `map_add)
                ","
                (Tactic.rwRule [] `map_add)
                ","
                (Tactic.rwRule [] `hx)
                ","
                (Tactic.rwRule [] `hy)
                ","
                (Tactic.rwRule [] `neg_add)]
               "]")
              [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `contract_left_ι_mul)
                ","
                (Tactic.simpLemma [] [] `map_sub)
                ","
                (Tactic.simpLemma [] [] `LinearMap.map_smul)]
               "]"]
              [])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `neg_sub)
                ","
                (Tactic.rwRule [] `sub_sub_eq_add_sub)
                ","
                (Tactic.rwRule [] `hx)
                ","
                (Tactic.rwRule [] `mul_neg)
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_eq_add_neg)]
               "]")
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
         [(Tactic.induction'
           "induction'"
           [(Tactic.casesTarget [] `x)]
           ["using" `CliffordAlgebra.leftInduction]
           ["with"
            [(Lean.binderIdent `r)
             (Lean.binderIdent `x)
             (Lean.binderIdent `y)
             (Lean.binderIdent `hx)
             (Lean.binderIdent `hy)
             (Lean.binderIdent `m)
             (Lean.binderIdent `x)
             (Lean.binderIdent `hx)]]
           [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Mathlib.Tactic.tacticSimp_rw__
             "simp_rw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `contract_left_algebra_map)
               ","
               (Tactic.rwRule [] `map_zero)
               ","
               (Tactic.rwRule [] `neg_zero)]
              "]")
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `map_add)
               ","
               (Tactic.rwRule [] `map_add)
               ","
               (Tactic.rwRule [] `map_add)
               ","
               (Tactic.rwRule [] `map_add)
               ","
               (Tactic.rwRule [] `hx)
               ","
               (Tactic.rwRule [] `hy)
               ","
               (Tactic.rwRule [] `neg_add)]
              "]")
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `contract_left_ι_mul)
               ","
               (Tactic.simpLemma [] [] `map_sub)
               ","
               (Tactic.simpLemma [] [] `LinearMap.map_smul)]
              "]"]
             [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `neg_sub)
               ","
               (Tactic.rwRule [] `sub_sub_eq_add_sub)
               ","
               (Tactic.rwRule [] `hx)
               ","
               (Tactic.rwRule [] `mul_neg)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_eq_add_neg)]
              "]")
             [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `contract_left_ι_mul)
           ","
           (Tactic.simpLemma [] [] `map_sub)
           ","
           (Tactic.simpLemma [] [] `LinearMap.map_smul)]
          "]"]
         [])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `neg_sub)
           ","
           (Tactic.rwRule [] `sub_sub_eq_add_sub)
           ","
           (Tactic.rwRule [] `hx)
           ","
           (Tactic.rwRule [] `mul_neg)
           ","
           (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_eq_add_neg)]
          "]")
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `neg_sub)
         ","
         (Tactic.rwRule [] `sub_sub_eq_add_sub)
         ","
         (Tactic.rwRule [] `hx)
         ","
         (Tactic.rwRule [] `mul_neg)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_eq_add_neg)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_eq_add_neg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_neg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_sub_eq_add_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `neg_sub
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
        [(Tactic.simpLemma [] [] `contract_left_ι_mul)
         ","
         (Tactic.simpLemma [] [] `map_sub)
         ","
         (Tactic.simpLemma [] [] `LinearMap.map_smul)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearMap.map_smul
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
      `contract_left_ι_mul
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
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `map_add)
           ","
           (Tactic.rwRule [] `map_add)
           ","
           (Tactic.rwRule [] `map_add)
           ","
           (Tactic.rwRule [] `map_add)
           ","
           (Tactic.rwRule [] `hx)
           ","
           (Tactic.rwRule [] `hy)
           ","
           (Tactic.rwRule [] `neg_add)]
          "]")
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `map_add)
         ","
         (Tactic.rwRule [] `map_add)
         ","
         (Tactic.rwRule [] `map_add)
         ","
         (Tactic.rwRule [] `map_add)
         ","
         (Tactic.rwRule [] `hx)
         ","
         (Tactic.rwRule [] `hy)
         ","
         (Tactic.rwRule [] `neg_add)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `neg_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Mathlib.Tactic.tacticSimp_rw__
         "simp_rw"
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `contract_left_algebra_map)
           ","
           (Tactic.rwRule [] `map_zero)
           ","
           (Tactic.rwRule [] `neg_zero)]
          "]")
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `contract_left_algebra_map)
         ","
         (Tactic.rwRule [] `map_zero)
         ","
         (Tactic.rwRule [] `neg_zero)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `neg_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `contract_left_algebra_map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.induction'
       "induction'"
       [(Tactic.casesTarget [] `x)]
       ["using" `CliffordAlgebra.leftInduction]
       ["with"
        [(Lean.binderIdent `r)
         (Lean.binderIdent `x)
         (Lean.binderIdent `y)
         (Lean.binderIdent `hx)
         (Lean.binderIdent `hy)
         (Lean.binderIdent `m)
         (Lean.binderIdent `x)
         (Lean.binderIdent `hx)]]
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_»
        `d
        "⌋"
        (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_» `d' "⌋" `x))
       "="
       («term-_»
        "-"
        (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_»
         `d'
         "⌋"
         (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_» `d "⌋" `x))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_»
       "-"
       (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_»
        `d'
        "⌋"
        (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_» `d "⌋" `x)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_»
       `d'
       "⌋"
       (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_» `d "⌋" `x))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋_»', expected 'CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.term_⌋_._@.LinearAlgebra.CliffordAlgebra.Contraction._hyg.9'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- This is [grinberg_clifford_2016][] Theorem 8 -/
  theorem
    contract_left_comm
    ( x : CliffordAlgebra Q ) : d ⌋ d' ⌋ x = - d' ⌋ d ⌋ x
    :=
      by
        induction' x using CliffordAlgebra.leftInduction with r x y hx hy m x hx
          · simp_rw [ contract_left_algebra_map , map_zero , neg_zero ]
          · rw [ map_add , map_add , map_add , map_add , hx , hy , neg_add ]
          ·
            simp only [ contract_left_ι_mul , map_sub , LinearMap.map_smul ]
              rw [ neg_sub , sub_sub_eq_add_sub , hx , mul_neg , ← sub_eq_add_neg ]
#align clifford_algebra.contract_left_comm CliffordAlgebra.contract_left_comm

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "This is [grinberg_clifford_2016][] Theorem 14 -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `contract_right_comm [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x] [":" (Term.app `CliffordAlgebra [`Q])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_»
          (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_» `x "⌊" `d)
          "⌊"
          `d')
         "="
         («term-_»
          "-"
          (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_»
           (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_» `x "⌊" `d')
           "⌊"
           `d)))))
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
             [(Tactic.rwRule [] `contract_right_eq)
              ","
              (Tactic.rwRule [] `contract_right_eq)
              ","
              (Tactic.rwRule [] `contract_right_eq)
              ","
              (Tactic.rwRule [] `contract_right_eq)
              ","
              (Tactic.rwRule [] `reverse_reverse)
              ","
              (Tactic.rwRule [] `reverse_reverse)
              ","
              (Tactic.rwRule [] `contract_left_comm)
              ","
              (Tactic.rwRule [] `map_neg)]
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
            [(Tactic.rwRule [] `contract_right_eq)
             ","
             (Tactic.rwRule [] `contract_right_eq)
             ","
             (Tactic.rwRule [] `contract_right_eq)
             ","
             (Tactic.rwRule [] `contract_right_eq)
             ","
             (Tactic.rwRule [] `reverse_reverse)
             ","
             (Tactic.rwRule [] `reverse_reverse)
             ","
             (Tactic.rwRule [] `contract_left_comm)
             ","
             (Tactic.rwRule [] `map_neg)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `contract_right_eq)
         ","
         (Tactic.rwRule [] `contract_right_eq)
         ","
         (Tactic.rwRule [] `contract_right_eq)
         ","
         (Tactic.rwRule [] `contract_right_eq)
         ","
         (Tactic.rwRule [] `reverse_reverse)
         ","
         (Tactic.rwRule [] `reverse_reverse)
         ","
         (Tactic.rwRule [] `contract_left_comm)
         ","
         (Tactic.rwRule [] `map_neg)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_neg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `contract_left_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `reverse_reverse
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `reverse_reverse
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `contract_right_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `contract_right_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `contract_right_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `contract_right_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_»
        (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_» `x "⌊" `d)
        "⌊"
        `d')
       "="
       («term-_»
        "-"
        (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_»
         (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_» `x "⌊" `d')
         "⌊"
         `d)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_»
       "-"
       (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_»
        (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_» `x "⌊" `d')
        "⌊"
        `d))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_»
       (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_» `x "⌊" `d')
       "⌊"
       `d)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌊_»', expected 'CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.term_⌊_._@.LinearAlgebra.CliffordAlgebra.Contraction._hyg.537'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- This is [grinberg_clifford_2016][] Theorem 14 -/
  theorem
    contract_right_comm
    ( x : CliffordAlgebra Q ) : x ⌊ d ⌊ d' = - x ⌊ d' ⌊ d
    :=
      by
        rw
          [
            contract_right_eq
              ,
              contract_right_eq
              ,
              contract_right_eq
              ,
              contract_right_eq
              ,
              reverse_reverse
              ,
              reverse_reverse
              ,
              contract_left_comm
              ,
              map_neg
            ]
#align clifford_algebra.contract_right_comm CliffordAlgebra.contract_right_comm

/- TODO:
lemma contract_right_contract_left (x : clifford_algebra Q) : (d ⌋ x) ⌊ d' = d ⌋ (x ⌊ d') :=
-/
end ContractLeft

-- mathport name: «expr ⌋ »
local infixl:70 "⌋" => contractLeft

-- mathport name: «expr ⌊ »
local infixl:70 "⌊" => contractRight

/-- Auxiliary construction for `clifford_algebra.change_form` -/
@[simps]
def changeFormAux (B : BilinForm R M) : M →ₗ[R] CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q :=
  haveI v_mul := (Algebra.lmul R (CliffordAlgebra Q)).toLinearMap ∘ₗ ι Q
  v_mul - contract_left ∘ₗ B.to_lin
#align clifford_algebra.change_form_aux CliffordAlgebra.changeFormAux

theorem change_form_aux_change_form_aux (B : BilinForm R M) (v : M) (x : CliffordAlgebra Q) :
    changeFormAux Q B v (changeFormAux Q B v x) = (Q v - B v v) • x :=
  by
  simp only [change_form_aux_apply_apply]
  rw [mul_sub, ← mul_assoc, ι_sq_scalar, map_sub, contract_left_ι_mul, ← sub_add, sub_sub_sub_comm,
    ← Algebra.smul_def, BilinForm.to_lin_apply, sub_self, sub_zero, contract_left_contract_left,
    add_zero, sub_smul]
#align
  clifford_algebra.change_form_aux_change_form_aux CliffordAlgebra.change_form_aux_change_form_aux

variable {Q}

variable {Q' Q'' : QuadraticForm R M} {B B' : BilinForm R M}

variable (h : B.toQuadraticForm = Q' - Q) (h' : B'.toQuadraticForm = Q'' - Q')

/-- Convert between two algebras of different quadratic form, sending vector to vectors, scalars to
scalars, and adjusting products by a contraction term.

This is $\lambda_B$ from [bourbaki2007][] $9 Lemma 2. -/
def changeForm (h : B.toQuadraticForm = Q' - Q) : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q' :=
  foldr Q (changeFormAux Q' B)
    (fun m x =>
      (change_form_aux_change_form_aux Q' B m x).trans <|
        by
        dsimp [← BilinForm.to_quadratic_form_apply]
        rw [h, QuadraticForm.sub_apply, sub_sub_cancel])
    1
#align clifford_algebra.change_form CliffordAlgebra.changeForm

/-- Auxiliary lemma used as an argument to `clifford_algebra.change_form` -/
theorem changeForm.zero_proof : (0 : BilinForm R M).toQuadraticForm = Q - Q :=
  (sub_self _).symm
#align clifford_algebra.change_form.zero_proof CliffordAlgebra.changeForm.zero_proof

/-- Auxiliary lemma used as an argument to `clifford_algebra.change_form` -/
theorem changeForm.add_proof : (B + B').toQuadraticForm = Q'' - Q :=
  (congr_arg₂ (· + ·) h h').trans <| sub_add_sub_cancel' _ _ _
#align clifford_algebra.change_form.add_proof CliffordAlgebra.changeForm.add_proof

/-- Auxiliary lemma used as an argument to `clifford_algebra.change_form` -/
theorem changeForm.neg_proof : (-B).toQuadraticForm = Q - Q' :=
  (congr_arg Neg.neg h).trans <| neg_sub _ _
#align clifford_algebra.change_form.neg_proof CliffordAlgebra.changeForm.neg_proof

theorem changeForm.associated_neg_proof [Invertible (2 : R)] :
    (-Q).Associated.toQuadraticForm = 0 - Q := by simp [QuadraticForm.to_quadratic_form_associated]
#align
  clifford_algebra.change_form.associated_neg_proof CliffordAlgebra.changeForm.associated_neg_proof

@[simp]
theorem change_form_algebra_map (r : R) : changeForm h (algebraMap R _ r) = algebraMap R _ r :=
  (foldr_algebra_map _ _ _ _ _).trans <| Eq.symm <| Algebra.algebra_map_eq_smul_one r
#align clifford_algebra.change_form_algebra_map CliffordAlgebra.change_form_algebra_map

@[simp]
theorem change_form_one : changeForm h (1 : CliffordAlgebra Q) = 1 := by
  simpa using change_form_algebra_map h (1 : R)
#align clifford_algebra.change_form_one CliffordAlgebra.change_form_one

@[simp]
theorem change_form_ι (m : M) : changeForm h (ι _ m) = ι _ m :=
  (foldr_ι _ _ _ _ _).trans <|
    Eq.symm <| by rw [change_form_aux_apply_apply, mul_one, contract_left_one, sub_zero]
#align clifford_algebra.change_form_ι CliffordAlgebra.change_form_ι

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `change_form_ι_mul [])
      (Command.declSig
       [(Term.explicitBinder "(" [`m] [":" `M] [] ")")
        (Term.explicitBinder "(" [`x] [":" (Term.app `CliffordAlgebra [`Q])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `changeForm [`h («term_*_» (Term.app `ι [(Term.hole "_") `m]) "*" `x)])
         "="
         («term_-_»
          («term_*_» (Term.app `ι [(Term.hole "_") `m]) "*" (Term.app `changeForm [`h `x]))
          "-"
          (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋__1»
           (Term.app `BilinForm.toLin [`B `m])
           "⌋"
           (Term.app `changeForm [`h `x]))))))
      (Command.declValSimple
       ":="
       («term_<|_»
        (Term.proj
         (Term.app
          `foldr_mul
          [(Term.hole "_")
           (Term.hole "_")
           (Term.hole "_")
           (Term.hole "_")
           (Term.hole "_")
           (Term.hole "_")])
         "."
         `trans)
        "<|"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `foldr_ι)] "]") [])
            ";"
            (Tactic.tacticRfl "rfl")]))))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj
        (Term.app
         `foldr_mul
         [(Term.hole "_")
          (Term.hole "_")
          (Term.hole "_")
          (Term.hole "_")
          (Term.hole "_")
          (Term.hole "_")])
        "."
        `trans)
       "<|"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `foldr_ι)] "]") [])
           ";"
           (Tactic.tacticRfl "rfl")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `foldr_ι)] "]") [])
          ";"
          (Tactic.tacticRfl "rfl")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `foldr_ι)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `foldr_ι
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj
       (Term.app
        `foldr_mul
        [(Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")])
       "."
       `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `foldr_mul
       [(Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `foldr_mul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `foldr_mul
      [(Term.hole "_")
       (Term.hole "_")
       (Term.hole "_")
       (Term.hole "_")
       (Term.hole "_")
       (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app `changeForm [`h («term_*_» (Term.app `ι [(Term.hole "_") `m]) "*" `x)])
       "="
       («term_-_»
        («term_*_» (Term.app `ι [(Term.hole "_") `m]) "*" (Term.app `changeForm [`h `x]))
        "-"
        (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋__1»
         (Term.app `BilinForm.toLin [`B `m])
         "⌋"
         (Term.app `changeForm [`h `x]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_»
       («term_*_» (Term.app `ι [(Term.hole "_") `m]) "*" (Term.app `changeForm [`h `x]))
       "-"
       (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋__1»
        (Term.app `BilinForm.toLin [`B `m])
        "⌋"
        (Term.app `changeForm [`h `x])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋__1»
       (Term.app `BilinForm.toLin [`B `m])
       "⌋"
       (Term.app `changeForm [`h `x]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋__1»', expected 'CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.term_⌋__1._@.LinearAlgebra.CliffordAlgebra.Contraction._hyg.1054'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  change_form_ι_mul
  ( m : M ) ( x : CliffordAlgebra Q )
    : changeForm h ι _ m * x = ι _ m * changeForm h x - BilinForm.toLin B m ⌋ changeForm h x
  := foldr_mul _ _ _ _ _ _ . trans <| by rw [ foldr_ι ] ; rfl
#align clifford_algebra.change_form_ι_mul CliffordAlgebra.change_form_ι_mul

theorem change_form_ι_mul_ι (m₁ m₂ : M) :
    changeForm h (ι _ m₁ * ι _ m₂) = ι _ m₁ * ι _ m₂ - algebraMap _ _ (B m₁ m₂) := by
  rw [change_form_ι_mul, change_form_ι, contract_left_ι, BilinForm.to_lin_apply]
#align clifford_algebra.change_form_ι_mul_ι CliffordAlgebra.change_form_ι_mul_ι

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "Theorem 23 of [grinberg_clifford_2016][] -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `change_form_contract_left [])
      (Command.declSig
       [(Term.explicitBinder "(" [`d] [":" (Term.app `Module.Dual [`R `M])] [] ")")
        (Term.explicitBinder "(" [`x] [":" (Term.app `CliffordAlgebra [`Q])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          `changeForm
          [`h (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋__1» `d "⌋" `x)])
         "="
         (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋__1»
          `d
          "⌋"
          (Term.app `changeForm [`h `x])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.induction'
            "induction'"
            [(Tactic.casesTarget [] `x)]
            ["using" `CliffordAlgebra.leftInduction]
            ["with"
             [(Lean.binderIdent `r)
              (Lean.binderIdent `x)
              (Lean.binderIdent `y)
              (Lean.binderIdent `hx)
              (Lean.binderIdent `hy)
              (Lean.binderIdent `m)
              (Lean.binderIdent `x)
              (Lean.binderIdent `hx)]]
            [])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `contract_left_algebra_map)
                ","
                (Tactic.simpLemma [] [] `change_form_algebra_map)
                ","
                (Tactic.simpLemma [] [] `map_zero)]
               "]"]
              [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `map_add)
                ","
                (Tactic.rwRule [] `map_add)
                ","
                (Tactic.rwRule [] `map_add)
                ","
                (Tactic.rwRule [] `map_add)
                ","
                (Tactic.rwRule [] `hx)
                ","
                (Tactic.rwRule [] `hy)]
               "]")
              [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `contract_left_ι_mul)
                ","
                (Tactic.simpLemma [] [] `change_form_ι_mul)
                ","
                (Tactic.simpLemma [] [] `map_sub)
                ","
                (Tactic.simpLemma [] [] `LinearMap.map_smul)]
               "]"]
              [])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hx)
                ","
                (Tactic.rwRule [] `contract_left_comm)
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_add)
                ","
                (Tactic.rwRule [] `sub_neg_eq_add)
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hx)]
               "]")
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
         [(Tactic.induction'
           "induction'"
           [(Tactic.casesTarget [] `x)]
           ["using" `CliffordAlgebra.leftInduction]
           ["with"
            [(Lean.binderIdent `r)
             (Lean.binderIdent `x)
             (Lean.binderIdent `y)
             (Lean.binderIdent `hx)
             (Lean.binderIdent `hy)
             (Lean.binderIdent `m)
             (Lean.binderIdent `x)
             (Lean.binderIdent `hx)]]
           [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `contract_left_algebra_map)
               ","
               (Tactic.simpLemma [] [] `change_form_algebra_map)
               ","
               (Tactic.simpLemma [] [] `map_zero)]
              "]"]
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `map_add)
               ","
               (Tactic.rwRule [] `map_add)
               ","
               (Tactic.rwRule [] `map_add)
               ","
               (Tactic.rwRule [] `map_add)
               ","
               (Tactic.rwRule [] `hx)
               ","
               (Tactic.rwRule [] `hy)]
              "]")
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `contract_left_ι_mul)
               ","
               (Tactic.simpLemma [] [] `change_form_ι_mul)
               ","
               (Tactic.simpLemma [] [] `map_sub)
               ","
               (Tactic.simpLemma [] [] `LinearMap.map_smul)]
              "]"]
             [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hx)
               ","
               (Tactic.rwRule [] `contract_left_comm)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_add)
               ","
               (Tactic.rwRule [] `sub_neg_eq_add)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hx)]
              "]")
             [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `contract_left_ι_mul)
           ","
           (Tactic.simpLemma [] [] `change_form_ι_mul)
           ","
           (Tactic.simpLemma [] [] `map_sub)
           ","
           (Tactic.simpLemma [] [] `LinearMap.map_smul)]
          "]"]
         [])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hx)
           ","
           (Tactic.rwRule [] `contract_left_comm)
           ","
           (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_add)
           ","
           (Tactic.rwRule [] `sub_neg_eq_add)
           ","
           (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hx)]
          "]")
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hx)
         ","
         (Tactic.rwRule [] `contract_left_comm)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_add)
         ","
         (Tactic.rwRule [] `sub_neg_eq_add)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hx)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_neg_eq_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `contract_left_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
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
        [(Tactic.simpLemma [] [] `contract_left_ι_mul)
         ","
         (Tactic.simpLemma [] [] `change_form_ι_mul)
         ","
         (Tactic.simpLemma [] [] `map_sub)
         ","
         (Tactic.simpLemma [] [] `LinearMap.map_smul)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearMap.map_smul
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
      `change_form_ι_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `contract_left_ι_mul
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
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `map_add)
           ","
           (Tactic.rwRule [] `map_add)
           ","
           (Tactic.rwRule [] `map_add)
           ","
           (Tactic.rwRule [] `map_add)
           ","
           (Tactic.rwRule [] `hx)
           ","
           (Tactic.rwRule [] `hy)]
          "]")
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `map_add)
         ","
         (Tactic.rwRule [] `map_add)
         ","
         (Tactic.rwRule [] `map_add)
         ","
         (Tactic.rwRule [] `map_add)
         ","
         (Tactic.rwRule [] `hx)
         ","
         (Tactic.rwRule [] `hy)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
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
          [(Tactic.simpLemma [] [] `contract_left_algebra_map)
           ","
           (Tactic.simpLemma [] [] `change_form_algebra_map)
           ","
           (Tactic.simpLemma [] [] `map_zero)]
          "]"]
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `contract_left_algebra_map)
         ","
         (Tactic.simpLemma [] [] `change_form_algebra_map)
         ","
         (Tactic.simpLemma [] [] `map_zero)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `change_form_algebra_map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `contract_left_algebra_map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.induction'
       "induction'"
       [(Tactic.casesTarget [] `x)]
       ["using" `CliffordAlgebra.leftInduction]
       ["with"
        [(Lean.binderIdent `r)
         (Lean.binderIdent `x)
         (Lean.binderIdent `y)
         (Lean.binderIdent `hx)
         (Lean.binderIdent `hy)
         (Lean.binderIdent `m)
         (Lean.binderIdent `x)
         (Lean.binderIdent `hx)]]
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        `changeForm
        [`h (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋__1» `d "⌋" `x)])
       "="
       (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋__1»
        `d
        "⌋"
        (Term.app `changeForm [`h `x])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋__1»
       `d
       "⌋"
       (Term.app `changeForm [`h `x]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.«term_⌋__1»', expected 'CliffordAlgebra.LinearAlgebra.CliffordAlgebra.Contraction.term_⌋__1._@.LinearAlgebra.CliffordAlgebra.Contraction._hyg.1054'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Theorem 23 of [grinberg_clifford_2016][] -/
  theorem
    change_form_contract_left
    ( d : Module.Dual R M ) ( x : CliffordAlgebra Q ) : changeForm h d ⌋ x = d ⌋ changeForm h x
    :=
      by
        induction' x using CliffordAlgebra.leftInduction with r x y hx hy m x hx
          · simp only [ contract_left_algebra_map , change_form_algebra_map , map_zero ]
          · rw [ map_add , map_add , map_add , map_add , hx , hy ]
          ·
            simp only [ contract_left_ι_mul , change_form_ι_mul , map_sub , LinearMap.map_smul ]
              rw [ ← hx , contract_left_comm , ← sub_add , sub_neg_eq_add , ← hx ]
#align clifford_algebra.change_form_contract_left CliffordAlgebra.change_form_contract_left

theorem change_form_self_apply (x : CliffordAlgebra Q) : changeForm changeForm.zero_proof x = x :=
  by
  induction' x using CliffordAlgebra.leftInduction with r x y hx hy m x hx
  · simp_rw [change_form_algebra_map]
  · rw [map_add, hx, hy]
  ·
    rw [change_form_ι_mul, hx, map_zero, LinearMap.zero_apply, map_zero, LinearMap.zero_apply,
      sub_zero]
#align clifford_algebra.change_form_self_apply CliffordAlgebra.change_form_self_apply

@[simp]
theorem change_form_self :
    changeForm changeForm.zero_proof = (LinearMap.id : CliffordAlgebra Q →ₗ[R] _) :=
  LinearMap.ext <| change_form_self_apply
#align clifford_algebra.change_form_self CliffordAlgebra.change_form_self

/-- This is [bourbaki2007][] $9 Lemma 3. -/
theorem change_form_change_form (x : CliffordAlgebra Q) :
    changeForm h' (changeForm h x) = changeForm (changeForm.add_proof h h') x :=
  by
  induction' x using CliffordAlgebra.leftInduction with r x y hx hy m x hx
  · simp_rw [change_form_algebra_map]
  · rw [map_add, map_add, map_add, hx, hy]
  ·
    rw [change_form_ι_mul, map_sub, change_form_ι_mul, change_form_ι_mul, hx, sub_sub, map_add,
      LinearMap.add_apply, map_add, LinearMap.add_apply, change_form_contract_left, hx,
      add_comm (_ : CliffordAlgebra Q'')]
#align clifford_algebra.change_form_change_form CliffordAlgebra.change_form_change_form

theorem change_form_comp_change_form :
    (changeForm h').comp (changeForm h) = changeForm (changeForm.add_proof h h') :=
  LinearMap.ext <| change_form_change_form _ _
#align clifford_algebra.change_form_comp_change_form CliffordAlgebra.change_form_comp_change_form

/-- Any two algebras whose quadratic forms differ by a bilinear form are isomorphic as modules.

This is $\bar \lambda_B$ from [bourbaki2007][] $9 Proposition 3. -/
@[simps apply]
def changeFormEquiv : CliffordAlgebra Q ≃ₗ[R] CliffordAlgebra Q' :=
  { changeForm h with
    toFun := changeForm h
    invFun := changeForm (changeForm.neg_proof h)
    left_inv := fun x =>
      (change_form_change_form _ _ x).trans <| by simp_rw [add_right_neg, change_form_self_apply]
    right_inv := fun x =>
      (change_form_change_form _ _ x).trans <| by simp_rw [add_left_neg, change_form_self_apply] }
#align clifford_algebra.change_form_equiv CliffordAlgebra.changeFormEquiv

@[simp]
theorem change_form_equiv_symm :
    (changeFormEquiv h).symm = changeFormEquiv (changeForm.neg_proof h) :=
  LinearEquiv.ext fun x => (rfl : changeForm _ x = changeForm _ x)
#align clifford_algebra.change_form_equiv_symm CliffordAlgebra.change_form_equiv_symm

variable (Q)

/-- The module isomorphism to the exterior algebra.

Note that this holds more generally when `Q` is divisible by two, rather than only when `1` is
divisible by two; but that would be more awkward to use. -/
@[simp]
def equivExterior [Invertible (2 : R)] : CliffordAlgebra Q ≃ₗ[R] ExteriorAlgebra R M :=
  changeFormEquiv changeForm.associated_neg_proof
#align clifford_algebra.equiv_exterior CliffordAlgebra.equivExterior

end CliffordAlgebra

