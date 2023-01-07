/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.star.chsh
! leanprover-community/mathlib commit 6afc9b06856ad973f6a2619e3e8a0a8d537a58f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Star.Basic
import Mathbin.Data.Complex.IsROrC

/-!
# The Clauser-Horne-Shimony-Holt inequality and Tsirelson's inequality.

We establish a version of the Clauser-Horne-Shimony-Holt (CHSH) inequality
(which is a generalization of Bell's inequality).
This is a foundational result which implies that
quantum mechanics is not a local hidden variable theory.

As usually stated the CHSH inequality requires substantial language from physics and probability,
but it is possible to give a statement that is purely about ordered `*`-algebras.
We do that here, to avoid as many practical and logical dependencies as possible.
Since the algebra of observables of any quantum system is an ordered `*`-algebra
(in particular a von Neumann algebra) this is a strict generalization of the usual statement.

Let `R` be a `*`-ring.

A CHSH tuple in `R` consists of
* four elements `A₀ A₁ B₀ B₁ : R`, such that
* each `Aᵢ` and `Bⱼ` is a self-adjoint involution, and
* the `Aᵢ` commute with the `Bⱼ`.

The physical interpretation is that the four elements are observables (hence self-adjoint)
that take values ±1 (hence involutions), and that the `Aᵢ` are spacelike separated from the `Bⱼ`
(and hence commute).

The CHSH inequality says that when `R` is an ordered `*`-ring
(that is, a `*`-ring which is ordered, and for every `r : R`, `0 ≤ star r * r`),
which is moreover *commutative*, we have
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2`

On the other hand, Tsirelson's inequality says that for any ordered `*`-ring we have
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2√2`

(A caveat: in the commutative case we need 2⁻¹ in the ring,
and in the noncommutative case we need √2 and √2⁻¹.
To keep things simple we just assume our rings are ℝ-algebras.)

The proofs I've seen in the literature either
assume a significant framework for quantum mechanics,
or assume the ring is a `C^*`-algebra.
In the `C^*`-algebra case,
the order structure is completely determined by the `*`-algebra structure:
`0 ≤ A` iff there exists some `B` so `A = star B * B`.
There's a nice proof of both bounds in this setting at
https://en.wikipedia.org/wiki/Tsirelson%27s_bound
The proof given here is purely algebraic.

## Future work

One can show that Tsirelson's inequality is tight.
In the `*`-ring of n-by-n complex matrices, if `A ≤ λ I` for some `λ : ℝ`,
then every eigenvalue has absolute value at most `λ`.
There is a CHSH tuple in 4-by-4 matrices such that
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁` has `2√2` as an eigenvalue.

## References

* [Clauser, Horne, Shimony, Holt,
  *Proposed experiment to test local hidden-variable theories*][zbMATH06785026]
* [Bell, *On the Einstein Podolsky Rosen Paradox*][MR3790629]
* [Tsirelson, *Quantum generalizations of Bell's inequality*][MR577178]

-/


universe u

/-- A CHSH tuple in a *-monoid consists of 4 self-adjoint involutions `A₀ A₁ B₀ B₁` such that
the `Aᵢ` commute with the `Bⱼ`.

The physical interpretation is that `A₀` and `A₁` are a pair of boolean observables which
are spacelike separated from another pair `B₀` and `B₁` of boolean observables.
-/
@[nolint has_nonempty_instance]
structure IsCHSHTuple {R} [Monoid R] [StarSemigroup R] (A₀ A₁ B₀ B₁ : R) where
  A₀_inv : A₀ ^ 2 = 1
  A₁_inv : A₁ ^ 2 = 1
  B₀_inv : B₀ ^ 2 = 1
  B₁_inv : B₁ ^ 2 = 1
  A₀_sa : star A₀ = A₀
  A₁_sa : star A₁ = A₁
  B₀_sa : star B₀ = B₀
  B₁_sa : star B₁ = B₁
  A₀B₀_commutes : A₀ * B₀ = B₀ * A₀
  A₀B₁_commutes : A₀ * B₁ = B₁ * A₀
  A₁B₀_commutes : A₁ * B₀ = B₀ * A₁
  A₁B₁_commutes : A₁ * B₁ = B₁ * A₁
#align is_CHSH_tuple IsCHSHTuple

variable {R : Type u}

theorem CHSH_id [CommRing R] {A₀ A₁ B₀ B₁ : R} (A₀_inv : A₀ ^ 2 = 1) (A₁_inv : A₁ ^ 2 = 1)
    (B₀_inv : B₀ ^ 2 = 1) (B₁_inv : B₁ ^ 2 = 1) :
    (2 - A₀ * B₀ - A₀ * B₁ - A₁ * B₀ + A₁ * B₁) * (2 - A₀ * B₀ - A₀ * B₁ - A₁ * B₀ + A₁ * B₁) =
      4 * (2 - A₀ * B₀ - A₀ * B₁ - A₁ * B₀ + A₁ * B₁) :=
  by
  -- If we had a Gröbner basis algorithm, this would be trivial.
  -- Without one, it is somewhat tedious!
  rw [← sub_eq_zero]
  repeat'
    ring_nf
    simp only [A₁_inv, B₁_inv, sub_eq_add_neg, add_mul, mul_add, sub_mul, mul_sub, add_assoc,
      neg_add, neg_sub, sub_add, sub_sub, neg_mul, ← sq, A₀_inv, B₀_inv, ← sq, ← mul_assoc, one_mul,
      mul_one, add_right_neg, add_zero, sub_eq_add_neg, A₀_inv, mul_one, add_right_neg, zero_mul]
#align CHSH_id CHSH_id

/-- Given a CHSH tuple (A₀, A₁, B₀, B₁) in a *commutative* ordered `*`-algebra over ℝ,
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2`.

(We could work over ℤ[⅟2] if we wanted to!)
-/
theorem CHSH_inequality_of_comm [OrderedCommRing R] [StarOrderedRing R] [Algebra ℝ R]
    [OrderedSmul ℝ R] (A₀ A₁ B₀ B₁ : R) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2 :=
  by
  let P := 2 - A₀ * B₀ - A₀ * B₁ - A₁ * B₀ + A₁ * B₁
  have i₁ : 0 ≤ P :=
    by
    have idem : P * P = 4 * P := CHSH_id T.A₀_inv T.A₁_inv T.B₀_inv T.B₁_inv
    have idem' : P = (1 / 4 : ℝ) • (P * P) :=
      by
      have h : 4 * P = (4 : ℝ) • P := by simp [Algebra.smul_def]
      rw [idem, h, ← mul_smul]
      norm_num
    have sa : star P = P := by
      dsimp [P]
      simp only [star_add, star_sub, star_mul, star_bit0, star_one, T.A₀_sa, T.A₁_sa, T.B₀_sa,
        T.B₁_sa, mul_comm B₀, mul_comm B₁]
    rw [idem']
    conv_rhs =>
      congr
      skip
      congr
      rw [← sa]
    convert smul_le_smul_of_nonneg (star_mul_self_nonneg : 0 ≤ star P * P) _
    · simp
    · infer_instance
    · norm_num
  apply le_of_sub_nonneg
  simpa only [sub_add_eq_sub_sub, ← sub_add] using i₁
#align CHSH_inequality_of_comm CHSH_inequality_of_comm

/-!
We now prove some rather specialized lemmas in preparation for the Tsirelson inequality,
which we hide in a namespace as they are unlikely to be useful elsewhere.
-/


-- mathport name: «expr√2»
local notation "√2" => (Real.sqrt 2 : ℝ)

namespace tsirelson_inequality

/-!
Before proving Tsirelson's bound,
we prepare some easy lemmas about √2.
-/


/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `tsirelson_inequality_aux [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term_=_»
         («term_*_»
          (Algebra.Star.Chsh.«term√2» "√2")
          "*"
          («term_^_» (Algebra.Star.Chsh.«term√2» "√2") "^" (num "3")))
         "="
         («term_*_»
          (Algebra.Star.Chsh.«term√2» "√2")
          "*"
          («term_+_»
           («term_*_» (num "2") "*" («term_⁻¹» (Algebra.Star.Chsh.«term√2» "√2") "⁻¹"))
           "+"
           («term_*_»
            (num "4")
            "*"
            («term_*_»
             («term_⁻¹» (Algebra.Star.Chsh.«term√2» "√2") "⁻¹")
             "*"
             («term_⁻¹» (num "2") "⁻¹"))))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Mathlib.Tactic.RingNF.ringNF "ring_nf" [] [] [])
           ";"
           (Tactic.fieldSimp
            "field_simp"
            []
            []
            []
            [(Tactic.simpArgs
              "["
              [(Tactic.simpLemma
                []
                []
                (Term.app
                 (Term.proj
                  (Term.app (Term.explicit "@" `Real.sqrt_pos) [(num "2")])
                  "."
                  (fieldIdx "2"))
                 [(Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))]))]
              "]")]
            [])
           []
           (Tactic.«tactic_<;>_»
            (Tactic.«tactic_<;>_»
             (convert
              "convert"
              []
              (Term.app
               `congr_arg
               [(Term.paren "(" («term_^_» (Term.cdot "·") "^" (num "2")) ")")
                (Term.app
                 (Term.explicit "@" `Real.sq_sqrt)
                 [(num "2")
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))])])
              ["using" (num "1")])
             "<;>"
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["[" [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `pow_mul)] "]"]
              []))
            "<;>"
            (Mathlib.Tactic.normNum "norm_num" [] [] []))])))
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
         [(Mathlib.Tactic.RingNF.ringNF "ring_nf" [] [] [])
          ";"
          (Tactic.fieldSimp
           "field_simp"
           []
           []
           []
           [(Tactic.simpArgs
             "["
             [(Tactic.simpLemma
               []
               []
               (Term.app
                (Term.proj
                 (Term.app (Term.explicit "@" `Real.sqrt_pos) [(num "2")])
                 "."
                 (fieldIdx "2"))
                [(Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))]))]
             "]")]
           [])
          []
          (Tactic.«tactic_<;>_»
           (Tactic.«tactic_<;>_»
            (convert
             "convert"
             []
             (Term.app
              `congr_arg
              [(Term.paren "(" («term_^_» (Term.cdot "·") "^" (num "2")) ")")
               (Term.app
                (Term.explicit "@" `Real.sq_sqrt)
                [(num "2")
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))])])
             ["using" (num "1")])
            "<;>"
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["[" [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `pow_mul)] "]"]
             []))
           "<;>"
           (Mathlib.Tactic.normNum "norm_num" [] [] []))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.«tactic_<;>_»
        (convert
         "convert"
         []
         (Term.app
          `congr_arg
          [(Term.paren "(" («term_^_» (Term.cdot "·") "^" (num "2")) ")")
           (Term.app
            (Term.explicit "@" `Real.sq_sqrt)
            [(num "2")
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))])])
         ["using" (num "1")])
        "<;>"
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["[" [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `pow_mul)] "]"]
         []))
       "<;>"
       (Mathlib.Tactic.normNum "norm_num" [] [] []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.normNum "norm_num" [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.«tactic_<;>_»
       (convert
        "convert"
        []
        (Term.app
         `congr_arg
         [(Term.paren "(" («term_^_» (Term.cdot "·") "^" (num "2")) ")")
          (Term.app
           (Term.explicit "@" `Real.sq_sqrt)
           [(num "2")
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))])])
        ["using" (num "1")])
       "<;>"
       (Tactic.simp
        "simp"
        []
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `pow_mul)] "]"]
        []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["[" [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `pow_mul)] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pow_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (convert
       "convert"
       []
       (Term.app
        `congr_arg
        [(Term.paren "(" («term_^_» (Term.cdot "·") "^" (num "2")) ")")
         (Term.app
          (Term.explicit "@" `Real.sq_sqrt)
          [(num "2")
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))])])
       ["using" (num "1")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `congr_arg
       [(Term.paren "(" («term_^_» (Term.cdot "·") "^" (num "2")) ")")
        (Term.app
         (Term.explicit "@" `Real.sq_sqrt)
         [(num "2")
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicit "@" `Real.sq_sqrt)
       [(num "2")
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.normNum "norm_num" [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `Real.sq_sqrt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Real.sq_sqrt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.explicit "@" `Real.sq_sqrt)
      [(num "2")
       (Term.paren
        "("
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
        ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.paren "(" («term_^_» (Term.cdot "·") "^" (num "2")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» (Term.cdot "·") "^" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.cdot "·")
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `congr_arg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.fieldSimp
       "field_simp"
       []
       []
       []
       [(Tactic.simpArgs
         "["
         [(Tactic.simpLemma
           []
           []
           (Term.app
            (Term.proj (Term.app (Term.explicit "@" `Real.sqrt_pos) [(num "2")]) "." (fieldIdx "2"))
            [(Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))]))]
         "]")]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app (Term.explicit "@" `Real.sqrt_pos) [(num "2")]) "." (fieldIdx "2"))
       [(Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.normNum "norm_num" [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app (Term.explicit "@" `Real.sqrt_pos) [(num "2")]) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.explicit "@" `Real.sqrt_pos) [(num "2")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `Real.sqrt_pos)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Real.sqrt_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.explicit "@" `Real.sqrt_pos) [(num "2")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.RingNF.ringNF "ring_nf" [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       («term_*_»
        (Algebra.Star.Chsh.«term√2» "√2")
        "*"
        («term_^_» (Algebra.Star.Chsh.«term√2» "√2") "^" (num "3")))
       "="
       («term_*_»
        (Algebra.Star.Chsh.«term√2» "√2")
        "*"
        («term_+_»
         («term_*_» (num "2") "*" («term_⁻¹» (Algebra.Star.Chsh.«term√2» "√2") "⁻¹"))
         "+"
         («term_*_»
          (num "4")
          "*"
          («term_*_»
           («term_⁻¹» (Algebra.Star.Chsh.«term√2» "√2") "⁻¹")
           "*"
           («term_⁻¹» (num "2") "⁻¹"))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Algebra.Star.Chsh.«term√2» "√2")
       "*"
       («term_+_»
        («term_*_» (num "2") "*" («term_⁻¹» (Algebra.Star.Chsh.«term√2» "√2") "⁻¹"))
        "+"
        («term_*_»
         (num "4")
         "*"
         («term_*_»
          («term_⁻¹» (Algebra.Star.Chsh.«term√2» "√2") "⁻¹")
          "*"
          («term_⁻¹» (num "2") "⁻¹")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       («term_*_» (num "2") "*" («term_⁻¹» (Algebra.Star.Chsh.«term√2» "√2") "⁻¹"))
       "+"
       («term_*_»
        (num "4")
        "*"
        («term_*_»
         («term_⁻¹» (Algebra.Star.Chsh.«term√2» "√2") "⁻¹")
         "*"
         («term_⁻¹» (num "2") "⁻¹"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (num "4")
       "*"
       («term_*_»
        («term_⁻¹» (Algebra.Star.Chsh.«term√2» "√2") "⁻¹")
        "*"
        («term_⁻¹» (num "2") "⁻¹")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» («term_⁻¹» (Algebra.Star.Chsh.«term√2» "√2") "⁻¹") "*" («term_⁻¹» (num "2") "⁻¹"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⁻¹» (num "2") "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_⁻¹» (Algebra.Star.Chsh.«term√2» "√2") "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Algebra.Star.Chsh.«term√2» "√2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Star.Chsh.«term√2»', expected 'Algebra.Star.Chsh.term√2._@.Algebra.Star.Chsh._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  tsirelson_inequality_aux
  : √2 * √2 ^ 3 = √2 * 2 * √2 ⁻¹ + 4 * √2 ⁻¹ * 2 ⁻¹
  :=
    by
      ring_nf
        ;
        field_simp [ @ Real.sqrt_pos 2 . 2 by norm_num ]
        convert congr_arg ( · ^ 2 ) @ Real.sq_sqrt 2 by norm_num using 1 <;> simp only [ ← pow_mul ]
          <;>
          norm_num
#align tsirelson_inequality.tsirelson_inequality_aux TsirelsonInequality.tsirelson_inequality_aux

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `sqrt_two_inv_mul_self [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        («term_=_»
         («term_*_»
          («term_⁻¹» (Algebra.Star.Chsh.«term√2» "√2") "⁻¹")
          "*"
          («term_⁻¹» (Algebra.Star.Chsh.«term√2» "√2") "⁻¹"))
         "="
         (Term.typeAscription
          "("
          («term_⁻¹» (num "2") "⁻¹")
          ":"
          [(Data.Real.Basic.termℝ "ℝ")]
          ")"))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_inv)] "]")
            [])
           []
           (Mathlib.Tactic.normNum "norm_num" [] [] [])])))
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
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_inv)] "]")
           [])
          []
          (Mathlib.Tactic.normNum "norm_num" [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.normNum "norm_num" [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_inv)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_inv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       («term_*_»
        («term_⁻¹» (Algebra.Star.Chsh.«term√2» "√2") "⁻¹")
        "*"
        («term_⁻¹» (Algebra.Star.Chsh.«term√2» "√2") "⁻¹"))
       "="
       (Term.typeAscription "(" («term_⁻¹» (num "2") "⁻¹") ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" («term_⁻¹» (num "2") "⁻¹") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⁻¹» (num "2") "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_*_»
       («term_⁻¹» (Algebra.Star.Chsh.«term√2» "√2") "⁻¹")
       "*"
       («term_⁻¹» (Algebra.Star.Chsh.«term√2» "√2") "⁻¹"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⁻¹» (Algebra.Star.Chsh.«term√2» "√2") "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Algebra.Star.Chsh.«term√2» "√2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Star.Chsh.«term√2»', expected 'Algebra.Star.Chsh.term√2._@.Algebra.Star.Chsh._hyg.5'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem sqrt_two_inv_mul_self : √2 ⁻¹ * √2 ⁻¹ = ( 2 ⁻¹ : ℝ ) := by rw [ ← mul_inv ] norm_num
#align tsirelson_inequality.sqrt_two_inv_mul_self TsirelsonInequality.sqrt_two_inv_mul_self

end tsirelson_inequality

open tsirelson_inequality

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "In a noncommutative ordered `*`-algebra over ℝ,\nTsirelson's bound for a CHSH tuple (A₀, A₁, B₀, B₁) is\n`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2^(3/2) • 1`.\n\nWe prove this by providing an explicit sum-of-squares decomposition\nof the difference.\n\n(We could work over `ℤ[2^(1/2), 2^(-1/2)]` if we really wanted to!)\n-/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `tsirelson_inequality [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `OrderedRing [`R]) "]")
        (Term.instBinder "[" [] (Term.app `StarOrderedRing [`R]) "]")
        (Term.instBinder "[" [] (Term.app `Algebra [(Data.Real.Basic.termℝ "ℝ") `R]) "]")
        (Term.instBinder "[" [] (Term.app `OrderedSmul [(Data.Real.Basic.termℝ "ℝ") `R]) "]")
        (Term.instBinder "[" [] (Term.app `StarModule [(Data.Real.Basic.termℝ "ℝ") `R]) "]")
        (Term.explicitBinder "(" [`A₀ `A₁ `B₀ `B₁] [":" `R] [] ")")
        (Term.explicitBinder "(" [`T] [":" (Term.app `IsCHSHTuple [`A₀ `A₁ `B₀ `B₁])] [] ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         («term_-_»
          («term_+_»
           («term_+_» («term_*_» `A₀ "*" `B₀) "+" («term_*_» `A₀ "*" `B₁))
           "+"
           («term_*_» `A₁ "*" `B₀))
          "-"
          («term_*_» `A₁ "*" `B₁))
         "≤"
         (Algebra.Group.Defs.«term_•_»
          («term_^_» (Algebra.Star.Chsh.«term√2» "√2") "^" (num "3"))
          " • "
          (num "1")))))
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
              [`M []]
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [(Term.explicitBinder "(" [`m] [":" (termℤ "ℤ")] [] ")")
                  (Term.explicitBinder "(" [`a] [":" (Data.Real.Basic.termℝ "ℝ")] [] ")")
                  (Term.explicitBinder "(" [`x] [":" `R] [] ")")]
                 []
                 ","
                 («term_=_»
                  (Algebra.Group.Defs.«term_•_» `m " • " (Algebra.Group.Defs.«term_•_» `a " • " `x))
                  "="
                  (Algebra.Group.Defs.«term_•_»
                   («term_*_»
                    (Term.typeAscription "(" `m ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                    "*"
                    `a)
                   " • "
                   `x))))]
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`m `a `x]
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
                      [(Tactic.rwRule
                        []
                        (Term.app `zsmul_eq_smul_cast [(Data.Real.Basic.termℝ "ℝ")]))
                       ","
                       (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_smul)]
                      "]")
                     [])]))))))))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `P
              []
              []
              ":="
              («term_-_»
               (Algebra.Group.Defs.«term_•_»
                («term_⁻¹» (Algebra.Star.Chsh.«term√2» "√2") "⁻¹")
                " • "
                («term_+_» `A₁ "+" `A₀))
               "-"
               `B₀))))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `Q
              []
              []
              ":="
              («term_+_»
               (Algebra.Group.Defs.«term_•_»
                («term_⁻¹» (Algebra.Star.Chsh.«term√2» "√2") "⁻¹")
                " • "
                («term_-_» `A₁ "-" `A₀))
               "+"
               `B₁))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`w []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 («term_+_»
                  («term_-_»
                   («term_-_»
                    («term_-_»
                     (Algebra.Group.Defs.«term_•_»
                      («term_^_» (Algebra.Star.Chsh.«term√2» "√2") "^" (num "3"))
                      " • "
                      (num "1"))
                     "-"
                     («term_*_» `A₀ "*" `B₀))
                    "-"
                    («term_*_» `A₀ "*" `B₁))
                   "-"
                   («term_*_» `A₁ "*" `B₀))
                  "+"
                  («term_*_» `A₁ "*" `B₁))
                 "="
                 (Algebra.Group.Defs.«term_•_»
                  («term_⁻¹» (Algebra.Star.Chsh.«term√2» "√2") "⁻¹")
                  " • "
                  («term_+_» («term_^_» `P "^" (num "2")) "+" («term_^_» `Q "^" (num "2"))))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.dsimp
                   "dsimp"
                   []
                   []
                   []
                   ["[" [(Tactic.simpLemma [] [] `P) "," (Tactic.simpLemma [] [] `Q)] "]"]
                   [])
                  []
                  (Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [] `sq)
                     ","
                     (Tactic.simpLemma [] [] `sub_mul)
                     ","
                     (Tactic.simpLemma [] [] `mul_sub)
                     ","
                     (Tactic.simpLemma [] [] `add_mul)
                     ","
                     (Tactic.simpLemma [] [] `mul_add)
                     ","
                     (Tactic.simpLemma [] [] `smul_add)
                     ","
                     (Tactic.simpLemma [] [] `smul_sub)]
                    "]"]
                   [])
                  []
                  (Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [] `Algebra.mul_smul_comm)
                     ","
                     (Tactic.simpLemma [] [] `Algebra.smul_mul_assoc)
                     ","
                     (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `mul_smul)
                     ","
                     (Tactic.simpLemma [] [] `sqrt_two_inv_mul_self)]
                    "]"]
                   [])
                  []
                  (Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `sq)
                     ","
                     (Tactic.simpLemma [] [] `T.A₀_inv)
                     ","
                     (Tactic.simpLemma [] [] `T.A₁_inv)
                     ","
                     (Tactic.simpLemma [] [] `T.B₀_inv)
                     ","
                     (Tactic.simpLemma [] [] `T.B₁_inv)]
                    "]"]
                   [])
                  []
                  (Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `T.A₀B₀_commutes)
                     ","
                     (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `T.A₀B₁_commutes)
                     ","
                     (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `T.A₁B₀_commutes)
                     ","
                     (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `T.A₁B₁_commutes)]
                    "]"]
                   [])
                  []
                  (Tactic.abel "abel" [] [])
                  []
                  (Tactic.simp "simp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `M)] "]"] [])
                  []
                  (Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [] `neg_mul)
                     ","
                     (Tactic.simpLemma [] [] `Int.cast_bit0)
                     ","
                     (Tactic.simpLemma [] [] `one_mul)
                     ","
                     (Tactic.simpLemma [] [] `mul_inv_cancel_of_invertible)
                     ","
                     (Tactic.simpLemma [] [] `Int.cast_one)
                     ","
                     (Tactic.simpLemma [] [] `one_smul)
                     ","
                     (Tactic.simpLemma [] [] `Int.cast_neg)
                     ","
                     (Tactic.simpLemma [] [] `add_right_inj)
                     ","
                     (Tactic.simpLemma [] [] `neg_smul)
                     ","
                     (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `add_smul)]
                    "]"]
                   [])
                  []
                  (Tactic.congr "congr" [])
                  []
                  (Tactic.exact
                   "exact"
                   (Term.app
                    `mul_left_cancel₀
                    [(Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
                     `tsirelson_inequality_aux]))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`pos []]
              [(Term.typeSpec
                ":"
                («term_≤_»
                 (num "0")
                 "≤"
                 (Algebra.Group.Defs.«term_•_»
                  («term_⁻¹» (Algebra.Star.Chsh.«term√2» "√2") "⁻¹")
                  " • "
                  («term_+_» («term_^_» `P "^" (num "2")) "+" («term_^_» `Q "^" (num "2"))))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`P_sa []]
                     [(Term.typeSpec ":" («term_=_» (Term.app `star [`P]) "=" `P))]
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `P)] "]"] [])
                         []
                         (Tactic.simp
                          "simp"
                          []
                          []
                          ["only"]
                          ["["
                           [(Tactic.simpLemma [] [] `star_smul)
                            ","
                            (Tactic.simpLemma [] [] `star_add)
                            ","
                            (Tactic.simpLemma [] [] `star_sub)
                            ","
                            (Tactic.simpLemma [] [] `star_id_of_comm)
                            ","
                            (Tactic.simpLemma [] [] `T.A₀_sa)
                            ","
                            (Tactic.simpLemma [] [] `T.A₁_sa)
                            ","
                            (Tactic.simpLemma [] [] `T.B₀_sa)
                            ","
                            (Tactic.simpLemma [] [] `T.B₁_sa)]
                           "]"]
                          [])]))))))
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`Q_sa []]
                     [(Term.typeSpec ":" («term_=_» (Term.app `star [`Q]) "=" `Q))]
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Q)] "]"] [])
                         []
                         (Tactic.simp
                          "simp"
                          []
                          []
                          ["only"]
                          ["["
                           [(Tactic.simpLemma [] [] `star_smul)
                            ","
                            (Tactic.simpLemma [] [] `star_add)
                            ","
                            (Tactic.simpLemma [] [] `star_sub)
                            ","
                            (Tactic.simpLemma [] [] `star_id_of_comm)
                            ","
                            (Tactic.simpLemma [] [] `T.A₀_sa)
                            ","
                            (Tactic.simpLemma [] [] `T.A₁_sa)
                            ","
                            (Tactic.simpLemma [] [] `T.B₀_sa)
                            ","
                            (Tactic.simpLemma [] [] `T.B₁_sa)]
                           "]"]
                          [])]))))))
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`P2_nonneg []]
                     [(Term.typeSpec ":" («term_≤_» (num "0") "≤" («term_^_» `P "^" (num "2"))))]
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.rwSeq
                          "rw"
                          []
                          (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sq)] "]")
                          [])
                         []
                         (Tactic.Conv.conv
                          "conv"
                          []
                          []
                          "=>"
                          (Tactic.Conv.convSeq
                           (Tactic.Conv.convSeq1Indented
                            [(Tactic.Conv.congr "congr")
                             []
                             (Tactic.Conv.skip "skip")
                             []
                             (Tactic.Conv.congr "congr")
                             []
                             (Tactic.Conv.convRw__
                              "rw"
                              []
                              (Tactic.rwRuleSeq
                               "["
                               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `P_sa)]
                               "]"))])))
                         []
                         (convert
                          "convert"
                          []
                          (Term.typeAscription
                           "("
                           `star_mul_self_nonneg
                           ":"
                           [(«term_≤_» (num "0") "≤" («term_*_» (Term.app `star [`P]) "*" `P))]
                           ")")
                          [])]))))))
                  []
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`Q2_nonneg []]
                     [(Term.typeSpec ":" («term_≤_» (num "0") "≤" («term_^_» `Q "^" (num "2"))))]
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.rwSeq
                          "rw"
                          []
                          (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sq)] "]")
                          [])
                         []
                         (Tactic.Conv.conv
                          "conv"
                          []
                          []
                          "=>"
                          (Tactic.Conv.convSeq
                           (Tactic.Conv.convSeq1Indented
                            [(Tactic.Conv.congr "congr")
                             []
                             (Tactic.Conv.skip "skip")
                             []
                             (Tactic.Conv.congr "congr")
                             []
                             (Tactic.Conv.convRw__
                              "rw"
                              []
                              (Tactic.rwRuleSeq
                               "["
                               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Q_sa)]
                               "]"))])))
                         []
                         (convert
                          "convert"
                          []
                          (Term.typeAscription
                           "("
                           `star_mul_self_nonneg
                           ":"
                           [(«term_≤_» (num "0") "≤" («term_*_» (Term.app `star [`Q]) "*" `Q))]
                           ")")
                          [])]))))))
                  []
                  (convert
                   "convert"
                   []
                   (Term.app
                    `smul_le_smul_of_nonneg
                    [(Term.app `add_nonneg [`P2_nonneg `Q2_nonneg])
                     (Term.app
                      `le_of_lt
                      [(Term.show
                        "show"
                        («term_<_» (num "0") "<" («term_⁻¹» (Algebra.Star.Chsh.«term√2» "√2") "⁻¹"))
                        (Term.byTactic'
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(Mathlib.Tactic.normNum "norm_num" [] [] [])]))))])])
                   [])
                  []
                  (Tactic.simp "simp" [] [] [] [] [])]))))))
           []
           (Tactic.apply "apply" `le_of_sub_nonneg)
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
               [(Tactic.simpLemma [] [] `sub_add_eq_sub_sub)
                ","
                (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `sub_add)
                ","
                (Tactic.simpLemma [] [] `w)]
               "]")]
             ["using" `Pos]))])))
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
             [`M []]
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                [(Term.explicitBinder "(" [`m] [":" (termℤ "ℤ")] [] ")")
                 (Term.explicitBinder "(" [`a] [":" (Data.Real.Basic.termℝ "ℝ")] [] ")")
                 (Term.explicitBinder "(" [`x] [":" `R] [] ")")]
                []
                ","
                («term_=_»
                 (Algebra.Group.Defs.«term_•_» `m " • " (Algebra.Group.Defs.«term_•_» `a " • " `x))
                 "="
                 (Algebra.Group.Defs.«term_•_»
                  («term_*_»
                   (Term.typeAscription "(" `m ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                   "*"
                   `a)
                  " • "
                  `x))))]
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`m `a `x]
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
                     [(Tactic.rwRule
                       []
                       (Term.app `zsmul_eq_smul_cast [(Data.Real.Basic.termℝ "ℝ")]))
                      ","
                      (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_smul)]
                     "]")
                    [])]))))))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `P
             []
             []
             ":="
             («term_-_»
              (Algebra.Group.Defs.«term_•_»
               («term_⁻¹» (Algebra.Star.Chsh.«term√2» "√2") "⁻¹")
               " • "
               («term_+_» `A₁ "+" `A₀))
              "-"
              `B₀))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `Q
             []
             []
             ":="
             («term_+_»
              (Algebra.Group.Defs.«term_•_»
               («term_⁻¹» (Algebra.Star.Chsh.«term√2» "√2") "⁻¹")
               " • "
               («term_-_» `A₁ "-" `A₀))
              "+"
              `B₁))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`w []]
             [(Term.typeSpec
               ":"
               («term_=_»
                («term_+_»
                 («term_-_»
                  («term_-_»
                   («term_-_»
                    (Algebra.Group.Defs.«term_•_»
                     («term_^_» (Algebra.Star.Chsh.«term√2» "√2") "^" (num "3"))
                     " • "
                     (num "1"))
                    "-"
                    («term_*_» `A₀ "*" `B₀))
                   "-"
                   («term_*_» `A₀ "*" `B₁))
                  "-"
                  («term_*_» `A₁ "*" `B₀))
                 "+"
                 («term_*_» `A₁ "*" `B₁))
                "="
                (Algebra.Group.Defs.«term_•_»
                 («term_⁻¹» (Algebra.Star.Chsh.«term√2» "√2") "⁻¹")
                 " • "
                 («term_+_» («term_^_» `P "^" (num "2")) "+" («term_^_» `Q "^" (num "2"))))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.dsimp
                  "dsimp"
                  []
                  []
                  []
                  ["[" [(Tactic.simpLemma [] [] `P) "," (Tactic.simpLemma [] [] `Q)] "]"]
                  [])
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `sq)
                    ","
                    (Tactic.simpLemma [] [] `sub_mul)
                    ","
                    (Tactic.simpLemma [] [] `mul_sub)
                    ","
                    (Tactic.simpLemma [] [] `add_mul)
                    ","
                    (Tactic.simpLemma [] [] `mul_add)
                    ","
                    (Tactic.simpLemma [] [] `smul_add)
                    ","
                    (Tactic.simpLemma [] [] `smul_sub)]
                   "]"]
                  [])
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `Algebra.mul_smul_comm)
                    ","
                    (Tactic.simpLemma [] [] `Algebra.smul_mul_assoc)
                    ","
                    (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `mul_smul)
                    ","
                    (Tactic.simpLemma [] [] `sqrt_two_inv_mul_self)]
                   "]"]
                  [])
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `sq)
                    ","
                    (Tactic.simpLemma [] [] `T.A₀_inv)
                    ","
                    (Tactic.simpLemma [] [] `T.A₁_inv)
                    ","
                    (Tactic.simpLemma [] [] `T.B₀_inv)
                    ","
                    (Tactic.simpLemma [] [] `T.B₁_inv)]
                   "]"]
                  [])
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `T.A₀B₀_commutes)
                    ","
                    (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `T.A₀B₁_commutes)
                    ","
                    (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `T.A₁B₀_commutes)
                    ","
                    (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `T.A₁B₁_commutes)]
                   "]"]
                  [])
                 []
                 (Tactic.abel "abel" [] [])
                 []
                 (Tactic.simp "simp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `M)] "]"] [])
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `neg_mul)
                    ","
                    (Tactic.simpLemma [] [] `Int.cast_bit0)
                    ","
                    (Tactic.simpLemma [] [] `one_mul)
                    ","
                    (Tactic.simpLemma [] [] `mul_inv_cancel_of_invertible)
                    ","
                    (Tactic.simpLemma [] [] `Int.cast_one)
                    ","
                    (Tactic.simpLemma [] [] `one_smul)
                    ","
                    (Tactic.simpLemma [] [] `Int.cast_neg)
                    ","
                    (Tactic.simpLemma [] [] `add_right_inj)
                    ","
                    (Tactic.simpLemma [] [] `neg_smul)
                    ","
                    (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `add_smul)]
                   "]"]
                  [])
                 []
                 (Tactic.congr "congr" [])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.app
                   `mul_left_cancel₀
                   [(Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
                    `tsirelson_inequality_aux]))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`pos []]
             [(Term.typeSpec
               ":"
               («term_≤_»
                (num "0")
                "≤"
                (Algebra.Group.Defs.«term_•_»
                 («term_⁻¹» (Algebra.Star.Chsh.«term√2» "√2") "⁻¹")
                 " • "
                 («term_+_» («term_^_» `P "^" (num "2")) "+" («term_^_» `Q "^" (num "2"))))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`P_sa []]
                    [(Term.typeSpec ":" («term_=_» (Term.app `star [`P]) "=" `P))]
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `P)] "]"] [])
                        []
                        (Tactic.simp
                         "simp"
                         []
                         []
                         ["only"]
                         ["["
                          [(Tactic.simpLemma [] [] `star_smul)
                           ","
                           (Tactic.simpLemma [] [] `star_add)
                           ","
                           (Tactic.simpLemma [] [] `star_sub)
                           ","
                           (Tactic.simpLemma [] [] `star_id_of_comm)
                           ","
                           (Tactic.simpLemma [] [] `T.A₀_sa)
                           ","
                           (Tactic.simpLemma [] [] `T.A₁_sa)
                           ","
                           (Tactic.simpLemma [] [] `T.B₀_sa)
                           ","
                           (Tactic.simpLemma [] [] `T.B₁_sa)]
                          "]"]
                         [])]))))))
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`Q_sa []]
                    [(Term.typeSpec ":" («term_=_» (Term.app `star [`Q]) "=" `Q))]
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Q)] "]"] [])
                        []
                        (Tactic.simp
                         "simp"
                         []
                         []
                         ["only"]
                         ["["
                          [(Tactic.simpLemma [] [] `star_smul)
                           ","
                           (Tactic.simpLemma [] [] `star_add)
                           ","
                           (Tactic.simpLemma [] [] `star_sub)
                           ","
                           (Tactic.simpLemma [] [] `star_id_of_comm)
                           ","
                           (Tactic.simpLemma [] [] `T.A₀_sa)
                           ","
                           (Tactic.simpLemma [] [] `T.A₁_sa)
                           ","
                           (Tactic.simpLemma [] [] `T.B₀_sa)
                           ","
                           (Tactic.simpLemma [] [] `T.B₁_sa)]
                          "]"]
                         [])]))))))
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`P2_nonneg []]
                    [(Term.typeSpec ":" («term_≤_» (num "0") "≤" («term_^_» `P "^" (num "2"))))]
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.rwSeq
                         "rw"
                         []
                         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sq)] "]")
                         [])
                        []
                        (Tactic.Conv.conv
                         "conv"
                         []
                         []
                         "=>"
                         (Tactic.Conv.convSeq
                          (Tactic.Conv.convSeq1Indented
                           [(Tactic.Conv.congr "congr")
                            []
                            (Tactic.Conv.skip "skip")
                            []
                            (Tactic.Conv.congr "congr")
                            []
                            (Tactic.Conv.convRw__
                             "rw"
                             []
                             (Tactic.rwRuleSeq
                              "["
                              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `P_sa)]
                              "]"))])))
                        []
                        (convert
                         "convert"
                         []
                         (Term.typeAscription
                          "("
                          `star_mul_self_nonneg
                          ":"
                          [(«term_≤_» (num "0") "≤" («term_*_» (Term.app `star [`P]) "*" `P))]
                          ")")
                         [])]))))))
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`Q2_nonneg []]
                    [(Term.typeSpec ":" («term_≤_» (num "0") "≤" («term_^_» `Q "^" (num "2"))))]
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.rwSeq
                         "rw"
                         []
                         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sq)] "]")
                         [])
                        []
                        (Tactic.Conv.conv
                         "conv"
                         []
                         []
                         "=>"
                         (Tactic.Conv.convSeq
                          (Tactic.Conv.convSeq1Indented
                           [(Tactic.Conv.congr "congr")
                            []
                            (Tactic.Conv.skip "skip")
                            []
                            (Tactic.Conv.congr "congr")
                            []
                            (Tactic.Conv.convRw__
                             "rw"
                             []
                             (Tactic.rwRuleSeq
                              "["
                              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Q_sa)]
                              "]"))])))
                        []
                        (convert
                         "convert"
                         []
                         (Term.typeAscription
                          "("
                          `star_mul_self_nonneg
                          ":"
                          [(«term_≤_» (num "0") "≤" («term_*_» (Term.app `star [`Q]) "*" `Q))]
                          ")")
                         [])]))))))
                 []
                 (convert
                  "convert"
                  []
                  (Term.app
                   `smul_le_smul_of_nonneg
                   [(Term.app `add_nonneg [`P2_nonneg `Q2_nonneg])
                    (Term.app
                     `le_of_lt
                     [(Term.show
                       "show"
                       («term_<_» (num "0") "<" («term_⁻¹» (Algebra.Star.Chsh.«term√2» "√2") "⁻¹"))
                       (Term.byTactic'
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Mathlib.Tactic.normNum "norm_num" [] [] [])]))))])])
                  [])
                 []
                 (Tactic.simp "simp" [] [] [] [] [])]))))))
          []
          (Tactic.apply "apply" `le_of_sub_nonneg)
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
              [(Tactic.simpLemma [] [] `sub_add_eq_sub_sub)
               ","
               (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `sub_add)
               ","
               (Tactic.simpLemma [] [] `w)]
              "]")]
            ["using" `Pos]))])))
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
          [(Tactic.simpLemma [] [] `sub_add_eq_sub_sub)
           ","
           (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `sub_add)
           ","
           (Tactic.simpLemma [] [] `w)]
          "]")]
        ["using" `Pos]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Pos
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `w
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_add_eq_sub_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `le_of_sub_nonneg)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `le_of_sub_nonneg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`pos []]
         [(Term.typeSpec
           ":"
           («term_≤_»
            (num "0")
            "≤"
            (Algebra.Group.Defs.«term_•_»
             («term_⁻¹» (Algebra.Star.Chsh.«term√2» "√2") "⁻¹")
             " • "
             («term_+_» («term_^_» `P "^" (num "2")) "+" («term_^_» `Q "^" (num "2"))))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`P_sa []]
                [(Term.typeSpec ":" («term_=_» (Term.app `star [`P]) "=" `P))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `P)] "]"] [])
                    []
                    (Tactic.simp
                     "simp"
                     []
                     []
                     ["only"]
                     ["["
                      [(Tactic.simpLemma [] [] `star_smul)
                       ","
                       (Tactic.simpLemma [] [] `star_add)
                       ","
                       (Tactic.simpLemma [] [] `star_sub)
                       ","
                       (Tactic.simpLemma [] [] `star_id_of_comm)
                       ","
                       (Tactic.simpLemma [] [] `T.A₀_sa)
                       ","
                       (Tactic.simpLemma [] [] `T.A₁_sa)
                       ","
                       (Tactic.simpLemma [] [] `T.B₀_sa)
                       ","
                       (Tactic.simpLemma [] [] `T.B₁_sa)]
                      "]"]
                     [])]))))))
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`Q_sa []]
                [(Term.typeSpec ":" («term_=_» (Term.app `star [`Q]) "=" `Q))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Q)] "]"] [])
                    []
                    (Tactic.simp
                     "simp"
                     []
                     []
                     ["only"]
                     ["["
                      [(Tactic.simpLemma [] [] `star_smul)
                       ","
                       (Tactic.simpLemma [] [] `star_add)
                       ","
                       (Tactic.simpLemma [] [] `star_sub)
                       ","
                       (Tactic.simpLemma [] [] `star_id_of_comm)
                       ","
                       (Tactic.simpLemma [] [] `T.A₀_sa)
                       ","
                       (Tactic.simpLemma [] [] `T.A₁_sa)
                       ","
                       (Tactic.simpLemma [] [] `T.B₀_sa)
                       ","
                       (Tactic.simpLemma [] [] `T.B₁_sa)]
                      "]"]
                     [])]))))))
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`P2_nonneg []]
                [(Term.typeSpec ":" («term_≤_» (num "0") "≤" («term_^_» `P "^" (num "2"))))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sq)] "]") [])
                    []
                    (Tactic.Conv.conv
                     "conv"
                     []
                     []
                     "=>"
                     (Tactic.Conv.convSeq
                      (Tactic.Conv.convSeq1Indented
                       [(Tactic.Conv.congr "congr")
                        []
                        (Tactic.Conv.skip "skip")
                        []
                        (Tactic.Conv.congr "congr")
                        []
                        (Tactic.Conv.convRw__
                         "rw"
                         []
                         (Tactic.rwRuleSeq
                          "["
                          [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `P_sa)]
                          "]"))])))
                    []
                    (convert
                     "convert"
                     []
                     (Term.typeAscription
                      "("
                      `star_mul_self_nonneg
                      ":"
                      [(«term_≤_» (num "0") "≤" («term_*_» (Term.app `star [`P]) "*" `P))]
                      ")")
                     [])]))))))
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`Q2_nonneg []]
                [(Term.typeSpec ":" («term_≤_» (num "0") "≤" («term_^_» `Q "^" (num "2"))))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sq)] "]") [])
                    []
                    (Tactic.Conv.conv
                     "conv"
                     []
                     []
                     "=>"
                     (Tactic.Conv.convSeq
                      (Tactic.Conv.convSeq1Indented
                       [(Tactic.Conv.congr "congr")
                        []
                        (Tactic.Conv.skip "skip")
                        []
                        (Tactic.Conv.congr "congr")
                        []
                        (Tactic.Conv.convRw__
                         "rw"
                         []
                         (Tactic.rwRuleSeq
                          "["
                          [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Q_sa)]
                          "]"))])))
                    []
                    (convert
                     "convert"
                     []
                     (Term.typeAscription
                      "("
                      `star_mul_self_nonneg
                      ":"
                      [(«term_≤_» (num "0") "≤" («term_*_» (Term.app `star [`Q]) "*" `Q))]
                      ")")
                     [])]))))))
             []
             (convert
              "convert"
              []
              (Term.app
               `smul_le_smul_of_nonneg
               [(Term.app `add_nonneg [`P2_nonneg `Q2_nonneg])
                (Term.app
                 `le_of_lt
                 [(Term.show
                   "show"
                   («term_<_» (num "0") "<" («term_⁻¹» (Algebra.Star.Chsh.«term√2» "√2") "⁻¹"))
                   (Term.byTactic'
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Mathlib.Tactic.normNum "norm_num" [] [] [])]))))])])
              [])
             []
             (Tactic.simp "simp" [] [] [] [] [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`P_sa []]
             [(Term.typeSpec ":" («term_=_» (Term.app `star [`P]) "=" `P))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `P)] "]"] [])
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `star_smul)
                    ","
                    (Tactic.simpLemma [] [] `star_add)
                    ","
                    (Tactic.simpLemma [] [] `star_sub)
                    ","
                    (Tactic.simpLemma [] [] `star_id_of_comm)
                    ","
                    (Tactic.simpLemma [] [] `T.A₀_sa)
                    ","
                    (Tactic.simpLemma [] [] `T.A₁_sa)
                    ","
                    (Tactic.simpLemma [] [] `T.B₀_sa)
                    ","
                    (Tactic.simpLemma [] [] `T.B₁_sa)]
                   "]"]
                  [])]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`Q_sa []]
             [(Term.typeSpec ":" («term_=_» (Term.app `star [`Q]) "=" `Q))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.dsimp "dsimp" [] [] [] ["[" [(Tactic.simpLemma [] [] `Q)] "]"] [])
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `star_smul)
                    ","
                    (Tactic.simpLemma [] [] `star_add)
                    ","
                    (Tactic.simpLemma [] [] `star_sub)
                    ","
                    (Tactic.simpLemma [] [] `star_id_of_comm)
                    ","
                    (Tactic.simpLemma [] [] `T.A₀_sa)
                    ","
                    (Tactic.simpLemma [] [] `T.A₁_sa)
                    ","
                    (Tactic.simpLemma [] [] `T.B₀_sa)
                    ","
                    (Tactic.simpLemma [] [] `T.B₁_sa)]
                   "]"]
                  [])]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`P2_nonneg []]
             [(Term.typeSpec ":" («term_≤_» (num "0") "≤" («term_^_» `P "^" (num "2"))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sq)] "]") [])
                 []
                 (Tactic.Conv.conv
                  "conv"
                  []
                  []
                  "=>"
                  (Tactic.Conv.convSeq
                   (Tactic.Conv.convSeq1Indented
                    [(Tactic.Conv.congr "congr")
                     []
                     (Tactic.Conv.skip "skip")
                     []
                     (Tactic.Conv.congr "congr")
                     []
                     (Tactic.Conv.convRw__
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `P_sa)]
                       "]"))])))
                 []
                 (convert
                  "convert"
                  []
                  (Term.typeAscription
                   "("
                   `star_mul_self_nonneg
                   ":"
                   [(«term_≤_» (num "0") "≤" («term_*_» (Term.app `star [`P]) "*" `P))]
                   ")")
                  [])]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`Q2_nonneg []]
             [(Term.typeSpec ":" («term_≤_» (num "0") "≤" («term_^_» `Q "^" (num "2"))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sq)] "]") [])
                 []
                 (Tactic.Conv.conv
                  "conv"
                  []
                  []
                  "=>"
                  (Tactic.Conv.convSeq
                   (Tactic.Conv.convSeq1Indented
                    [(Tactic.Conv.congr "congr")
                     []
                     (Tactic.Conv.skip "skip")
                     []
                     (Tactic.Conv.congr "congr")
                     []
                     (Tactic.Conv.convRw__
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Q_sa)]
                       "]"))])))
                 []
                 (convert
                  "convert"
                  []
                  (Term.typeAscription
                   "("
                   `star_mul_self_nonneg
                   ":"
                   [(«term_≤_» (num "0") "≤" («term_*_» (Term.app `star [`Q]) "*" `Q))]
                   ")")
                  [])]))))))
          []
          (convert
           "convert"
           []
           (Term.app
            `smul_le_smul_of_nonneg
            [(Term.app `add_nonneg [`P2_nonneg `Q2_nonneg])
             (Term.app
              `le_of_lt
              [(Term.show
                "show"
                («term_<_» (num "0") "<" («term_⁻¹» (Algebra.Star.Chsh.«term√2» "√2") "⁻¹"))
                (Term.byTactic'
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])]))))])])
           [])
          []
          (Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert
       "convert"
       []
       (Term.app
        `smul_le_smul_of_nonneg
        [(Term.app `add_nonneg [`P2_nonneg `Q2_nonneg])
         (Term.app
          `le_of_lt
          [(Term.show
            "show"
            («term_<_» (num "0") "<" («term_⁻¹» (Algebra.Star.Chsh.«term√2» "√2") "⁻¹"))
            (Term.byTactic'
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])]))))])])
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `smul_le_smul_of_nonneg
       [(Term.app `add_nonneg [`P2_nonneg `Q2_nonneg])
        (Term.app
         `le_of_lt
         [(Term.show
           "show"
           («term_<_» (num "0") "<" («term_⁻¹» (Algebra.Star.Chsh.«term√2» "√2") "⁻¹"))
           (Term.byTactic'
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])]))))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le_of_lt
       [(Term.show
         "show"
         («term_<_» (num "0") "<" («term_⁻¹» (Algebra.Star.Chsh.«term√2» "√2") "⁻¹"))
         (Term.byTactic'
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.show
       "show"
       («term_<_» (num "0") "<" («term_⁻¹» (Algebra.Star.Chsh.«term√2» "√2") "⁻¹"))
       (Term.byTactic'
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.normNum "norm_num" [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_<_» (num "0") "<" («term_⁻¹» (Algebra.Star.Chsh.«term√2» "√2") "⁻¹"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⁻¹» (Algebra.Star.Chsh.«term√2» "√2") "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Algebra.Star.Chsh.«term√2» "√2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Star.Chsh.«term√2»', expected 'Algebra.Star.Chsh.term√2._@.Algebra.Star.Chsh._hyg.5'
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
    In a noncommutative ordered `*`-algebra over ℝ,
    Tsirelson's bound for a CHSH tuple (A₀, A₁, B₀, B₁) is
    `A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2^(3/2) • 1`.
    
    We prove this by providing an explicit sum-of-squares decomposition
    of the difference.
    
    (We could work over `ℤ[2^(1/2), 2^(-1/2)]` if we really wanted to!)
    -/
  theorem
    tsirelson_inequality
    [ OrderedRing R ]
        [ StarOrderedRing R ]
        [ Algebra ℝ R ]
        [ OrderedSmul ℝ R ]
        [ StarModule ℝ R ]
        ( A₀ A₁ B₀ B₁ : R )
        ( T : IsCHSHTuple A₀ A₁ B₀ B₁ )
      : A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ √2 ^ 3 • 1
    :=
      by
        have
            M
              : ∀ ( m : ℤ ) ( a : ℝ ) ( x : R ) , m • a • x = ( m : ℝ ) * a • x
              :=
              fun m a x => by rw [ zsmul_eq_smul_cast ℝ , ← mul_smul ]
          let P := √2 ⁻¹ • A₁ + A₀ - B₀
          let Q := √2 ⁻¹ • A₁ - A₀ + B₁
          have
            w
              : √2 ^ 3 • 1 - A₀ * B₀ - A₀ * B₁ - A₁ * B₀ + A₁ * B₁ = √2 ⁻¹ • P ^ 2 + Q ^ 2
              :=
              by
                dsimp [ P , Q ]
                  simp only [ sq , sub_mul , mul_sub , add_mul , mul_add , smul_add , smul_sub ]
                  simp
                    only
                    [
                      Algebra.mul_smul_comm
                        ,
                        Algebra.smul_mul_assoc
                        ,
                        ← mul_smul
                        ,
                        sqrt_two_inv_mul_self
                      ]
                  simp only [ ← sq , T.A₀_inv , T.A₁_inv , T.B₀_inv , T.B₁_inv ]
                  simp
                    only
                    [
                      ← T.A₀B₀_commutes , ← T.A₀B₁_commutes , ← T.A₁B₀_commutes , ← T.A₁B₁_commutes
                      ]
                  abel
                  simp only [ M ]
                  simp
                    only
                    [
                      neg_mul
                        ,
                        Int.cast_bit0
                        ,
                        one_mul
                        ,
                        mul_inv_cancel_of_invertible
                        ,
                        Int.cast_one
                        ,
                        one_smul
                        ,
                        Int.cast_neg
                        ,
                        add_right_inj
                        ,
                        neg_smul
                        ,
                        ← add_smul
                      ]
                  congr
                  exact mul_left_cancel₀ by norm_num tsirelson_inequality_aux
          have
            pos
              : 0 ≤ √2 ⁻¹ • P ^ 2 + Q ^ 2
              :=
              by
                have
                    P_sa
                      : star P = P
                      :=
                      by
                        dsimp [ P ]
                          simp
                            only
                            [
                              star_smul
                                ,
                                star_add
                                ,
                                star_sub
                                ,
                                star_id_of_comm
                                ,
                                T.A₀_sa
                                ,
                                T.A₁_sa
                                ,
                                T.B₀_sa
                                ,
                                T.B₁_sa
                              ]
                  have
                    Q_sa
                      : star Q = Q
                      :=
                      by
                        dsimp [ Q ]
                          simp
                            only
                            [
                              star_smul
                                ,
                                star_add
                                ,
                                star_sub
                                ,
                                star_id_of_comm
                                ,
                                T.A₀_sa
                                ,
                                T.A₁_sa
                                ,
                                T.B₀_sa
                                ,
                                T.B₁_sa
                              ]
                  have
                    P2_nonneg
                      : 0 ≤ P ^ 2
                      :=
                      by
                        rw [ sq ]
                          conv => congr skip congr rw [ ← P_sa ]
                          convert ( star_mul_self_nonneg : 0 ≤ star P * P )
                  have
                    Q2_nonneg
                      : 0 ≤ Q ^ 2
                      :=
                      by
                        rw [ sq ]
                          conv => congr skip congr rw [ ← Q_sa ]
                          convert ( star_mul_self_nonneg : 0 ≤ star Q * Q )
                  convert
                    smul_le_smul_of_nonneg
                      add_nonneg P2_nonneg Q2_nonneg le_of_lt show 0 < √2 ⁻¹ by norm_num
                  simp
          apply le_of_sub_nonneg
          simpa only [ sub_add_eq_sub_sub , ← sub_add , w ] using Pos
#align tsirelson_inequality tsirelson_inequality

