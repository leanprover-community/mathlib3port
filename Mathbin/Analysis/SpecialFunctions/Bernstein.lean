/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module analysis.special_functions.bernstein
! leanprover-community/mathlib commit 5a3e819569b0f12cbec59d740a2613018e7b8eec
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Field.Basic
import Mathbin.RingTheory.Polynomial.Bernstein
import Mathbin.Topology.ContinuousFunction.Polynomial
import Mathbin.Topology.ContinuousFunction.Compact

/-!
# Bernstein approximations and Weierstrass' theorem

We prove that the Bernstein approximations
```
∑ k : fin (n+1), f (k/n : ℝ) * n.choose k * x^k * (1-x)^(n-k)
```
for a continuous function `f : C([0,1], ℝ)` converge uniformly to `f` as `n` tends to infinity.

Our proof follows [Richard Beals' *Analysis, an introduction*][beals-analysis], §7D.
The original proof, due to [Bernstein](bernstein1912) in 1912, is probabilistic,
and relies on Bernoulli's theorem,
which gives bounds for how quickly the observed frequencies in a
Bernoulli trial approach the underlying probability.

The proof here does not directly rely on Bernoulli's theorem,
but can also be given a probabilistic account.
* Consider a weighted coin which with probability `x` produces heads,
  and with probability `1-x` produces tails.
* The value of `bernstein n k x` is the probability that
  such a coin gives exactly `k` heads in a sequence of `n` tosses.
* If such an appearance of `k` heads results in a payoff of `f(k / n)`,
  the `n`-th Bernstein approximation for `f` evaluated at `x` is the expected payoff.
* The main estimate in the proof bounds the probability that
  the observed frequency of heads differs from `x` by more than some `δ`,
  obtaining a bound of `(4 * n * δ^2)⁻¹`, irrespective of `x`.
* This ensures that for `n` large, the Bernstein approximation is (uniformly) close to the
  payoff function `f`.

(You don't need to think in these terms to follow the proof below: it's a giant `calc` block!)

This result proves Weierstrass' theorem that polynomials are dense in `C([0,1], ℝ)`,
although we defer an abstract statement of this until later.
-/


noncomputable section

open Classical

open BigOperators

open BoundedContinuousFunction

open unitInterval

/-- The Bernstein polynomials, as continuous functions on `[0,1]`.
-/
def bernstein (n ν : ℕ) : C(I, ℝ) :=
  (bernsteinPolynomial ℝ n ν).toContinuousMapOn I
#align bernstein bernstein

@[simp]
theorem bernstein_apply (n ν : ℕ) (x : I) :
    bernstein n ν x = n.choose ν * x ^ ν * (1 - x) ^ (n - ν) :=
  by
  dsimp [bernstein, Polynomial.toContinuousMapOn, Polynomial.toContinuousMap, bernsteinPolynomial]
  simp
#align bernstein_apply bernstein_apply

theorem bernstein_nonneg {n ν : ℕ} {x : I} : 0 ≤ bernstein n ν x :=
  by
  simp only [bernstein_apply]
  exact
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by unit_interval) _))
      (pow_nonneg (by unit_interval) _)
#align bernstein_nonneg bernstein_nonneg

/-!
We now give a slight reformulation of `bernstein_polynomial.variance`.
-/


namespace bernstein

/-- Send `k : fin (n+1)` to the equally spaced points `k/n` in the unit interval.
-/
def z {n : ℕ} (k : Fin (n + 1)) : I :=
  ⟨(k : ℝ) / n, by
    cases n
    · norm_num
    · have h₁ : 0 < (n.succ : ℝ) := by exact_mod_cast Nat.succ_pos _
      have h₂ : ↑k ≤ n.succ := by exact_mod_cast Fin.le_last k
      rw [Set.mem_Icc, le_div_iff h₁, div_le_iff h₁]
      norm_cast
      simp [h₂]⟩
#align bernstein.z bernstein.z

-- mathport name: «expr /ₙ»
local postfix:90 "/ₙ" => z

theorem probability (n : ℕ) (x : I) : (∑ k : Fin (n + 1), bernstein n k x) = 1 :=
  by
  have := bernsteinPolynomial.sum ℝ n
  apply_fun fun p => Polynomial.aeval (x : ℝ) p  at this
  simp [AlgHom.map_sum, Finset.sum_range] at this
  exact this
#align bernstein.probability bernstein.probability

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `variance [])
      (Command.declSig
       [(Term.implicitBinder "{" [`n] [":" (termℕ "ℕ")] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          («term_<_»
           (num "0")
           "<"
           (Term.typeAscription "(" `n ":" [(Data.Real.Basic.termℝ "ℝ")] ")"))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`x]
         [":" (unitInterval.Topology.UnitInterval.unit_interval "I")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
          "∑"
          (Std.ExtendedBinder.extBinders
           (Std.ExtendedBinder.extBinder
            (Lean.binderIdent `k)
            [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]))
          ", "
          («term_*_»
           («term_^_»
            (Term.typeAscription
             "("
             («term_-_» `x "-" (bernstein.Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
             ":"
             [(Data.Real.Basic.termℝ "ℝ")]
             ")")
            "^"
            (num "2"))
           "*"
           (Term.app `bernstein [`n `k `x])))
         "="
         («term_/_» («term_*_» `x "*" («term_-_» (num "1") "-" `x)) "/" `n))))
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
              [`h' []]
              [(Term.typeSpec
                ":"
                («term_≠_»
                 (Term.typeAscription "(" `n ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                 "≠"
                 (num "0")))]
              ":="
              (Term.app `ne_of_gt [`h]))))
           []
           (Mathlib.Tactic.applyFun
            "apply_fun"
            (Term.fun
             "fun"
             (Term.basicFun
              [`x]
              [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))]
              "=>"
              («term_*_» `x "*" `n)))
            []
            ["using" (Term.app `GroupWithZero.mul_right_injective [`h'])])
           []
           (Mathlib.Tactic.applyFun
            "apply_fun"
            (Term.fun
             "fun"
             (Term.basicFun
              [`x]
              [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))]
              "=>"
              («term_*_» `x "*" `n)))
            []
            ["using" (Term.app `GroupWithZero.mul_right_injective [`h'])])
           []
           (Tactic.dsimp "dsimp" [] [] [] [] [])
           []
           (Mathlib.Tactic.Conv.convLHS
            "conv_lhs"
            []
            []
            "=>"
            (Tactic.Conv.convSeq
             (Tactic.Conv.convSeq1Indented
              [(Tactic.Conv.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `Finset.sum_mul) "," (Tactic.simpLemma [] [] `z)]
                 "]"])])))
           []
           (Mathlib.Tactic.Conv.convRHS
            "conv_rhs"
            []
            []
            "=>"
            (Tactic.Conv.convSeq
             (Tactic.Conv.convSeq1Indented
              [(Tactic.Conv.convRw__
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] (Term.app `div_mul_cancel [(Term.hole "_") `h']))]
                 "]"))])))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              []
              ":="
              (Term.app `bernsteinPolynomial.variance [(Data.Real.Basic.termℝ "ℝ") `n]))))
           []
           (Mathlib.Tactic.applyFun
            "apply_fun"
            (Term.fun
             "fun"
             (Term.basicFun
              [`p]
              []
              "=>"
              (Term.app
               `Polynomial.aeval
               [(Term.typeAscription "(" `x ":" [(Data.Real.Basic.termℝ "ℝ")] ")") `p])))
            [(Tactic.location "at" (Tactic.locationHyp [`this] []))]
            [])
           []
           (Tactic.simp
            "simp"
            []
            []
            []
            ["["
             [(Tactic.simpLemma [] [] `AlgHom.map_sum)
              ","
              (Tactic.simpLemma [] [] `Finset.sum_range)
              ","
              (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Polynomial.nat_cast_mul)]
             "]"]
            [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
           []
           (convert "convert" [] `this ["using" (num "1")])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.congr "congr" [(num "1")])
             []
             (tacticFunext__ "funext" [`k])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 []
                 (Term.app
                  `mul_comm
                  [(Term.hole "_")
                   (Term.typeAscription "(" `n ":" [(Data.Real.Basic.termℝ "ℝ")] ")")]))
                ","
                (Tactic.rwRule
                 []
                 (Term.app
                  `mul_comm
                  [(Term.hole "_")
                   (Term.typeAscription "(" `n ":" [(Data.Real.Basic.termℝ "ℝ")] ")")]))
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)]
               "]")
              [])
             []
             (Tactic.congr "congr" [(num "1")])
             []
             (Tactic.fieldSimp
              "field_simp"
              []
              []
              []
              [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `h)] "]")]
              [])
             []
             (Mathlib.Tactic.RingNF.ring "ring")])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Mathlib.Tactic.RingNF.ring "ring")])])))
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
             [`h' []]
             [(Term.typeSpec
               ":"
               («term_≠_»
                (Term.typeAscription "(" `n ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                "≠"
                (num "0")))]
             ":="
             (Term.app `ne_of_gt [`h]))))
          []
          (Mathlib.Tactic.applyFun
           "apply_fun"
           (Term.fun
            "fun"
            (Term.basicFun
             [`x]
             [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))]
             "=>"
             («term_*_» `x "*" `n)))
           []
           ["using" (Term.app `GroupWithZero.mul_right_injective [`h'])])
          []
          (Mathlib.Tactic.applyFun
           "apply_fun"
           (Term.fun
            "fun"
            (Term.basicFun
             [`x]
             [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))]
             "=>"
             («term_*_» `x "*" `n)))
           []
           ["using" (Term.app `GroupWithZero.mul_right_injective [`h'])])
          []
          (Tactic.dsimp "dsimp" [] [] [] [] [])
          []
          (Mathlib.Tactic.Conv.convLHS
           "conv_lhs"
           []
           []
           "=>"
           (Tactic.Conv.convSeq
            (Tactic.Conv.convSeq1Indented
             [(Tactic.Conv.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `Finset.sum_mul) "," (Tactic.simpLemma [] [] `z)]
                "]"])])))
          []
          (Mathlib.Tactic.Conv.convRHS
           "conv_rhs"
           []
           []
           "=>"
           (Tactic.Conv.convSeq
            (Tactic.Conv.convSeq1Indented
             [(Tactic.Conv.convRw__
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] (Term.app `div_mul_cancel [(Term.hole "_") `h']))]
                "]"))])))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             []
             ":="
             (Term.app `bernsteinPolynomial.variance [(Data.Real.Basic.termℝ "ℝ") `n]))))
          []
          (Mathlib.Tactic.applyFun
           "apply_fun"
           (Term.fun
            "fun"
            (Term.basicFun
             [`p]
             []
             "=>"
             (Term.app
              `Polynomial.aeval
              [(Term.typeAscription "(" `x ":" [(Data.Real.Basic.termℝ "ℝ")] ")") `p])))
           [(Tactic.location "at" (Tactic.locationHyp [`this] []))]
           [])
          []
          (Tactic.simp
           "simp"
           []
           []
           []
           ["["
            [(Tactic.simpLemma [] [] `AlgHom.map_sum)
             ","
             (Tactic.simpLemma [] [] `Finset.sum_range)
             ","
             (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Polynomial.nat_cast_mul)]
            "]"]
           [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
          []
          (convert "convert" [] `this ["using" (num "1")])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.congr "congr" [(num "1")])
            []
            (tacticFunext__ "funext" [`k])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                []
                (Term.app
                 `mul_comm
                 [(Term.hole "_")
                  (Term.typeAscription "(" `n ":" [(Data.Real.Basic.termℝ "ℝ")] ")")]))
               ","
               (Tactic.rwRule
                []
                (Term.app
                 `mul_comm
                 [(Term.hole "_")
                  (Term.typeAscription "(" `n ":" [(Data.Real.Basic.termℝ "ℝ")] ")")]))
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)]
              "]")
             [])
            []
            (Tactic.congr "congr" [(num "1")])
            []
            (Tactic.fieldSimp
             "field_simp"
             []
             []
             []
             [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `h)] "]")]
             [])
            []
            (Mathlib.Tactic.RingNF.ring "ring")])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Mathlib.Tactic.RingNF.ring "ring")])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__ (cdotTk (patternIgnore (token.«· » "·"))) [(Mathlib.Tactic.RingNF.ring "ring")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.RingNF.ring "ring")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.congr "congr" [(num "1")])
        []
        (tacticFunext__ "funext" [`k])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            []
            (Term.app
             `mul_comm
             [(Term.hole "_") (Term.typeAscription "(" `n ":" [(Data.Real.Basic.termℝ "ℝ")] ")")]))
           ","
           (Tactic.rwRule
            []
            (Term.app
             `mul_comm
             [(Term.hole "_") (Term.typeAscription "(" `n ":" [(Data.Real.Basic.termℝ "ℝ")] ")")]))
           ","
           (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)
           ","
           (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)]
          "]")
         [])
        []
        (Tactic.congr "congr" [(num "1")])
        []
        (Tactic.fieldSimp
         "field_simp"
         []
         []
         []
         [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `h)] "]")]
         [])
        []
        (Mathlib.Tactic.RingNF.ring "ring")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.RingNF.ring "ring")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.fieldSimp
       "field_simp"
       []
       []
       []
       [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `h)] "]")]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.congr "congr" [(num "1")])
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
           `mul_comm
           [(Term.hole "_") (Term.typeAscription "(" `n ":" [(Data.Real.Basic.termℝ "ℝ")] ")")]))
         ","
         (Tactic.rwRule
          []
          (Term.app
           `mul_comm
           [(Term.hole "_") (Term.typeAscription "(" `n ":" [(Data.Real.Basic.termℝ "ℝ")] ")")]))
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mul_comm
       [(Term.hole "_") (Term.typeAscription "(" `n ":" [(Data.Real.Basic.termℝ "ℝ")] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" `n ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mul_comm
       [(Term.hole "_") (Term.typeAscription "(" `n ":" [(Data.Real.Basic.termℝ "ℝ")] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" `n ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tacticFunext__ "funext" [`k])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.congr "congr" [(num "1")])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert "convert" [] `this ["using" (num "1")])
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
       []
       ["["
        [(Tactic.simpLemma [] [] `AlgHom.map_sum)
         ","
         (Tactic.simpLemma [] [] `Finset.sum_range)
         ","
         (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Polynomial.nat_cast_mul)]
        "]"]
       [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Polynomial.nat_cast_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Finset.sum_range
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `AlgHom.map_sum
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.applyFun
       "apply_fun"
       (Term.fun
        "fun"
        (Term.basicFun
         [`p]
         []
         "=>"
         (Term.app
          `Polynomial.aeval
          [(Term.typeAscription "(" `x ":" [(Data.Real.Basic.termℝ "ℝ")] ")") `p])))
       [(Tactic.location "at" (Tactic.locationHyp [`this] []))]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`p]
        []
        "=>"
        (Term.app
         `Polynomial.aeval
         [(Term.typeAscription "(" `x ":" [(Data.Real.Basic.termℝ "ℝ")] ")") `p])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Polynomial.aeval
       [(Term.typeAscription "(" `x ":" [(Data.Real.Basic.termℝ "ℝ")] ")") `p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription "(" `x ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Polynomial.aeval
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         []
         ":="
         (Term.app `bernsteinPolynomial.variance [(Data.Real.Basic.termℝ "ℝ") `n]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `bernsteinPolynomial.variance [(Data.Real.Basic.termℝ "ℝ") `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `bernsteinPolynomial.variance
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.Conv.convRHS
       "conv_rhs"
       []
       []
       "=>"
       (Tactic.Conv.convSeq
        (Tactic.Conv.convSeq1Indented
         [(Tactic.Conv.convRw__
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] (Term.app `div_mul_cancel [(Term.hole "_") `h']))]
            "]"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convSeq1Indented', expected 'Lean.Parser.Tactic.Conv.convSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `div_mul_cancel [(Term.hole "_") `h'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `div_mul_cancel
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.Conv.convLHS
       "conv_lhs"
       []
       []
       "=>"
       (Tactic.Conv.convSeq
        (Tactic.Conv.convSeq1Indented
         [(Tactic.Conv.simp
           "simp"
           []
           []
           ["only"]
           ["[" [(Tactic.simpLemma [] [] `Finset.sum_mul) "," (Tactic.simpLemma [] [] `z)] "]"])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convSeq1Indented', expected 'Lean.Parser.Tactic.Conv.convSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Finset.sum_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp "dsimp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.applyFun
       "apply_fun"
       (Term.fun
        "fun"
        (Term.basicFun
         [`x]
         [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))]
         "=>"
         («term_*_» `x "*" `n)))
       []
       ["using" (Term.app `GroupWithZero.mul_right_injective [`h'])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `GroupWithZero.mul_right_injective [`h'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `GroupWithZero.mul_right_injective
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))]
        "=>"
        («term_*_» `x "*" `n)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `x "*" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.applyFun
       "apply_fun"
       (Term.fun
        "fun"
        (Term.basicFun
         [`x]
         [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))]
         "=>"
         («term_*_» `x "*" `n)))
       []
       ["using" (Term.app `GroupWithZero.mul_right_injective [`h'])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `GroupWithZero.mul_right_injective [`h'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `GroupWithZero.mul_right_injective
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))]
        "=>"
        («term_*_» `x "*" `n)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `x "*" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`h' []]
         [(Term.typeSpec
           ":"
           («term_≠_»
            (Term.typeAscription "(" `n ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
            "≠"
            (num "0")))]
         ":="
         (Term.app `ne_of_gt [`h]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ne_of_gt [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ne_of_gt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» (Term.typeAscription "(" `n ":" [(Data.Real.Basic.termℝ "ℝ")] ")") "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription "(" `n ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
        "∑"
        (Std.ExtendedBinder.extBinders
         (Std.ExtendedBinder.extBinder
          (Lean.binderIdent `k)
          [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]))
        ", "
        («term_*_»
         («term_^_»
          (Term.typeAscription
           "("
           («term_-_» `x "-" (bernstein.Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
           ":"
           [(Data.Real.Basic.termℝ "ℝ")]
           ")")
          "^"
          (num "2"))
         "*"
         (Term.app `bernstein [`n `k `x])))
       "="
       («term_/_» («term_*_» `x "*" («term_-_» (num "1") "-" `x)) "/" `n))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» («term_*_» `x "*" («term_-_» (num "1") "-" `x)) "/" `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_*_» `x "*" («term_-_» (num "1") "-" `x))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» (num "1") "-" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_-_» (num "1") "-" `x) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
       "∑"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder
         (Lean.binderIdent `k)
         [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]))
       ", "
       («term_*_»
        («term_^_»
         (Term.typeAscription
          "("
          («term_-_» `x "-" (bernstein.Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
          ":"
          [(Data.Real.Basic.termℝ "ℝ")]
          ")")
         "^"
         (num "2"))
        "*"
        (Term.app `bernstein [`n `k `x])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_^_»
        (Term.typeAscription
         "("
         («term_-_» `x "-" (bernstein.Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
         ":"
         [(Data.Real.Basic.termℝ "ℝ")]
         ")")
        "^"
        (num "2"))
       "*"
       (Term.app `bernstein [`n `k `x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `bernstein [`n `k `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `bernstein
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_^_»
       (Term.typeAscription
        "("
        («term_-_» `x "-" (bernstein.Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
        ":"
        [(Data.Real.Basic.termℝ "ℝ")]
        ")")
       "^"
       (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Term.typeAscription
       "("
       («term_-_» `x "-" (bernstein.Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
       ":"
       [(Data.Real.Basic.termℝ "ℝ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» `x "-" (bernstein.Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (bernstein.Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'bernstein.Analysis.SpecialFunctions.Bernstein.«term_/ₙ»', expected 'bernstein.Analysis.SpecialFunctions.Bernstein.term_/ₙ._@.Analysis.SpecialFunctions.Bernstein._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  variance
  { n : ℕ } ( h : 0 < ( n : ℝ ) ) ( x : I )
    : ∑ k : Fin n + 1 , ( x - k /ₙ : ℝ ) ^ 2 * bernstein n k x = x * 1 - x / n
  :=
    by
      have h' : ( n : ℝ ) ≠ 0 := ne_of_gt h
        apply_fun fun x : ℝ => x * n using GroupWithZero.mul_right_injective h'
        apply_fun fun x : ℝ => x * n using GroupWithZero.mul_right_injective h'
        dsimp
        conv_lhs => simp only [ Finset.sum_mul , z ]
        conv_rhs => rw [ div_mul_cancel _ h' ]
        have := bernsteinPolynomial.variance ℝ n
        apply_fun fun p => Polynomial.aeval ( x : ℝ ) p at this
        simp [ AlgHom.map_sum , Finset.sum_range , ← Polynomial.nat_cast_mul ] at this
        convert this using 1
        ·
          congr 1
            funext k
            rw [ mul_comm _ ( n : ℝ ) , mul_comm _ ( n : ℝ ) , ← mul_assoc , ← mul_assoc ]
            congr 1
            field_simp [ h ]
            ring
        · ring
#align bernstein.variance bernstein.variance

end bernstein

open bernstein

-- mathport name: «expr /ₙ»
local postfix:1024 "/ₙ" => z

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The `n`-th approximation of a continuous function on `[0,1]` by Bernstein polynomials,\ngiven by `∑ k, f (k/n) * bernstein n k x`.\n-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `bernsteinApproximation [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")
        (Term.explicitBinder
         "("
         [`f]
         [":"
          (Topology.ContinuousFunction.Basic.«termC(_,_)»
           "C("
           (unitInterval.Topology.UnitInterval.unit_interval "I")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")")]
         []
         ")")]
       [(Term.typeSpec
         ":"
         (Topology.ContinuousFunction.Basic.«termC(_,_)»
          "C("
          (unitInterval.Topology.UnitInterval.unit_interval "I")
          ", "
          (Data.Real.Basic.termℝ "ℝ")
          ")"))])
      (Command.declValSimple
       ":="
       (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
        "∑"
        (Std.ExtendedBinder.extBinders
         (Std.ExtendedBinder.extBinder
          (Lean.binderIdent `k)
          [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]))
        ", "
        (Algebra.Group.Defs.«term_•_»
         (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
         " • "
         (Term.app `bernstein [`n `k])))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
       "∑"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder
         (Lean.binderIdent `k)
         [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]))
       ", "
       (Algebra.Group.Defs.«term_•_»
        (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
        " • "
        (Term.app `bernstein [`n `k])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Defs.«term_•_»
       (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
       " • "
       (Term.app `bernstein [`n `k]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `bernstein [`n `k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `bernstein
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
      (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.SpecialFunctions.Bernstein.«term_/ₙ»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.SpecialFunctions.Bernstein.«term_/ₙ»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.SpecialFunctions.Bernstein.«term_/ₙ»', expected 'Analysis.SpecialFunctions.Bernstein.term_/ₙ._@.Analysis.SpecialFunctions.Bernstein._hyg.502'
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
    The `n`-th approximation of a continuous function on `[0,1]` by Bernstein polynomials,
    given by `∑ k, f (k/n) * bernstein n k x`.
    -/
  def
    bernsteinApproximation
    ( n : ℕ ) ( f : C( I , ℝ ) ) : C( I , ℝ )
    := ∑ k : Fin n + 1 , f k /ₙ • bernstein n k
#align bernstein_approximation bernsteinApproximation

/-!
We now set up some of the basic machinery of the proof that the Bernstein approximations
converge uniformly.

A key player is the set `S f ε h n x`,
for some function `f : C(I, ℝ)`, `h : 0 < ε`, `n : ℕ` and `x : I`.

This is the set of points `k` in `fin (n+1)` such that
`k/n` is within `δ` of `x`, where `δ` is the modulus of uniform continuity for `f`,
chosen so `|f x - f y| < ε/2` when `|x - y| < δ`.

We show that if `k ∉ S`, then `1 ≤ δ^-2 * (x - k/n)^2`.
-/


namespace bernsteinApproximation

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
      (Command.declId `apply [])
      (Command.declSig
       [(Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")
        (Term.explicitBinder
         "("
         [`f]
         [":"
          (Topology.ContinuousFunction.Basic.«termC(_,_)»
           "C("
           (unitInterval.Topology.UnitInterval.unit_interval "I")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")")]
         []
         ")")
        (Term.explicitBinder
         "("
         [`x]
         [":" (unitInterval.Topology.UnitInterval.unit_interval "I")]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `bernsteinApproximation [`n `f `x])
         "="
         (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
          "∑"
          (Std.ExtendedBinder.extBinders
           (Std.ExtendedBinder.extBinder
            (Lean.binderIdent `k)
            [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]))
          ", "
          («term_*_»
           (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
           "*"
           (Term.app `bernstein [`n `k `x]))))))
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
            ["[" [(Tactic.simpLemma [] [] `bernsteinApproximation)] "]"]
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
           ["[" [(Tactic.simpLemma [] [] `bernsteinApproximation)] "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `bernsteinApproximation)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `bernsteinApproximation
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app `bernsteinApproximation [`n `f `x])
       "="
       (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
        "∑"
        (Std.ExtendedBinder.extBinders
         (Std.ExtendedBinder.extBinder
          (Lean.binderIdent `k)
          [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]))
        ", "
        («term_*_»
         (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
         "*"
         (Term.app `bernstein [`n `k `x]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
       "∑"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder
         (Lean.binderIdent `k)
         [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]))
       ", "
       («term_*_»
        (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
        "*"
        (Term.app `bernstein [`n `k `x])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
       "*"
       (Term.app `bernstein [`n `k `x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `bernstein [`n `k `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `bernstein
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.SpecialFunctions.Bernstein.«term_/ₙ»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.SpecialFunctions.Bernstein.«term_/ₙ»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.SpecialFunctions.Bernstein.«term_/ₙ»', expected 'Analysis.SpecialFunctions.Bernstein.term_/ₙ._@.Analysis.SpecialFunctions.Bernstein._hyg.502'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    apply
    ( n : ℕ ) ( f : C( I , ℝ ) ) ( x : I )
      : bernsteinApproximation n f x = ∑ k : Fin n + 1 , f k /ₙ * bernstein n k x
    := by simp [ bernsteinApproximation ]
#align bernstein_approximation.apply bernsteinApproximation.apply

/-- The modulus of (uniform) continuity for `f`, chosen so `|f x - f y| < ε/2` when `|x - y| < δ`.
-/
def δ (f : C(I, ℝ)) (ε : ℝ) (h : 0 < ε) : ℝ :=
  f.modulus (ε / 2) (half_pos h)
#align bernstein_approximation.δ bernsteinApproximation.δ

theorem δ_pos {f : C(I, ℝ)} {ε : ℝ} {h : 0 < ε} : 0 < δ f ε h :=
  f.modulus_pos
#align bernstein_approximation.δ_pos bernsteinApproximation.δ_pos

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "The set of points `k` so `k/n` is within `δ` of `x`.\n-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `s [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`f]
         [":"
          (Topology.ContinuousFunction.Basic.«termC(_,_)»
           "C("
           (unitInterval.Topology.UnitInterval.unit_interval "I")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")")]
         []
         ")")
        (Term.explicitBinder "(" [`ε] [":" (Data.Real.Basic.termℝ "ℝ")] [] ")")
        (Term.explicitBinder "(" [`h] [":" («term_<_» (num "0") "<" `ε)] [] ")")
        (Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")
        (Term.explicitBinder
         "("
         [`x]
         [":" (unitInterval.Topology.UnitInterval.unit_interval "I")]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `Finset [(Term.app `Fin [(«term_+_» `n "+" (num "1"))])]))])
      (Command.declValSimple
       ":="
       (Term.proj
        (Set.«term{_|_}»
         "{"
         (Std.ExtendedBinder.extBinder
          (Lean.binderIdent `k)
          [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))])
         "|"
         («term_<_»
          (Term.app `dist [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ") `x])
          "<"
          (Term.app `δ [`f `ε `h]))
         "}")
        "."
        `toFinset)
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Set.«term{_|_}»
        "{"
        (Std.ExtendedBinder.extBinder
         (Lean.binderIdent `k)
         [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))])
        "|"
        («term_<_»
         (Term.app `dist [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ") `x])
         "<"
         (Term.app `δ [`f `ε `h]))
        "}")
       "."
       `toFinset)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Set.«term{_|_}»
       "{"
       (Std.ExtendedBinder.extBinder
        (Lean.binderIdent `k)
        [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))])
       "|"
       («term_<_»
        (Term.app `dist [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ") `x])
        "<"
        (Term.app `δ [`f `ε `h]))
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_»
       (Term.app `dist [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ") `x])
       "<"
       (Term.app `δ [`f `ε `h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `δ [`f `ε `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `δ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `dist [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ") `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.SpecialFunctions.Bernstein.«term_/ₙ»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.SpecialFunctions.Bernstein.«term_/ₙ»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.SpecialFunctions.Bernstein.«term_/ₙ»', expected 'Analysis.SpecialFunctions.Bernstein.term_/ₙ._@.Analysis.SpecialFunctions.Bernstein._hyg.502'
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
    The set of points `k` so `k/n` is within `δ` of `x`.
    -/
  def
    s
    ( f : C( I , ℝ ) ) ( ε : ℝ ) ( h : 0 < ε ) ( n : ℕ ) ( x : I ) : Finset Fin n + 1
    := { k : Fin n + 1 | dist k /ₙ x < δ f ε h } . toFinset
#align bernstein_approximation.S bernsteinApproximation.s

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "If `k ∈ S`, then `f(k/n)` is close to `f x`.\n-/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `lt_of_mem_S [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`f]
         [":"
          (Topology.ContinuousFunction.Basic.«termC(_,_)»
           "C("
           (unitInterval.Topology.UnitInterval.unit_interval "I")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")")]
         "}")
        (Term.implicitBinder "{" [`ε] [":" (Data.Real.Basic.termℝ "ℝ")] "}")
        (Term.implicitBinder "{" [`h] [":" («term_<_» (num "0") "<" `ε)] "}")
        (Term.implicitBinder "{" [`n] [":" (termℕ "ℕ")] "}")
        (Term.implicitBinder
         "{"
         [`x]
         [":" (unitInterval.Topology.UnitInterval.unit_interval "I")]
         "}")
        (Term.implicitBinder "{" [`k] [":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))])] "}")
        (Term.explicitBinder
         "("
         [`m]
         [":" («term_∈_» `k "∈" (Term.app `s [`f `ε `h `n `x]))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_<_»
         («term|___|»
          (group "|")
          («term_-_»
           (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
           "-"
           (Term.app `f [`x]))
          (group)
          "|")
         "<"
         («term_/_» `ε "/" (num "2")))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.apply
            "apply"
            (Term.app
             `f.dist_lt_of_dist_lt_modulus
             [(«term_/_» `ε "/" (num "2")) (Term.app `half_pos [`h])]))
           []
           (Std.Tactic.Simpa.simpa
            "simpa"
            []
            []
            (Std.Tactic.Simpa.simpaArgsRest
             []
             []
             []
             [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `S)] "]")]
             ["using" `m]))])))
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
           (Term.app
            `f.dist_lt_of_dist_lt_modulus
            [(«term_/_» `ε "/" (num "2")) (Term.app `half_pos [`h])]))
          []
          (Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            []
            [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `S)] "]")]
            ["using" `m]))])))
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
        [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `S)] "]")]
        ["using" `m]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `S
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply
       "apply"
       (Term.app
        `f.dist_lt_of_dist_lt_modulus
        [(«term_/_» `ε "/" (num "2")) (Term.app `half_pos [`h])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `f.dist_lt_of_dist_lt_modulus
       [(«term_/_» `ε "/" (num "2")) (Term.app `half_pos [`h])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `half_pos [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `half_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `half_pos [`h]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_/_» `ε "/" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 70, (some 71, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_/_» `ε "/" (num "2")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f.dist_lt_of_dist_lt_modulus
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_<_»
       («term|___|»
        (group "|")
        («term_-_»
         (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
         "-"
         (Term.app `f [`x]))
        (group)
        "|")
       "<"
       («term_/_» `ε "/" (num "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» `ε "/" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term|___|»
       (group "|")
       («term_-_»
        (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
        "-"
        (Term.app `f [`x]))
       (group)
       "|")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_»
       (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
       "-"
       (Term.app `f [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.SpecialFunctions.Bernstein.«term_/ₙ»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.SpecialFunctions.Bernstein.«term_/ₙ»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.SpecialFunctions.Bernstein.«term_/ₙ»', expected 'Analysis.SpecialFunctions.Bernstein.term_/ₙ._@.Analysis.SpecialFunctions.Bernstein._hyg.502'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    If `k ∈ S`, then `f(k/n)` is close to `f x`.
    -/
  theorem
    lt_of_mem_S
    { f : C( I , ℝ ) }
        { ε : ℝ }
        { h : 0 < ε }
        { n : ℕ }
        { x : I }
        { k : Fin n + 1 }
        ( m : k ∈ s f ε h n x )
      : | f k /ₙ - f x | < ε / 2
    := by apply f.dist_lt_of_dist_lt_modulus ε / 2 half_pos h simpa [ S ] using m
#align bernstein_approximation.lt_of_mem_S bernsteinApproximation.lt_of_mem_S

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "If `k ∉ S`, then as `δ ≤ |x - k/n|`, we have the inequality `1 ≤ δ^-2 * (x - k/n)^2`.\nThis particular formulation will be helpful later.\n-/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `le_of_mem_S_compl [])
      (Command.declSig
       [(Term.implicitBinder
         "{"
         [`f]
         [":"
          (Topology.ContinuousFunction.Basic.«termC(_,_)»
           "C("
           (unitInterval.Topology.UnitInterval.unit_interval "I")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")")]
         "}")
        (Term.implicitBinder "{" [`ε] [":" (Data.Real.Basic.termℝ "ℝ")] "}")
        (Term.implicitBinder "{" [`h] [":" («term_<_» (num "0") "<" `ε)] "}")
        (Term.implicitBinder "{" [`n] [":" (termℕ "ℕ")] "}")
        (Term.implicitBinder
         "{"
         [`x]
         [":" (unitInterval.Topology.UnitInterval.unit_interval "I")]
         "}")
        (Term.implicitBinder "{" [`k] [":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))])] "}")
        (Term.explicitBinder
         "("
         [`m]
         [":" («term_∈_» `k "∈" (Order.Basic.«term_ᶜ» (Term.app `s [`f `ε `h `n `x]) "ᶜ"))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         (Term.typeAscription "(" (num "1") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
         "≤"
         («term_*_»
          («term_^_»
           (Term.app `δ [`f `ε `h])
           "^"
           (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")"))
          "*"
          («term_^_»
           («term_-_» `x "-" (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
           "^"
           (num "2"))))))
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
             [(Tactic.simpLemma [] [] `Finset.mem_compl)
              ","
              (Tactic.simpLemma [] [] `not_lt)
              ","
              (Tactic.simpLemma [] [] `Set.mem_to_finset)
              ","
              (Tactic.simpLemma [] [] `Set.mem_setOf_eq)
              ","
              (Tactic.simpLemma [] [] `S)]
             "]"]
            [(Tactic.location "at" (Tactic.locationHyp [`m] []))])
           []
           (Tactic.tacticErw__
            "erw"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `zpow_neg)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `div_eq_inv_mul)
              ","
              (Tactic.rwRule [] (Term.app `one_le_div [(Term.app `pow_pos [`δ_pos (num "2")])]))
              ","
              (Tactic.rwRule [] `sq_le_sq)
              ","
              (Tactic.rwRule [] (Term.app `abs_of_pos [`δ_pos]))]
             "]")
            [])
           []
           (Std.Tactic.tacticRwa__
            "rwa"
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dist_comm)] "]")
            [(Tactic.location "at" (Tactic.locationHyp [`m] []))])])))
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
            [(Tactic.simpLemma [] [] `Finset.mem_compl)
             ","
             (Tactic.simpLemma [] [] `not_lt)
             ","
             (Tactic.simpLemma [] [] `Set.mem_to_finset)
             ","
             (Tactic.simpLemma [] [] `Set.mem_setOf_eq)
             ","
             (Tactic.simpLemma [] [] `S)]
            "]"]
           [(Tactic.location "at" (Tactic.locationHyp [`m] []))])
          []
          (Tactic.tacticErw__
           "erw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `zpow_neg)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `div_eq_inv_mul)
             ","
             (Tactic.rwRule [] (Term.app `one_le_div [(Term.app `pow_pos [`δ_pos (num "2")])]))
             ","
             (Tactic.rwRule [] `sq_le_sq)
             ","
             (Tactic.rwRule [] (Term.app `abs_of_pos [`δ_pos]))]
            "]")
           [])
          []
          (Std.Tactic.tacticRwa__
           "rwa"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dist_comm)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`m] []))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dist_comm)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`m] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `dist_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticErw__
       "erw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `zpow_neg)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `div_eq_inv_mul)
         ","
         (Tactic.rwRule [] (Term.app `one_le_div [(Term.app `pow_pos [`δ_pos (num "2")])]))
         ","
         (Tactic.rwRule [] `sq_le_sq)
         ","
         (Tactic.rwRule [] (Term.app `abs_of_pos [`δ_pos]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `abs_of_pos [`δ_pos])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `δ_pos
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `abs_of_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sq_le_sq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `one_le_div [(Term.app `pow_pos [`δ_pos (num "2")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pow_pos [`δ_pos (num "2")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `δ_pos
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pow_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `pow_pos [`δ_pos (num "2")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `one_le_div
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `div_eq_inv_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `zpow_neg
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
        [(Tactic.simpLemma [] [] `Finset.mem_compl)
         ","
         (Tactic.simpLemma [] [] `not_lt)
         ","
         (Tactic.simpLemma [] [] `Set.mem_to_finset)
         ","
         (Tactic.simpLemma [] [] `Set.mem_setOf_eq)
         ","
         (Tactic.simpLemma [] [] `S)]
        "]"]
       [(Tactic.location "at" (Tactic.locationHyp [`m] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `m
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `S
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
      `Set.mem_to_finset
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `not_lt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Finset.mem_compl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≤_»
       (Term.typeAscription "(" (num "1") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
       "≤"
       («term_*_»
        («term_^_»
         (Term.app `δ [`f `ε `h])
         "^"
         (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")"))
        "*"
        («term_^_»
         («term_-_» `x "-" (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
         "^"
         (num "2"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_^_»
        (Term.app `δ [`f `ε `h])
        "^"
        (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")"))
       "*"
       («term_^_»
        («term_-_» `x "-" (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
        "^"
        (num "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       («term_-_» `x "-" (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
       "^"
       (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      («term_-_» `x "-" (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.SpecialFunctions.Bernstein.«term_/ₙ»', expected 'Analysis.SpecialFunctions.Bernstein.term_/ₙ._@.Analysis.SpecialFunctions.Bernstein._hyg.502'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    If `k ∉ S`, then as `δ ≤ |x - k/n|`, we have the inequality `1 ≤ δ^-2 * (x - k/n)^2`.
    This particular formulation will be helpful later.
    -/
  theorem
    le_of_mem_S_compl
    { f : C( I , ℝ ) }
        { ε : ℝ }
        { h : 0 < ε }
        { n : ℕ }
        { x : I }
        { k : Fin n + 1 }
        ( m : k ∈ s f ε h n x ᶜ )
      : ( 1 : ℝ ) ≤ δ f ε h ^ ( - 2 : ℤ ) * x - k /ₙ ^ 2
    :=
      by
        simp only [ Finset.mem_compl , not_lt , Set.mem_to_finset , Set.mem_setOf_eq , S ] at m
          erw
            [
              zpow_neg , ← div_eq_inv_mul , one_le_div pow_pos δ_pos 2 , sq_le_sq , abs_of_pos δ_pos
              ]
          rwa [ dist_comm ] at m
#align bernstein_approximation.le_of_mem_S_compl bernsteinApproximation.le_of_mem_S_compl

end bernsteinApproximation

open bernsteinApproximation

open BoundedContinuousFunction

open Filter

open TopologicalSpace

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The Bernstein approximations\n```\n∑ k : fin (n+1), f (k/n : ℝ) * n.choose k * x^k * (1-x)^(n-k)\n```\nfor a continuous function `f : C([0,1], ℝ)` converge uniformly to `f` as `n` tends to infinity.\n\nThis is the proof given in [Richard Beals' *Analysis, an introduction*][beals-analysis], §7D,\nand reproduced on wikipedia.\n-/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `bernstein_approximation_uniform [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`f]
         [":"
          (Topology.ContinuousFunction.Basic.«termC(_,_)»
           "C("
           (unitInterval.Topology.UnitInterval.unit_interval "I")
           ", "
           (Data.Real.Basic.termℝ "ℝ")
           ")")]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `Tendsto
         [(Term.fun
           "fun"
           (Term.basicFun
            [`n]
            [(Term.typeSpec ":" (termℕ "ℕ"))]
            "=>"
            (Term.app `bernsteinApproximation [`n `f])))
          `atTop
          (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`f])])))
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
             [(Tactic.simpLemma [] [] `metric.nhds_basis_ball.tendsto_right_iff)
              ","
              (Tactic.simpLemma [] [] `Metric.mem_ball)
              ","
              (Tactic.simpLemma [] [] `dist_eq_norm)]
             "]"]
            [])
           []
           (Tactic.intro "intro" [`ε `h])
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl (Term.letIdDecl `δ [] [] ":=" (Term.app `δ [`f `ε `h]))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`nhds_zero []]
              []
              ":="
              (Term.app
               `tendsto_const_div_at_top_nhds_0_nat
               [(«term_*_»
                 («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
                 "*"
                 («term_^_»
                  `δ
                  "^"
                  (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")")))]))))
           []
           (Tactic.filterUpwards
            "filter_upwards"
            [(Tactic.termList
              "["
              [(Term.app
                `nhds_zero.eventually
                [(Term.app `gt_mem_nhds [(Term.app `half_pos [`h])])])
               ","
               (Term.app `eventually_gt_at_top [(num "0")])]
              "]")]
            ["with" [`n `nh `npos']]
            [])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`npos []]
              [(Term.typeSpec
                ":"
                («term_<_»
                 (num "0")
                 "<"
                 (Term.typeAscription "(" `n ":" [(Data.Real.Basic.termℝ "ℝ")] ")")))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `npos')]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`w₁ []]
              [(Term.typeSpec
                ":"
                («term_≤_»
                 (num "0")
                 "≤"
                 («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))))]
              ":="
              (Term.app
               `mul_nonneg
               [(Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
                (Term.app `norm_nonneg [`f])]))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`w₂ []]
              [(Term.typeSpec
                ":"
                («term_≤_»
                 (num "0")
                 "≤"
                 («term_*_»
                  («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
                  "*"
                  («term_^_»
                   `δ
                   "^"
                   (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")")))))]
              ":="
              (Term.app `mul_nonneg [`w₁ `pow_minus_two_nonneg]))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] (Term.app `ContinuousMap.norm_lt_iff [(Term.hole "_") `h]))]
             "]")
            [])
           []
           (Tactic.intro "intro" [`x])
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl (Term.letIdDecl `S [] [] ":=" (Term.app `S [`f `ε `h `n `x]))))
           []
           (calcTactic
            "calc"
            (calcStep
             («term_=_»
              («term|___|»
               (group "|")
               (Term.app («term_-_» (Term.app `bernsteinApproximation [`n `f]) "-" `f) [`x])
               (group)
               "|")
              "="
              («term|___|»
               (group "|")
               («term_-_» (Term.app `bernsteinApproximation [`n `f `x]) "-" (Term.app `f [`x]))
               (group)
               "|"))
             ":="
             `rfl)
            [(calcStep
              («term_=_»
               (Term.hole "_")
               "="
               («term|___|»
                (group "|")
                («term_-_»
                 (Term.app `bernsteinApproximation [`n `f `x])
                 "-"
                 («term_*_» (Term.app `f [`x]) "*" (num "1")))
                (group)
                "|"))
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_one)] "]")
                   [])]))))
             (calcStep
              («term_=_»
               (Term.hole "_")
               "="
               («term|___|»
                (group "|")
                («term_-_»
                 (Term.app `bernsteinApproximation [`n `f `x])
                 "-"
                 («term_*_»
                  (Term.app `f [`x])
                  "*"
                  (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
                   "∑"
                   (Std.ExtendedBinder.extBinders
                    (Std.ExtendedBinder.extBinder
                     (Lean.binderIdent `k)
                     [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]))
                   ", "
                   (Term.app `bernstein [`n `k `x]))))
                (group)
                "|"))
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `bernstein.probability)] "]")
                   [])]))))
             (calcStep
              («term_=_»
               (Term.hole "_")
               "="
               («term|___|»
                (group "|")
                (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
                 "∑"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder
                   (Lean.binderIdent `k)
                   [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]))
                 ", "
                 («term_*_»
                  («term_-_»
                   (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
                   "-"
                   (Term.app `f [`x]))
                  "*"
                  (Term.app `bernstein [`n `k `x])))
                (group)
                "|"))
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
                    [(Tactic.simpLemma [] [] `bernsteinApproximation)
                     ","
                     (Tactic.simpLemma [] [] `Finset.mul_sum)
                     ","
                     (Tactic.simpLemma [] [] `sub_mul)]
                    "]"]
                   [])]))))
             (calcStep
              («term_≤_»
               (Term.hole "_")
               "≤"
               (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
                "∑"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder
                  (Lean.binderIdent `k)
                  [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]))
                ", "
                («term|___|»
                 (group "|")
                 («term_*_»
                  («term_-_»
                   (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
                   "-"
                   (Term.app `f [`x]))
                  "*"
                  (Term.app `bernstein [`n `k `x]))
                 (group)
                 "|")))
              ":="
              (Term.app `Finset.abs_sum_le_sum_abs [(Term.hole "_") (Term.hole "_")]))
             (calcStep
              («term_=_»
               (Term.hole "_")
               "="
               (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
                "∑"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder
                  (Lean.binderIdent `k)
                  [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]))
                ", "
                («term_*_»
                 («term|___|»
                  (group "|")
                  («term_-_»
                   (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
                   "-"
                   (Term.app `f [`x]))
                  (group)
                  "|")
                 "*"
                 (Term.app `bernstein [`n `k `x]))))
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Mathlib.Tactic.tacticSimp_rw__
                   "simp_rw"
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `abs_mul)
                     ","
                     (Tactic.rwRule [] (Term.app `abs_eq_self.mpr [`bernstein_nonneg]))]
                    "]")
                   [])]))))
             (calcStep
              («term_=_»
               (Term.hole "_")
               "="
               («term_+_»
                (BigOperators.Algebra.BigOperators.Basic.finset.sum
                 "∑"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `k) []))
                 " in "
                 `S
                 ", "
                 («term_*_»
                  («term|___|»
                   (group "|")
                   («term_-_»
                    (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
                    "-"
                    (Term.app `f [`x]))
                   (group)
                   "|")
                  "*"
                  (Term.app `bernstein [`n `k `x])))
                "+"
                (BigOperators.Algebra.BigOperators.Basic.finset.sum
                 "∑"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `k) []))
                 " in "
                 (Order.Basic.«term_ᶜ» `S "ᶜ")
                 ", "
                 («term_*_»
                  («term|___|»
                   (group "|")
                   («term_-_»
                    (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
                    "-"
                    (Term.app `f [`x]))
                   (group)
                   "|")
                  "*"
                  (Term.app `bernstein [`n `k `x])))))
              ":="
              (Term.proj (Term.app `S.sum_add_sum_compl [(Term.hole "_")]) "." `symm))
             (calcStep
              («term_<_»
               (Term.hole "_")
               "<"
               («term_+_» («term_/_» `ε "/" (num "2")) "+" («term_/_» `ε "/" (num "2"))))
              ":="
              (Term.app `add_lt_add_of_le_of_lt [(Term.hole "_") (Term.hole "_")]))
             (calcStep («term_=_» (Term.hole "_") "=" `ε) ":=" (Term.app `add_halves [`ε]))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(calcTactic
              "calc"
              (calcStep
               («term_≤_»
                (BigOperators.Algebra.BigOperators.Basic.finset.sum
                 "∑"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `k) []))
                 " in "
                 `S
                 ", "
                 («term_*_»
                  («term|___|»
                   (group "|")
                   («term_-_»
                    (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
                    "-"
                    (Term.app `f [`x]))
                   (group)
                   "|")
                  "*"
                  (Term.app `bernstein [`n `k `x])))
                "≤"
                (BigOperators.Algebra.BigOperators.Basic.finset.sum
                 "∑"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `k) []))
                 " in "
                 `S
                 ", "
                 («term_*_» («term_/_» `ε "/" (num "2")) "*" (Term.app `bernstein [`n `k `x]))))
               ":="
               (Term.app
                `Finset.sum_le_sum
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [`k `m]
                   []
                   "=>"
                   (Term.app
                    `mul_le_mul_of_nonneg_right
                    [(Term.app `le_of_lt [(Term.app `lt_of_mem_S [`m])]) `bernstein_nonneg])))]))
              [(calcStep
                («term_=_»
                 (Term.hole "_")
                 "="
                 («term_*_»
                  («term_/_» `ε "/" (num "2"))
                  "*"
                  (BigOperators.Algebra.BigOperators.Basic.finset.sum
                   "∑"
                   (Std.ExtendedBinder.extBinders
                    (Std.ExtendedBinder.extBinder (Lean.binderIdent `k) []))
                   " in "
                   `S
                   ", "
                   (Term.app `bernstein [`n `k `x]))))
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.mul_sum)] "]")
                     [])]))))
               (calcStep
                («term_≤_»
                 (Term.hole "_")
                 "≤"
                 («term_*_»
                  («term_/_» `ε "/" (num "2"))
                  "*"
                  (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
                   "∑"
                   (Std.ExtendedBinder.extBinders
                    (Std.ExtendedBinder.extBinder
                     (Lean.binderIdent `k)
                     [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]))
                   ", "
                   (Term.app `bernstein [`n `k `x]))))
                ":="
                (Term.app
                 `mul_le_mul_of_nonneg_left
                 [(Term.app
                   `Finset.sum_le_univ_sum_of_nonneg
                   [(Term.fun "fun" (Term.basicFun [`k] [] "=>" `bernstein_nonneg))])
                  (Term.app `le_of_lt [(Term.app `half_pos [`h])])]))
               (calcStep
                («term_=_» (Term.hole "_") "=" («term_/_» `ε "/" (num "2")))
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
                      [(Tactic.rwRule [] `bernstein.probability) "," (Tactic.rwRule [] `mul_one)]
                      "]")
                     [])]))))])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(calcTactic
              "calc"
              (calcStep
               («term_≤_»
                (BigOperators.Algebra.BigOperators.Basic.finset.sum
                 "∑"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `k) []))
                 " in "
                 (Order.Basic.«term_ᶜ» `S "ᶜ")
                 ", "
                 («term_*_»
                  («term|___|»
                   (group "|")
                   («term_-_»
                    (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
                    "-"
                    (Term.app `f [`x]))
                   (group)
                   "|")
                  "*"
                  (Term.app `bernstein [`n `k `x])))
                "≤"
                (BigOperators.Algebra.BigOperators.Basic.finset.sum
                 "∑"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `k) []))
                 " in "
                 (Order.Basic.«term_ᶜ» `S "ᶜ")
                 ", "
                 («term_*_»
                  («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
                  "*"
                  (Term.app `bernstein [`n `k `x]))))
               ":="
               (Term.app
                `Finset.sum_le_sum
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [`k `m]
                   []
                   "=>"
                   (Term.app
                    `mul_le_mul_of_nonneg_right
                    [(Term.app `f.dist_le_two_norm [(Term.hole "_") (Term.hole "_")])
                     `bernstein_nonneg])))]))
              [(calcStep
                («term_=_»
                 (Term.hole "_")
                 "="
                 («term_*_»
                  («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
                  "*"
                  (BigOperators.Algebra.BigOperators.Basic.finset.sum
                   "∑"
                   (Std.ExtendedBinder.extBinders
                    (Std.ExtendedBinder.extBinder (Lean.binderIdent `k) []))
                   " in "
                   (Order.Basic.«term_ᶜ» `S "ᶜ")
                   ", "
                   (Term.app `bernstein [`n `k `x]))))
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.mul_sum)] "]")
                     [])]))))
               (calcStep
                («term_≤_»
                 (Term.hole "_")
                 "≤"
                 («term_*_»
                  («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
                  "*"
                  (BigOperators.Algebra.BigOperators.Basic.finset.sum
                   "∑"
                   (Std.ExtendedBinder.extBinders
                    (Std.ExtendedBinder.extBinder (Lean.binderIdent `k) []))
                   " in "
                   (Order.Basic.«term_ᶜ» `S "ᶜ")
                   ", "
                   («term_*_»
                    («term_*_»
                     («term_^_»
                      `δ
                      "^"
                      (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")"))
                     "*"
                     («term_^_»
                      («term_-_» `x "-" (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
                      "^"
                      (num "2")))
                    "*"
                    (Term.app `bernstein [`n `k `x])))))
                ":="
                (Term.app
                 `mul_le_mul_of_nonneg_left
                 [(Term.app
                   `Finset.sum_le_sum
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [`k `m]
                      []
                      "=>"
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Mathlib.Tactic.Conv.convLHS
                           "conv_lhs"
                           []
                           []
                           "=>"
                           (Tactic.Conv.convSeq
                            (Tactic.Conv.convSeq1Indented
                             [(Tactic.Conv.convRw__
                               "rw"
                               []
                               (Tactic.rwRuleSeq
                                "["
                                [(Tactic.rwRule
                                  [(patternIgnore (token.«← » "←"))]
                                  (Term.app
                                   `one_mul
                                   [(Term.app
                                     `bernstein
                                     [(Term.hole "_") (Term.hole "_") (Term.hole "_")])]))]
                                "]"))])))
                          []
                          (Tactic.exact
                           "exact"
                           (Term.app
                            `mul_le_mul_of_nonneg_right
                            [(Term.app `le_of_mem_S_compl [`m]) `bernstein_nonneg]))])))))])
                  `w₁]))
               (calcStep
                («term_≤_»
                 (Term.hole "_")
                 "≤"
                 («term_*_»
                  («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
                  "*"
                  (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
                   "∑"
                   (Std.ExtendedBinder.extBinders
                    (Std.ExtendedBinder.extBinder
                     (Lean.binderIdent `k)
                     [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]))
                   ", "
                   («term_*_»
                    («term_*_»
                     («term_^_»
                      `δ
                      "^"
                      (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")"))
                     "*"
                     («term_^_»
                      («term_-_» `x "-" (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
                      "^"
                      (num "2")))
                    "*"
                    (Term.app `bernstein [`n `k `x])))))
                ":="
                (Term.app
                 `mul_le_mul_of_nonneg_left
                 [(Term.app
                   `Finset.sum_le_univ_sum_of_nonneg
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [`k]
                      []
                      "=>"
                      (Term.app
                       `mul_nonneg
                       [(Term.app
                         `mul_nonneg
                         [`pow_minus_two_nonneg (Term.app `sq_nonneg [(Term.hole "_")])])
                        `bernstein_nonneg])))])
                  `w₁]))
               (calcStep
                («term_=_»
                 (Term.hole "_")
                 "="
                 («term_*_»
                  («term_*_»
                   («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
                   "*"
                   («term_^_»
                    `δ
                    "^"
                    (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")")))
                  "*"
                  (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
                   "∑"
                   (Std.ExtendedBinder.extBinders
                    (Std.ExtendedBinder.extBinder
                     (Lean.binderIdent `k)
                     [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]))
                   ", "
                   («term_*_»
                    («term_^_»
                     («term_-_» `x "-" (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
                     "^"
                     (num "2"))
                    "*"
                    (Term.app `bernstein [`n `k `x])))))
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Mathlib.Tactic.Conv.convRHS
                     "conv_rhs"
                     []
                     []
                     "=>"
                     (Tactic.Conv.convSeq
                      (Tactic.Conv.convSeq1Indented
                       [(Tactic.Conv.convRw__
                         "rw"
                         []
                         (Tactic.rwRuleSeq
                          "["
                          [(Tactic.rwRule [] `mul_assoc) "," (Tactic.rwRule [] `Finset.mul_sum)]
                          "]"))
                        []
                        (Tactic.Conv.simp
                         "simp"
                         []
                         []
                         ["only"]
                         ["["
                          [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `mul_assoc)]
                          "]"])])))]))))
               (calcStep
                («term_=_»
                 (Term.hole "_")
                 "="
                 («term_/_»
                  («term_*_»
                   («term_*_»
                    («term_*_»
                     («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
                     "*"
                     («term_^_»
                      `δ
                      "^"
                      (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")")))
                    "*"
                    `x)
                   "*"
                   («term_-_» (num "1") "-" `x))
                  "/"
                  `n))
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `variance [`npos]))] "]")
                     [])
                    []
                    (Mathlib.Tactic.RingNF.ring "ring")]))))
               (calcStep
                («term_≤_»
                 (Term.hole "_")
                 "≤"
                 («term_/_»
                  («term_*_»
                   («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
                   "*"
                   («term_^_»
                    `δ
                    "^"
                    (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")")))
                  "/"
                  `n))
                ":="
                («term_<|_»
                 (Term.proj (Term.app `div_le_div_right [`npos]) "." `mpr)
                 "<|"
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.«tactic_<;>_»
                      (Tactic.refine'
                       "refine'"
                       (Term.app
                        `mul_le_of_le_of_le_one'
                        [(Term.app `mul_le_of_le_one_right [`w₂ (Term.hole "_")])
                         (Term.hole "_")
                         (Term.hole "_")
                         `w₂]))
                      "<;>"
                      (Tactic.unitInterval "unit_interval"))])))))
               (calcStep
                («term_<_» (Term.hole "_") "<" («term_/_» `ε "/" (num "2")))
                ":="
                `nh)])])])))
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
            [(Tactic.simpLemma [] [] `metric.nhds_basis_ball.tendsto_right_iff)
             ","
             (Tactic.simpLemma [] [] `Metric.mem_ball)
             ","
             (Tactic.simpLemma [] [] `dist_eq_norm)]
            "]"]
           [])
          []
          (Tactic.intro "intro" [`ε `h])
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl (Term.letIdDecl `δ [] [] ":=" (Term.app `δ [`f `ε `h]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`nhds_zero []]
             []
             ":="
             (Term.app
              `tendsto_const_div_at_top_nhds_0_nat
              [(«term_*_»
                («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
                "*"
                («term_^_»
                 `δ
                 "^"
                 (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")")))]))))
          []
          (Tactic.filterUpwards
           "filter_upwards"
           [(Tactic.termList
             "["
             [(Term.app `nhds_zero.eventually [(Term.app `gt_mem_nhds [(Term.app `half_pos [`h])])])
              ","
              (Term.app `eventually_gt_at_top [(num "0")])]
             "]")]
           ["with" [`n `nh `npos']]
           [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`npos []]
             [(Term.typeSpec
               ":"
               («term_<_»
                (num "0")
                "<"
                (Term.typeAscription "(" `n ":" [(Data.Real.Basic.termℝ "ℝ")] ")")))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `npos')]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`w₁ []]
             [(Term.typeSpec
               ":"
               («term_≤_»
                (num "0")
                "≤"
                («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))))]
             ":="
             (Term.app
              `mul_nonneg
              [(Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented [(Mathlib.Tactic.normNum "norm_num" [] [] [])])))
               (Term.app `norm_nonneg [`f])]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`w₂ []]
             [(Term.typeSpec
               ":"
               («term_≤_»
                (num "0")
                "≤"
                («term_*_»
                 («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
                 "*"
                 («term_^_»
                  `δ
                  "^"
                  (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")")))))]
             ":="
             (Term.app `mul_nonneg [`w₁ `pow_minus_two_nonneg]))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] (Term.app `ContinuousMap.norm_lt_iff [(Term.hole "_") `h]))]
            "]")
           [])
          []
          (Tactic.intro "intro" [`x])
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl (Term.letIdDecl `S [] [] ":=" (Term.app `S [`f `ε `h `n `x]))))
          []
          (calcTactic
           "calc"
           (calcStep
            («term_=_»
             («term|___|»
              (group "|")
              (Term.app («term_-_» (Term.app `bernsteinApproximation [`n `f]) "-" `f) [`x])
              (group)
              "|")
             "="
             («term|___|»
              (group "|")
              («term_-_» (Term.app `bernsteinApproximation [`n `f `x]) "-" (Term.app `f [`x]))
              (group)
              "|"))
            ":="
            `rfl)
           [(calcStep
             («term_=_»
              (Term.hole "_")
              "="
              («term|___|»
               (group "|")
               («term_-_»
                (Term.app `bernsteinApproximation [`n `f `x])
                "-"
                («term_*_» (Term.app `f [`x]) "*" (num "1")))
               (group)
               "|"))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_one)] "]")
                  [])]))))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              («term|___|»
               (group "|")
               («term_-_»
                (Term.app `bernsteinApproximation [`n `f `x])
                "-"
                («term_*_»
                 (Term.app `f [`x])
                 "*"
                 (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
                  "∑"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder
                    (Lean.binderIdent `k)
                    [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]))
                  ", "
                  (Term.app `bernstein [`n `k `x]))))
               (group)
               "|"))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `bernstein.probability)] "]")
                  [])]))))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              («term|___|»
               (group "|")
               (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
                "∑"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder
                  (Lean.binderIdent `k)
                  [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]))
                ", "
                («term_*_»
                 («term_-_»
                  (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
                  "-"
                  (Term.app `f [`x]))
                 "*"
                 (Term.app `bernstein [`n `k `x])))
               (group)
               "|"))
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
                   [(Tactic.simpLemma [] [] `bernsteinApproximation)
                    ","
                    (Tactic.simpLemma [] [] `Finset.mul_sum)
                    ","
                    (Tactic.simpLemma [] [] `sub_mul)]
                   "]"]
                  [])]))))
            (calcStep
             («term_≤_»
              (Term.hole "_")
              "≤"
              (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
               "∑"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder
                 (Lean.binderIdent `k)
                 [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]))
               ", "
               («term|___|»
                (group "|")
                («term_*_»
                 («term_-_»
                  (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
                  "-"
                  (Term.app `f [`x]))
                 "*"
                 (Term.app `bernstein [`n `k `x]))
                (group)
                "|")))
             ":="
             (Term.app `Finset.abs_sum_le_sum_abs [(Term.hole "_") (Term.hole "_")]))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
               "∑"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder
                 (Lean.binderIdent `k)
                 [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]))
               ", "
               («term_*_»
                («term|___|»
                 (group "|")
                 («term_-_»
                  (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
                  "-"
                  (Term.app `f [`x]))
                 (group)
                 "|")
                "*"
                (Term.app `bernstein [`n `k `x]))))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Mathlib.Tactic.tacticSimp_rw__
                  "simp_rw"
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `abs_mul)
                    ","
                    (Tactic.rwRule [] (Term.app `abs_eq_self.mpr [`bernstein_nonneg]))]
                   "]")
                  [])]))))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              («term_+_»
               (BigOperators.Algebra.BigOperators.Basic.finset.sum
                "∑"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `k) []))
                " in "
                `S
                ", "
                («term_*_»
                 («term|___|»
                  (group "|")
                  («term_-_»
                   (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
                   "-"
                   (Term.app `f [`x]))
                  (group)
                  "|")
                 "*"
                 (Term.app `bernstein [`n `k `x])))
               "+"
               (BigOperators.Algebra.BigOperators.Basic.finset.sum
                "∑"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `k) []))
                " in "
                (Order.Basic.«term_ᶜ» `S "ᶜ")
                ", "
                («term_*_»
                 («term|___|»
                  (group "|")
                  («term_-_»
                   (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
                   "-"
                   (Term.app `f [`x]))
                  (group)
                  "|")
                 "*"
                 (Term.app `bernstein [`n `k `x])))))
             ":="
             (Term.proj (Term.app `S.sum_add_sum_compl [(Term.hole "_")]) "." `symm))
            (calcStep
             («term_<_»
              (Term.hole "_")
              "<"
              («term_+_» («term_/_» `ε "/" (num "2")) "+" («term_/_» `ε "/" (num "2"))))
             ":="
             (Term.app `add_lt_add_of_le_of_lt [(Term.hole "_") (Term.hole "_")]))
            (calcStep («term_=_» (Term.hole "_") "=" `ε) ":=" (Term.app `add_halves [`ε]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(calcTactic
             "calc"
             (calcStep
              («term_≤_»
               (BigOperators.Algebra.BigOperators.Basic.finset.sum
                "∑"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `k) []))
                " in "
                `S
                ", "
                («term_*_»
                 («term|___|»
                  (group "|")
                  («term_-_»
                   (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
                   "-"
                   (Term.app `f [`x]))
                  (group)
                  "|")
                 "*"
                 (Term.app `bernstein [`n `k `x])))
               "≤"
               (BigOperators.Algebra.BigOperators.Basic.finset.sum
                "∑"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `k) []))
                " in "
                `S
                ", "
                («term_*_» («term_/_» `ε "/" (num "2")) "*" (Term.app `bernstein [`n `k `x]))))
              ":="
              (Term.app
               `Finset.sum_le_sum
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [`k `m]
                  []
                  "=>"
                  (Term.app
                   `mul_le_mul_of_nonneg_right
                   [(Term.app `le_of_lt [(Term.app `lt_of_mem_S [`m])]) `bernstein_nonneg])))]))
             [(calcStep
               («term_=_»
                (Term.hole "_")
                "="
                («term_*_»
                 («term_/_» `ε "/" (num "2"))
                 "*"
                 (BigOperators.Algebra.BigOperators.Basic.finset.sum
                  "∑"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder (Lean.binderIdent `k) []))
                  " in "
                  `S
                  ", "
                  (Term.app `bernstein [`n `k `x]))))
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.mul_sum)] "]")
                    [])]))))
              (calcStep
               («term_≤_»
                (Term.hole "_")
                "≤"
                («term_*_»
                 («term_/_» `ε "/" (num "2"))
                 "*"
                 (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
                  "∑"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder
                    (Lean.binderIdent `k)
                    [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]))
                  ", "
                  (Term.app `bernstein [`n `k `x]))))
               ":="
               (Term.app
                `mul_le_mul_of_nonneg_left
                [(Term.app
                  `Finset.sum_le_univ_sum_of_nonneg
                  [(Term.fun "fun" (Term.basicFun [`k] [] "=>" `bernstein_nonneg))])
                 (Term.app `le_of_lt [(Term.app `half_pos [`h])])]))
              (calcStep
               («term_=_» (Term.hole "_") "=" («term_/_» `ε "/" (num "2")))
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
                     [(Tactic.rwRule [] `bernstein.probability) "," (Tactic.rwRule [] `mul_one)]
                     "]")
                    [])]))))])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(calcTactic
             "calc"
             (calcStep
              («term_≤_»
               (BigOperators.Algebra.BigOperators.Basic.finset.sum
                "∑"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `k) []))
                " in "
                (Order.Basic.«term_ᶜ» `S "ᶜ")
                ", "
                («term_*_»
                 («term|___|»
                  (group "|")
                  («term_-_»
                   (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
                   "-"
                   (Term.app `f [`x]))
                  (group)
                  "|")
                 "*"
                 (Term.app `bernstein [`n `k `x])))
               "≤"
               (BigOperators.Algebra.BigOperators.Basic.finset.sum
                "∑"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `k) []))
                " in "
                (Order.Basic.«term_ᶜ» `S "ᶜ")
                ", "
                («term_*_»
                 («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
                 "*"
                 (Term.app `bernstein [`n `k `x]))))
              ":="
              (Term.app
               `Finset.sum_le_sum
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [`k `m]
                  []
                  "=>"
                  (Term.app
                   `mul_le_mul_of_nonneg_right
                   [(Term.app `f.dist_le_two_norm [(Term.hole "_") (Term.hole "_")])
                    `bernstein_nonneg])))]))
             [(calcStep
               («term_=_»
                (Term.hole "_")
                "="
                («term_*_»
                 («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
                 "*"
                 (BigOperators.Algebra.BigOperators.Basic.finset.sum
                  "∑"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder (Lean.binderIdent `k) []))
                  " in "
                  (Order.Basic.«term_ᶜ» `S "ᶜ")
                  ", "
                  (Term.app `bernstein [`n `k `x]))))
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.mul_sum)] "]")
                    [])]))))
              (calcStep
               («term_≤_»
                (Term.hole "_")
                "≤"
                («term_*_»
                 («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
                 "*"
                 (BigOperators.Algebra.BigOperators.Basic.finset.sum
                  "∑"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder (Lean.binderIdent `k) []))
                  " in "
                  (Order.Basic.«term_ᶜ» `S "ᶜ")
                  ", "
                  («term_*_»
                   («term_*_»
                    («term_^_»
                     `δ
                     "^"
                     (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")"))
                    "*"
                    («term_^_»
                     («term_-_» `x "-" (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
                     "^"
                     (num "2")))
                   "*"
                   (Term.app `bernstein [`n `k `x])))))
               ":="
               (Term.app
                `mul_le_mul_of_nonneg_left
                [(Term.app
                  `Finset.sum_le_sum
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [`k `m]
                     []
                     "=>"
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Mathlib.Tactic.Conv.convLHS
                          "conv_lhs"
                          []
                          []
                          "=>"
                          (Tactic.Conv.convSeq
                           (Tactic.Conv.convSeq1Indented
                            [(Tactic.Conv.convRw__
                              "rw"
                              []
                              (Tactic.rwRuleSeq
                               "["
                               [(Tactic.rwRule
                                 [(patternIgnore (token.«← » "←"))]
                                 (Term.app
                                  `one_mul
                                  [(Term.app
                                    `bernstein
                                    [(Term.hole "_") (Term.hole "_") (Term.hole "_")])]))]
                               "]"))])))
                         []
                         (Tactic.exact
                          "exact"
                          (Term.app
                           `mul_le_mul_of_nonneg_right
                           [(Term.app `le_of_mem_S_compl [`m]) `bernstein_nonneg]))])))))])
                 `w₁]))
              (calcStep
               («term_≤_»
                (Term.hole "_")
                "≤"
                («term_*_»
                 («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
                 "*"
                 (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
                  "∑"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder
                    (Lean.binderIdent `k)
                    [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]))
                  ", "
                  («term_*_»
                   («term_*_»
                    («term_^_»
                     `δ
                     "^"
                     (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")"))
                    "*"
                    («term_^_»
                     («term_-_» `x "-" (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
                     "^"
                     (num "2")))
                   "*"
                   (Term.app `bernstein [`n `k `x])))))
               ":="
               (Term.app
                `mul_le_mul_of_nonneg_left
                [(Term.app
                  `Finset.sum_le_univ_sum_of_nonneg
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [`k]
                     []
                     "=>"
                     (Term.app
                      `mul_nonneg
                      [(Term.app
                        `mul_nonneg
                        [`pow_minus_two_nonneg (Term.app `sq_nonneg [(Term.hole "_")])])
                       `bernstein_nonneg])))])
                 `w₁]))
              (calcStep
               («term_=_»
                (Term.hole "_")
                "="
                («term_*_»
                 («term_*_»
                  («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
                  "*"
                  («term_^_»
                   `δ
                   "^"
                   (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")")))
                 "*"
                 (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
                  "∑"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder
                    (Lean.binderIdent `k)
                    [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]))
                  ", "
                  («term_*_»
                   («term_^_»
                    («term_-_» `x "-" (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
                    "^"
                    (num "2"))
                   "*"
                   (Term.app `bernstein [`n `k `x])))))
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Mathlib.Tactic.Conv.convRHS
                    "conv_rhs"
                    []
                    []
                    "=>"
                    (Tactic.Conv.convSeq
                     (Tactic.Conv.convSeq1Indented
                      [(Tactic.Conv.convRw__
                        "rw"
                        []
                        (Tactic.rwRuleSeq
                         "["
                         [(Tactic.rwRule [] `mul_assoc) "," (Tactic.rwRule [] `Finset.mul_sum)]
                         "]"))
                       []
                       (Tactic.Conv.simp
                        "simp"
                        []
                        []
                        ["only"]
                        ["["
                         [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `mul_assoc)]
                         "]"])])))]))))
              (calcStep
               («term_=_»
                (Term.hole "_")
                "="
                («term_/_»
                 («term_*_»
                  («term_*_»
                   («term_*_»
                    («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
                    "*"
                    («term_^_»
                     `δ
                     "^"
                     (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")")))
                   "*"
                   `x)
                  "*"
                  («term_-_» (num "1") "-" `x))
                 "/"
                 `n))
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `variance [`npos]))] "]")
                    [])
                   []
                   (Mathlib.Tactic.RingNF.ring "ring")]))))
              (calcStep
               («term_≤_»
                (Term.hole "_")
                "≤"
                («term_/_»
                 («term_*_»
                  («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
                  "*"
                  («term_^_»
                   `δ
                   "^"
                   (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")")))
                 "/"
                 `n))
               ":="
               («term_<|_»
                (Term.proj (Term.app `div_le_div_right [`npos]) "." `mpr)
                "<|"
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.«tactic_<;>_»
                     (Tactic.refine'
                      "refine'"
                      (Term.app
                       `mul_le_of_le_of_le_one'
                       [(Term.app `mul_le_of_le_one_right [`w₂ (Term.hole "_")])
                        (Term.hole "_")
                        (Term.hole "_")
                        `w₂]))
                     "<;>"
                     (Tactic.unitInterval "unit_interval"))])))))
              (calcStep
               («term_<_» (Term.hole "_") "<" («term_/_» `ε "/" (num "2")))
               ":="
               `nh)])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(calcTactic
         "calc"
         (calcStep
          («term_≤_»
           (BigOperators.Algebra.BigOperators.Basic.finset.sum
            "∑"
            (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `k) []))
            " in "
            (Order.Basic.«term_ᶜ» `S "ᶜ")
            ", "
            («term_*_»
             («term|___|»
              (group "|")
              («term_-_»
               (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
               "-"
               (Term.app `f [`x]))
              (group)
              "|")
             "*"
             (Term.app `bernstein [`n `k `x])))
           "≤"
           (BigOperators.Algebra.BigOperators.Basic.finset.sum
            "∑"
            (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `k) []))
            " in "
            (Order.Basic.«term_ᶜ» `S "ᶜ")
            ", "
            («term_*_»
             («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
             "*"
             (Term.app `bernstein [`n `k `x]))))
          ":="
          (Term.app
           `Finset.sum_le_sum
           [(Term.fun
             "fun"
             (Term.basicFun
              [`k `m]
              []
              "=>"
              (Term.app
               `mul_le_mul_of_nonneg_right
               [(Term.app `f.dist_le_two_norm [(Term.hole "_") (Term.hole "_")])
                `bernstein_nonneg])))]))
         [(calcStep
           («term_=_»
            (Term.hole "_")
            "="
            («term_*_»
             («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
             "*"
             (BigOperators.Algebra.BigOperators.Basic.finset.sum
              "∑"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `k) []))
              " in "
              (Order.Basic.«term_ᶜ» `S "ᶜ")
              ", "
              (Term.app `bernstein [`n `k `x]))))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.mul_sum)] "]")
                [])]))))
          (calcStep
           («term_≤_»
            (Term.hole "_")
            "≤"
            («term_*_»
             («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
             "*"
             (BigOperators.Algebra.BigOperators.Basic.finset.sum
              "∑"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `k) []))
              " in "
              (Order.Basic.«term_ᶜ» `S "ᶜ")
              ", "
              («term_*_»
               («term_*_»
                («term_^_»
                 `δ
                 "^"
                 (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")"))
                "*"
                («term_^_»
                 («term_-_» `x "-" (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
                 "^"
                 (num "2")))
               "*"
               (Term.app `bernstein [`n `k `x])))))
           ":="
           (Term.app
            `mul_le_mul_of_nonneg_left
            [(Term.app
              `Finset.sum_le_sum
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`k `m]
                 []
                 "=>"
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Mathlib.Tactic.Conv.convLHS
                      "conv_lhs"
                      []
                      []
                      "=>"
                      (Tactic.Conv.convSeq
                       (Tactic.Conv.convSeq1Indented
                        [(Tactic.Conv.convRw__
                          "rw"
                          []
                          (Tactic.rwRuleSeq
                           "["
                           [(Tactic.rwRule
                             [(patternIgnore (token.«← » "←"))]
                             (Term.app
                              `one_mul
                              [(Term.app
                                `bernstein
                                [(Term.hole "_") (Term.hole "_") (Term.hole "_")])]))]
                           "]"))])))
                     []
                     (Tactic.exact
                      "exact"
                      (Term.app
                       `mul_le_mul_of_nonneg_right
                       [(Term.app `le_of_mem_S_compl [`m]) `bernstein_nonneg]))])))))])
             `w₁]))
          (calcStep
           («term_≤_»
            (Term.hole "_")
            "≤"
            («term_*_»
             («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
             "*"
             (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
              "∑"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder
                (Lean.binderIdent `k)
                [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]))
              ", "
              («term_*_»
               («term_*_»
                («term_^_»
                 `δ
                 "^"
                 (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")"))
                "*"
                («term_^_»
                 («term_-_» `x "-" (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
                 "^"
                 (num "2")))
               "*"
               (Term.app `bernstein [`n `k `x])))))
           ":="
           (Term.app
            `mul_le_mul_of_nonneg_left
            [(Term.app
              `Finset.sum_le_univ_sum_of_nonneg
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`k]
                 []
                 "=>"
                 (Term.app
                  `mul_nonneg
                  [(Term.app
                    `mul_nonneg
                    [`pow_minus_two_nonneg (Term.app `sq_nonneg [(Term.hole "_")])])
                   `bernstein_nonneg])))])
             `w₁]))
          (calcStep
           («term_=_»
            (Term.hole "_")
            "="
            («term_*_»
             («term_*_»
              («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
              "*"
              («term_^_»
               `δ
               "^"
               (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")")))
             "*"
             (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
              "∑"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder
                (Lean.binderIdent `k)
                [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]))
              ", "
              («term_*_»
               («term_^_»
                («term_-_» `x "-" (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
                "^"
                (num "2"))
               "*"
               (Term.app `bernstein [`n `k `x])))))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Mathlib.Tactic.Conv.convRHS
                "conv_rhs"
                []
                []
                "=>"
                (Tactic.Conv.convSeq
                 (Tactic.Conv.convSeq1Indented
                  [(Tactic.Conv.convRw__
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] `mul_assoc) "," (Tactic.rwRule [] `Finset.mul_sum)]
                     "]"))
                   []
                   (Tactic.Conv.simp
                    "simp"
                    []
                    []
                    ["only"]
                    ["["
                     [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `mul_assoc)]
                     "]"])])))]))))
          (calcStep
           («term_=_»
            (Term.hole "_")
            "="
            («term_/_»
             («term_*_»
              («term_*_»
               («term_*_»
                («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
                "*"
                («term_^_»
                 `δ
                 "^"
                 (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")")))
               "*"
               `x)
              "*"
              («term_-_» (num "1") "-" `x))
             "/"
             `n))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `variance [`npos]))] "]")
                [])
               []
               (Mathlib.Tactic.RingNF.ring "ring")]))))
          (calcStep
           («term_≤_»
            (Term.hole "_")
            "≤"
            («term_/_»
             («term_*_»
              («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
              "*"
              («term_^_»
               `δ
               "^"
               (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")")))
             "/"
             `n))
           ":="
           («term_<|_»
            (Term.proj (Term.app `div_le_div_right [`npos]) "." `mpr)
            "<|"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.«tactic_<;>_»
                 (Tactic.refine'
                  "refine'"
                  (Term.app
                   `mul_le_of_le_of_le_one'
                   [(Term.app `mul_le_of_le_one_right [`w₂ (Term.hole "_")])
                    (Term.hole "_")
                    (Term.hole "_")
                    `w₂]))
                 "<;>"
                 (Tactic.unitInterval "unit_interval"))])))))
          (calcStep («term_<_» (Term.hole "_") "<" («term_/_» `ε "/" (num "2"))) ":=" `nh)])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_≤_»
         (BigOperators.Algebra.BigOperators.Basic.finset.sum
          "∑"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `k) []))
          " in "
          (Order.Basic.«term_ᶜ» `S "ᶜ")
          ", "
          («term_*_»
           («term|___|»
            (group "|")
            («term_-_»
             (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
             "-"
             (Term.app `f [`x]))
            (group)
            "|")
           "*"
           (Term.app `bernstein [`n `k `x])))
         "≤"
         (BigOperators.Algebra.BigOperators.Basic.finset.sum
          "∑"
          (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `k) []))
          " in "
          (Order.Basic.«term_ᶜ» `S "ᶜ")
          ", "
          («term_*_»
           («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
           "*"
           (Term.app `bernstein [`n `k `x]))))
        ":="
        (Term.app
         `Finset.sum_le_sum
         [(Term.fun
           "fun"
           (Term.basicFun
            [`k `m]
            []
            "=>"
            (Term.app
             `mul_le_mul_of_nonneg_right
             [(Term.app `f.dist_le_two_norm [(Term.hole "_") (Term.hole "_")])
              `bernstein_nonneg])))]))
       [(calcStep
         («term_=_»
          (Term.hole "_")
          "="
          («term_*_»
           («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
           "*"
           (BigOperators.Algebra.BigOperators.Basic.finset.sum
            "∑"
            (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `k) []))
            " in "
            (Order.Basic.«term_ᶜ» `S "ᶜ")
            ", "
            (Term.app `bernstein [`n `k `x]))))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.mul_sum)] "]")
              [])]))))
        (calcStep
         («term_≤_»
          (Term.hole "_")
          "≤"
          («term_*_»
           («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
           "*"
           (BigOperators.Algebra.BigOperators.Basic.finset.sum
            "∑"
            (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `k) []))
            " in "
            (Order.Basic.«term_ᶜ» `S "ᶜ")
            ", "
            («term_*_»
             («term_*_»
              («term_^_»
               `δ
               "^"
               (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")"))
              "*"
              («term_^_»
               («term_-_» `x "-" (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
               "^"
               (num "2")))
             "*"
             (Term.app `bernstein [`n `k `x])))))
         ":="
         (Term.app
          `mul_le_mul_of_nonneg_left
          [(Term.app
            `Finset.sum_le_sum
            [(Term.fun
              "fun"
              (Term.basicFun
               [`k `m]
               []
               "=>"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Mathlib.Tactic.Conv.convLHS
                    "conv_lhs"
                    []
                    []
                    "=>"
                    (Tactic.Conv.convSeq
                     (Tactic.Conv.convSeq1Indented
                      [(Tactic.Conv.convRw__
                        "rw"
                        []
                        (Tactic.rwRuleSeq
                         "["
                         [(Tactic.rwRule
                           [(patternIgnore (token.«← » "←"))]
                           (Term.app
                            `one_mul
                            [(Term.app
                              `bernstein
                              [(Term.hole "_") (Term.hole "_") (Term.hole "_")])]))]
                         "]"))])))
                   []
                   (Tactic.exact
                    "exact"
                    (Term.app
                     `mul_le_mul_of_nonneg_right
                     [(Term.app `le_of_mem_S_compl [`m]) `bernstein_nonneg]))])))))])
           `w₁]))
        (calcStep
         («term_≤_»
          (Term.hole "_")
          "≤"
          («term_*_»
           («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
           "*"
           (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
            "∑"
            (Std.ExtendedBinder.extBinders
             (Std.ExtendedBinder.extBinder
              (Lean.binderIdent `k)
              [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]))
            ", "
            («term_*_»
             («term_*_»
              («term_^_»
               `δ
               "^"
               (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")"))
              "*"
              («term_^_»
               («term_-_» `x "-" (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
               "^"
               (num "2")))
             "*"
             (Term.app `bernstein [`n `k `x])))))
         ":="
         (Term.app
          `mul_le_mul_of_nonneg_left
          [(Term.app
            `Finset.sum_le_univ_sum_of_nonneg
            [(Term.fun
              "fun"
              (Term.basicFun
               [`k]
               []
               "=>"
               (Term.app
                `mul_nonneg
                [(Term.app
                  `mul_nonneg
                  [`pow_minus_two_nonneg (Term.app `sq_nonneg [(Term.hole "_")])])
                 `bernstein_nonneg])))])
           `w₁]))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          («term_*_»
           («term_*_»
            («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
            "*"
            («term_^_»
             `δ
             "^"
             (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")")))
           "*"
           (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
            "∑"
            (Std.ExtendedBinder.extBinders
             (Std.ExtendedBinder.extBinder
              (Lean.binderIdent `k)
              [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]))
            ", "
            («term_*_»
             («term_^_»
              («term_-_» `x "-" (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
              "^"
              (num "2"))
             "*"
             (Term.app `bernstein [`n `k `x])))))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Mathlib.Tactic.Conv.convRHS
              "conv_rhs"
              []
              []
              "=>"
              (Tactic.Conv.convSeq
               (Tactic.Conv.convSeq1Indented
                [(Tactic.Conv.convRw__
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `mul_assoc) "," (Tactic.rwRule [] `Finset.mul_sum)]
                   "]"))
                 []
                 (Tactic.Conv.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `mul_assoc)]
                   "]"])])))]))))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          («term_/_»
           («term_*_»
            («term_*_»
             («term_*_»
              («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
              "*"
              («term_^_»
               `δ
               "^"
               (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")")))
             "*"
             `x)
            "*"
            («term_-_» (num "1") "-" `x))
           "/"
           `n))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `variance [`npos]))] "]")
              [])
             []
             (Mathlib.Tactic.RingNF.ring "ring")]))))
        (calcStep
         («term_≤_»
          (Term.hole "_")
          "≤"
          («term_/_»
           («term_*_»
            («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
            "*"
            («term_^_»
             `δ
             "^"
             (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")")))
           "/"
           `n))
         ":="
         («term_<|_»
          (Term.proj (Term.app `div_le_div_right [`npos]) "." `mpr)
          "<|"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.«tactic_<;>_»
               (Tactic.refine'
                "refine'"
                (Term.app
                 `mul_le_of_le_of_le_one'
                 [(Term.app `mul_le_of_le_one_right [`w₂ (Term.hole "_")])
                  (Term.hole "_")
                  (Term.hole "_")
                  `w₂]))
               "<;>"
               (Tactic.unitInterval "unit_interval"))])))))
        (calcStep («term_<_» (Term.hole "_") "<" («term_/_» `ε "/" (num "2"))) ":=" `nh)])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nh
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» (Term.hole "_") "<" («term_/_» `ε "/" (num "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_» `ε "/" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      («term_<|_»
       (Term.proj (Term.app `div_le_div_right [`npos]) "." `mpr)
       "<|"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Tactic.refine'
             "refine'"
             (Term.app
              `mul_le_of_le_of_le_one'
              [(Term.app `mul_le_of_le_one_right [`w₂ (Term.hole "_")])
               (Term.hole "_")
               (Term.hole "_")
               `w₂]))
            "<;>"
            (Tactic.unitInterval "unit_interval"))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Tactic.refine'
            "refine'"
            (Term.app
             `mul_le_of_le_of_le_one'
             [(Term.app `mul_le_of_le_one_right [`w₂ (Term.hole "_")])
              (Term.hole "_")
              (Term.hole "_")
              `w₂]))
           "<;>"
           (Tactic.unitInterval "unit_interval"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Tactic.refine'
        "refine'"
        (Term.app
         `mul_le_of_le_of_le_one'
         [(Term.app `mul_le_of_le_one_right [`w₂ (Term.hole "_")])
          (Term.hole "_")
          (Term.hole "_")
          `w₂]))
       "<;>"
       (Tactic.unitInterval "unit_interval"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.unitInterval "unit_interval")
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.refine'
       "refine'"
       (Term.app
        `mul_le_of_le_of_le_one'
        [(Term.app `mul_le_of_le_one_right [`w₂ (Term.hole "_")])
         (Term.hole "_")
         (Term.hole "_")
         `w₂]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mul_le_of_le_of_le_one'
       [(Term.app `mul_le_of_le_one_right [`w₂ (Term.hole "_")])
        (Term.hole "_")
        (Term.hole "_")
        `w₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `w₂
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app `mul_le_of_le_one_right [`w₂ (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `w₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_le_of_le_one_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `mul_le_of_le_one_right [`w₂ (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_le_of_le_of_le_one'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj (Term.app `div_le_div_right [`npos]) "." `mpr)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `div_le_div_right [`npos])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `npos
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `div_le_div_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `div_le_div_right [`npos])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Term.hole "_")
       "≤"
       («term_/_»
        («term_*_»
         («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
         "*"
         («term_^_»
          `δ
          "^"
          (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")")))
        "/"
        `n))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_»
       («term_*_»
        («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
        "*"
        («term_^_» `δ "^" (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")")))
       "/"
       `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_*_»
       («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
       "*"
       («term_^_» `δ "^" (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `δ "^" (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℤ "ℤ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `δ
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
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
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `variance [`npos]))] "]")
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
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `variance [`npos]))] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `variance [`npos])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `npos
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `variance
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       («term_/_»
        («term_*_»
         («term_*_»
          («term_*_»
           («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
           "*"
           («term_^_»
            `δ
            "^"
            (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")")))
          "*"
          `x)
         "*"
         («term_-_» (num "1") "-" `x))
        "/"
        `n))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_/_»
       («term_*_»
        («term_*_»
         («term_*_»
          («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
          "*"
          («term_^_»
           `δ
           "^"
           (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")")))
         "*"
         `x)
        "*"
        («term_-_» (num "1") "-" `x))
       "/"
       `n)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `n
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_*_»
       («term_*_»
        («term_*_»
         («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
         "*"
         («term_^_»
          `δ
          "^"
          (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")")))
        "*"
        `x)
       "*"
       («term_-_» (num "1") "-" `x))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» (num "1") "-" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_-_» (num "1") "-" `x) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_*_»
       («term_*_»
        («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
        "*"
        («term_^_» `δ "^" (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")")))
       "*"
       `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_*_»
       («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
       "*"
       («term_^_» `δ "^" (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `δ "^" (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℤ "ℤ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `δ
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Mathlib.Tactic.Conv.convRHS
           "conv_rhs"
           []
           []
           "=>"
           (Tactic.Conv.convSeq
            (Tactic.Conv.convSeq1Indented
             [(Tactic.Conv.convRw__
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `mul_assoc) "," (Tactic.rwRule [] `Finset.mul_sum)]
                "]"))
              []
              (Tactic.Conv.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `mul_assoc)]
                "]"])])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.Conv.convRHS
       "conv_rhs"
       []
       []
       "=>"
       (Tactic.Conv.convSeq
        (Tactic.Conv.convSeq1Indented
         [(Tactic.Conv.convRw__
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `mul_assoc) "," (Tactic.rwRule [] `Finset.mul_sum)]
            "]"))
          []
          (Tactic.Conv.simp
           "simp"
           []
           []
           ["only"]
           ["[" [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `mul_assoc)] "]"])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convSeq1Indented', expected 'Lean.Parser.Tactic.Conv.convSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Finset.mul_sum
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       («term_*_»
        («term_*_»
         («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
         "*"
         («term_^_»
          `δ
          "^"
          (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")")))
        "*"
        (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
         "∑"
         (Std.ExtendedBinder.extBinders
          (Std.ExtendedBinder.extBinder
           (Lean.binderIdent `k)
           [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]))
         ", "
         («term_*_»
          («term_^_»
           («term_-_» `x "-" (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
           "^"
           (num "2"))
          "*"
          (Term.app `bernstein [`n `k `x])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_*_»
        («term_*_» (num "2") "*" (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `f "‖"))
        "*"
        («term_^_» `δ "^" (Term.typeAscription "(" («term-_» "-" (num "2")) ":" [(termℤ "ℤ")] ")")))
       "*"
       (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
        "∑"
        (Std.ExtendedBinder.extBinders
         (Std.ExtendedBinder.extBinder
          (Lean.binderIdent `k)
          [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]))
        ", "
        («term_*_»
         («term_^_»
          («term_-_» `x "-" (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
          "^"
          (num "2"))
         "*"
         (Term.app `bernstein [`n `k `x]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (BigOperators.Algebra.BigOperators.Basic.finset.sum_univ
       "∑"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder
         (Lean.binderIdent `k)
         [(group ":" (Term.app `Fin [(«term_+_» `n "+" (num "1"))]))]))
       ", "
       («term_*_»
        («term_^_»
         («term_-_» `x "-" (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
         "^"
         (num "2"))
        "*"
        (Term.app `bernstein [`n `k `x])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_^_»
        («term_-_» `x "-" (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
        "^"
        (num "2"))
       "*"
       (Term.app `bernstein [`n `k `x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `bernstein [`n `k `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `bernstein
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_^_»
       («term_-_» `x "-" (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
       "^"
       (num "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "2")
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      («term_-_» `x "-" (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.SpecialFunctions.Bernstein.«term_/ₙ»', expected 'Analysis.SpecialFunctions.Bernstein.term_/ₙ._@.Analysis.SpecialFunctions.Bernstein._hyg.502'
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
    The Bernstein approximations
    ```
    ∑ k : fin (n+1), f (k/n : ℝ) * n.choose k * x^k * (1-x)^(n-k)
    ```
    for a continuous function `f : C([0,1], ℝ)` converge uniformly to `f` as `n` tends to infinity.
    
    This is the proof given in [Richard Beals' *Analysis, an introduction*][beals-analysis], §7D,
    and reproduced on wikipedia.
    -/
  theorem
    bernstein_approximation_uniform
    ( f : C( I , ℝ ) ) : Tendsto fun n : ℕ => bernsteinApproximation n f atTop 𝓝 f
    :=
      by
        simp only [ metric.nhds_basis_ball.tendsto_right_iff , Metric.mem_ball , dist_eq_norm ]
          intro ε h
          let δ := δ f ε h
          have nhds_zero := tendsto_const_div_at_top_nhds_0_nat 2 * ‖ f ‖ * δ ^ ( - 2 : ℤ )
          filter_upwards
            [ nhds_zero.eventually gt_mem_nhds half_pos h , eventually_gt_at_top 0 ]
            with n nh npos'
          have npos : 0 < ( n : ℝ ) := by exact_mod_cast npos'
          have w₁ : 0 ≤ 2 * ‖ f ‖ := mul_nonneg by norm_num norm_nonneg f
          have w₂ : 0 ≤ 2 * ‖ f ‖ * δ ^ ( - 2 : ℤ ) := mul_nonneg w₁ pow_minus_two_nonneg
          rw [ ContinuousMap.norm_lt_iff _ h ]
          intro x
          let S := S f ε h n x
          calc
            | bernsteinApproximation n f - f x | = | bernsteinApproximation n f x - f x | := rfl
            _ = | bernsteinApproximation n f x - f x * 1 | := by rw [ mul_one ]
              _ = | bernsteinApproximation n f x - f x * ∑ k : Fin n + 1 , bernstein n k x |
                :=
                by rw [ bernstein.probability ]
              _ = | ∑ k : Fin n + 1 , f k /ₙ - f x * bernstein n k x |
                :=
                by simp [ bernsteinApproximation , Finset.mul_sum , sub_mul ]
              _ ≤ ∑ k : Fin n + 1 , | f k /ₙ - f x * bernstein n k x |
                :=
                Finset.abs_sum_le_sum_abs _ _
              _ = ∑ k : Fin n + 1 , | f k /ₙ - f x | * bernstein n k x
                :=
                by simp_rw [ abs_mul , abs_eq_self.mpr bernstein_nonneg ]
              _
                  =
                  ∑ k in S , | f k /ₙ - f x | * bernstein n k x
                    +
                    ∑ k in S ᶜ , | f k /ₙ - f x | * bernstein n k x
                :=
                S.sum_add_sum_compl _ . symm
              _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt _ _
              _ = ε := add_halves ε
          ·
            calc
              ∑ k in S , | f k /ₙ - f x | * bernstein n k x ≤ ∑ k in S , ε / 2 * bernstein n k x
                :=
                Finset.sum_le_sum
                  fun k m => mul_le_mul_of_nonneg_right le_of_lt lt_of_mem_S m bernstein_nonneg
              _ = ε / 2 * ∑ k in S , bernstein n k x := by rw [ Finset.mul_sum ]
                _ ≤ ε / 2 * ∑ k : Fin n + 1 , bernstein n k x
                  :=
                  mul_le_mul_of_nonneg_left
                    Finset.sum_le_univ_sum_of_nonneg fun k => bernstein_nonneg le_of_lt half_pos h
                _ = ε / 2 := by rw [ bernstein.probability , mul_one ]
          ·
            calc
              ∑ k in S ᶜ , | f k /ₙ - f x | * bernstein n k x
                  ≤
                  ∑ k in S ᶜ , 2 * ‖ f ‖ * bernstein n k x
                :=
                Finset.sum_le_sum
                  fun k m => mul_le_mul_of_nonneg_right f.dist_le_two_norm _ _ bernstein_nonneg
              _ = 2 * ‖ f ‖ * ∑ k in S ᶜ , bernstein n k x := by rw [ Finset.mul_sum ]
                _ ≤ 2 * ‖ f ‖ * ∑ k in S ᶜ , δ ^ ( - 2 : ℤ ) * x - k /ₙ ^ 2 * bernstein n k x
                  :=
                  mul_le_mul_of_nonneg_left
                    Finset.sum_le_sum
                        fun
                          k m
                            =>
                            by
                              conv_lhs => rw [ ← one_mul bernstein _ _ _ ]
                                exact
                                  mul_le_mul_of_nonneg_right le_of_mem_S_compl m bernstein_nonneg
                      w₁
                _ ≤ 2 * ‖ f ‖ * ∑ k : Fin n + 1 , δ ^ ( - 2 : ℤ ) * x - k /ₙ ^ 2 * bernstein n k x
                  :=
                  mul_le_mul_of_nonneg_left
                    Finset.sum_le_univ_sum_of_nonneg
                        fun
                          k
                            =>
                            mul_nonneg mul_nonneg pow_minus_two_nonneg sq_nonneg _ bernstein_nonneg
                      w₁
                _ = 2 * ‖ f ‖ * δ ^ ( - 2 : ℤ ) * ∑ k : Fin n + 1 , x - k /ₙ ^ 2 * bernstein n k x
                  :=
                  by conv_rhs => rw [ mul_assoc , Finset.mul_sum ] simp only [ ← mul_assoc ]
                _ = 2 * ‖ f ‖ * δ ^ ( - 2 : ℤ ) * x * 1 - x / n := by rw [ variance npos ] ring
                _ ≤ 2 * ‖ f ‖ * δ ^ ( - 2 : ℤ ) / n
                  :=
                  div_le_div_right npos . mpr
                    <|
                    by
                      refine' mul_le_of_le_of_le_one' mul_le_of_le_one_right w₂ _ _ _ w₂
                        <;>
                        unit_interval
                _ < ε / 2 := nh
#align bernstein_approximation_uniform bernstein_approximation_uniform

