import Mathbin.RingTheory.Polynomial.Bernstein
import Mathbin.Topology.ContinuousFunction.Polynomial

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

open_locale Classical

open_locale BigOperators

open_locale BoundedContinuousFunction

open_locale UnitInterval

/-- 
The Bernstein polynomials, as continuous functions on `[0,1]`.
-/
def bernstein (n ν : ℕ) : C(I, ℝ) :=
  (bernsteinPolynomial ℝ n ν).toContinuousMapOn I

@[simp]
theorem bernstein_apply (n ν : ℕ) (x : I) : bernstein n ν x = (n.choose ν*x^ν)*1 - x^n - ν := by
  dsimp [bernstein, Polynomial.toContinuousMapOn, Polynomial.toContinuousMap, bernsteinPolynomial]
  simp

theorem bernstein_nonneg {n ν : ℕ} {x : I} : 0 ≤ bernstein n ν x := by
  simp only [bernstein_apply]
  exact
    mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _)
        (pow_nonneg
          (by
            unit_interval)
          _))
      (pow_nonneg
        (by
          unit_interval)
        _)

/-!
We now give a slight reformulation of `bernstein_polynomial.variance`.
-/


namespace bernstein

/-- 
Send `k : fin (n+1)` to the equally spaced points `k/n` in the unit interval.
-/
def z {n : ℕ} (k : Finₓ (n+1)) : I :=
  ⟨(k : ℝ) / n, by
    cases n
    ·
      norm_num
    ·
      have h₁ : 0 < (n.succ : ℝ) := by
        exact_mod_cast Nat.succ_posₓ _
      have h₂ : ↑k ≤ n.succ := by
        exact_mod_cast Finₓ.le_last k
      rw [Set.mem_Icc, le_div_iff h₁, div_le_iff h₁]
      norm_cast
      simp [h₂]⟩

local postfix:90 "/ₙ" => z

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `probability [])
  (Command.declSig
   [(Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")
    (Term.explicitBinder "(" [`x] [":" (Topology.UnitInterval.termI "I")] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Algebra.BigOperators.Basic.«term∑_,_»
      "∑"
      (Lean.explicitBinders
       (Lean.unbracketedExplicitBinders
        [(Lean.binderIdent `k)]
        [":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])]))
      ", "
      (Term.app `bernstein [`n `k `x]))
     "="
     (numLit "1"))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl [] [] ":=" (Term.app `bernsteinPolynomial.sum [(Data.Real.Basic.termℝ "ℝ") `n]))))
        [])
       (group
        (Tactic.applyFun
         "apply_fun"
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`p] [])]
           "=>"
           (Term.app
            `Polynomial.aeval
            [(Term.paren "(" [`x [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")") `p])))
         [(Tactic.location "at" (Tactic.locationHyp [`this] []))]
         [])
        [])
       (group
        (Tactic.simp
         "simp"
         []
         []
         ["[" [(Tactic.simpLemma [] [] `AlgHom.map_sum) "," (Tactic.simpLemma [] [] `Finset.sum_range)] "]"]
         [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
        [])
       (group (Tactic.exact "exact" `this) [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl [] [] ":=" (Term.app `bernsteinPolynomial.sum [(Data.Real.Basic.termℝ "ℝ") `n]))))
       [])
      (group
       (Tactic.applyFun
        "apply_fun"
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`p] [])]
          "=>"
          (Term.app
           `Polynomial.aeval
           [(Term.paren "(" [`x [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")") `p])))
        [(Tactic.location "at" (Tactic.locationHyp [`this] []))]
        [])
       [])
      (group
       (Tactic.simp
        "simp"
        []
        []
        ["[" [(Tactic.simpLemma [] [] `AlgHom.map_sum) "," (Tactic.simpLemma [] [] `Finset.sum_range)] "]"]
        [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
       [])
      (group (Tactic.exact "exact" `this) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" `this)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   []
   []
   ["[" [(Tactic.simpLemma [] [] `AlgHom.map_sum) "," (Tactic.simpLemma [] [] `Finset.sum_range)] "]"]
   [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.location', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.sum_range
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `AlgHom.map_sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.applyFun
   "apply_fun"
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`p] [])]
     "=>"
     (Term.app
      `Polynomial.aeval
      [(Term.paren "(" [`x [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")") `p])))
   [(Tactic.location "at" (Tactic.locationHyp [`this] []))]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.applyFun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.location', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`p] [])]
    "=>"
    (Term.app
     `Polynomial.aeval
     [(Term.paren "(" [`x [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")") `p])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Polynomial.aeval [(Term.paren "(" [`x [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")") `p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.paren "(" [`x [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Polynomial.aeval
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `bernsteinPolynomial.sum [(Data.Real.Basic.termℝ "ℝ") `n]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `bernsteinPolynomial.sum [(Data.Real.Basic.termℝ "ℝ") `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `bernsteinPolynomial.sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Algebra.BigOperators.Basic.«term∑_,_»
    "∑"
    (Lean.explicitBinders
     (Lean.unbracketedExplicitBinders
      [(Lean.binderIdent `k)]
      [":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])]))
    ", "
    (Term.app `bernstein [`n `k `x]))
   "="
   (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Algebra.BigOperators.Basic.«term∑_,_»
   "∑"
   (Lean.explicitBinders
    (Lean.unbracketedExplicitBinders
     [(Lean.binderIdent `k)]
     [":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])]))
   ", "
   (Term.app `bernstein [`n `k `x]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `bernstein [`n `k `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `bernstein
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  probability
  ( n : ℕ ) ( x : I ) : ∑ k : Finₓ n + 1 , bernstein n k x = 1
  :=
    by
      have := bernsteinPolynomial.sum ℝ n
        apply_fun fun p => Polynomial.aeval ( x : ℝ ) p at this
        simp [ AlgHom.map_sum , Finset.sum_range ] at this
        exact this

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
      («term_<_» (numLit "0") "<" (Term.paren "(" [`n [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")"))]
     []
     ")")
    (Term.explicitBinder "(" [`x] [":" (Topology.UnitInterval.termI "I")] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Algebra.BigOperators.Basic.«term∑_,_»
      "∑"
      (Lean.explicitBinders
       (Lean.unbracketedExplicitBinders
        [(Lean.binderIdent `k)]
        [":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])]))
      ", "
      (Finset.Data.Finset.Fold.«term_*_»
       (Cardinal.SetTheory.Cardinal.«term_^_»
        (Term.paren
         "("
         [(«term_-_» `x "-" (bernstein.Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
          [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]]
         ")")
        "^"
        (numLit "2"))
       "*"
       (Term.app `bernstein [`n `k `x])))
     "="
     («term_/_» (Finset.Data.Finset.Fold.«term_*_» `x "*" («term_-_» (numLit "1") "-" `x)) "/" `n))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`h' []]
           [(Term.typeSpec
             ":"
             («term_≠_»
              (Term.paren "(" [`n [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
              "≠"
              (numLit "0")))]
           ":="
           (Term.app `ne_of_gtₓ [`h]))))
        [])
       (group
        (Tactic.applyFun
         "apply_fun"
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`x] [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))])]
           "=>"
           (Finset.Data.Finset.Fold.«term_*_» `x "*" `n)))
         []
         ["using" (Term.app `GroupWithZeroₓ.mul_right_injective [`h'])])
        [])
       (group
        (Tactic.applyFun
         "apply_fun"
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`x] [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))])]
           "=>"
           (Finset.Data.Finset.Fold.«term_*_» `x "*" `n)))
         []
         ["using" (Term.app `GroupWithZeroₓ.mul_right_injective [`h'])])
        [])
       (group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
       (group
        (Mathlib.Tactic.Conv.convLHS
         "conv_lhs"
         []
         []
         "=>"
         (Tactic.Conv.convSeq
          (Tactic.Conv.convSeq1Indented
           [(group
             (Tactic.Conv.simp
              "simp"
              []
              ["only"]
              ["[" [(Tactic.simpLemma [] [] `Finset.sum_mul) "," (Tactic.simpLemma [] [] `z)] "]"]
              [])
             [])])))
        [])
       (group
        (Mathlib.Tactic.Conv.convRHS
         "conv_rhs"
         []
         []
         "=>"
         (Tactic.Conv.convSeq
          (Tactic.Conv.convSeq1Indented
           [(group
             (Tactic.Conv.convRw__
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `div_mul_cancel [(Term.hole "_") `h']))] "]"))
             [])])))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl [] [] ":=" (Term.app `bernsteinPolynomial.variance [(Data.Real.Basic.termℝ "ℝ") `n]))))
        [])
       (group
        (Tactic.applyFun
         "apply_fun"
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`p] [])]
           "=>"
           (Term.app
            `Polynomial.aeval
            [(Term.paren "(" [`x [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")") `p])))
         [(Tactic.location "at" (Tactic.locationHyp [`this] []))]
         [])
        [])
       (group
        (Tactic.simp
         "simp"
         []
         []
         ["["
          [(Tactic.simpLemma [] [] `AlgHom.map_sum)
           ","
           (Tactic.simpLemma [] [] `Finset.sum_range)
           ","
           (Tactic.simpLemma [] ["←"] `Polynomial.nat_cast_mul)]
          "]"]
         [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
        [])
       (group (Tactic.convert "convert" [] `this ["using" (numLit "1")]) [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.congr "congr" [(numLit "1")] []) [])
            (group (tacticFunext__ "funext" [`k]) [])
            (group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 []
                 (Term.app
                  `mul_commₓ
                  [(Term.hole "_") (Term.paren "(" [`n [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")]))
                ","
                (Tactic.rwRule
                 []
                 (Term.app
                  `mul_commₓ
                  [(Term.hole "_") (Term.paren "(" [`n [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")]))
                ","
                (Tactic.rwRule ["←"] `mul_assocₓ)
                ","
                (Tactic.rwRule ["←"] `mul_assocₓ)]
               "]")
              [])
             [])
            (group (Tactic.congr "congr" [(numLit "1")] []) [])
            (group (Tactic.fieldSimp "field_simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] [] []) [])
            (group (Tactic.Ring.tacticRing "ring") [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.Ring.tacticRing "ring") [])])))
        [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`h' []]
          [(Term.typeSpec
            ":"
            («term_≠_»
             (Term.paren "(" [`n [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
             "≠"
             (numLit "0")))]
          ":="
          (Term.app `ne_of_gtₓ [`h]))))
       [])
      (group
       (Tactic.applyFun
        "apply_fun"
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`x] [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))])]
          "=>"
          (Finset.Data.Finset.Fold.«term_*_» `x "*" `n)))
        []
        ["using" (Term.app `GroupWithZeroₓ.mul_right_injective [`h'])])
       [])
      (group
       (Tactic.applyFun
        "apply_fun"
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`x] [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))])]
          "=>"
          (Finset.Data.Finset.Fold.«term_*_» `x "*" `n)))
        []
        ["using" (Term.app `GroupWithZeroₓ.mul_right_injective [`h'])])
       [])
      (group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
      (group
       (Mathlib.Tactic.Conv.convLHS
        "conv_lhs"
        []
        []
        "=>"
        (Tactic.Conv.convSeq
         (Tactic.Conv.convSeq1Indented
          [(group
            (Tactic.Conv.simp
             "simp"
             []
             ["only"]
             ["[" [(Tactic.simpLemma [] [] `Finset.sum_mul) "," (Tactic.simpLemma [] [] `z)] "]"]
             [])
            [])])))
       [])
      (group
       (Mathlib.Tactic.Conv.convRHS
        "conv_rhs"
        []
        []
        "=>"
        (Tactic.Conv.convSeq
         (Tactic.Conv.convSeq1Indented
          [(group
            (Tactic.Conv.convRw__
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `div_mul_cancel [(Term.hole "_") `h']))] "]"))
            [])])))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl [] [] ":=" (Term.app `bernsteinPolynomial.variance [(Data.Real.Basic.termℝ "ℝ") `n]))))
       [])
      (group
       (Tactic.applyFun
        "apply_fun"
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`p] [])]
          "=>"
          (Term.app
           `Polynomial.aeval
           [(Term.paren "(" [`x [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")") `p])))
        [(Tactic.location "at" (Tactic.locationHyp [`this] []))]
        [])
       [])
      (group
       (Tactic.simp
        "simp"
        []
        []
        ["["
         [(Tactic.simpLemma [] [] `AlgHom.map_sum)
          ","
          (Tactic.simpLemma [] [] `Finset.sum_range)
          ","
          (Tactic.simpLemma [] ["←"] `Polynomial.nat_cast_mul)]
         "]"]
        [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
       [])
      (group (Tactic.convert "convert" [] `this ["using" (numLit "1")]) [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.congr "congr" [(numLit "1")] []) [])
           (group (tacticFunext__ "funext" [`k]) [])
           (group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                []
                (Term.app
                 `mul_commₓ
                 [(Term.hole "_") (Term.paren "(" [`n [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")]))
               ","
               (Tactic.rwRule
                []
                (Term.app
                 `mul_commₓ
                 [(Term.hole "_") (Term.paren "(" [`n [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")]))
               ","
               (Tactic.rwRule ["←"] `mul_assocₓ)
               ","
               (Tactic.rwRule ["←"] `mul_assocₓ)]
              "]")
             [])
            [])
           (group (Tactic.congr "congr" [(numLit "1")] []) [])
           (group (Tactic.fieldSimp "field_simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] [] []) [])
           (group (Tactic.Ring.tacticRing "ring") [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.Ring.tacticRing "ring") [])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic·._» "·" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.Ring.tacticRing "ring") [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.Ring.tacticRing "ring")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Ring.tacticRing', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.congr "congr" [(numLit "1")] []) [])
      (group (tacticFunext__ "funext" [`k]) [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule
           []
           (Term.app
            `mul_commₓ
            [(Term.hole "_") (Term.paren "(" [`n [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")]))
          ","
          (Tactic.rwRule
           []
           (Term.app
            `mul_commₓ
            [(Term.hole "_") (Term.paren "(" [`n [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")]))
          ","
          (Tactic.rwRule ["←"] `mul_assocₓ)
          ","
          (Tactic.rwRule ["←"] `mul_assocₓ)]
         "]")
        [])
       [])
      (group (Tactic.congr "congr" [(numLit "1")] []) [])
      (group (Tactic.fieldSimp "field_simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] [] []) [])
      (group (Tactic.Ring.tacticRing "ring") [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.Ring.tacticRing "ring")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Ring.tacticRing', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
  (Tactic.fieldSimp "field_simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.fieldSimp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.congr "congr" [(numLit "1")] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.congr', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule
      []
      (Term.app
       `mul_commₓ
       [(Term.hole "_") (Term.paren "(" [`n [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")]))
     ","
     (Tactic.rwRule
      []
      (Term.app
       `mul_commₓ
       [(Term.hole "_") (Term.paren "(" [`n [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")]))
     ","
     (Tactic.rwRule ["←"] `mul_assocₓ)
     ","
     (Tactic.rwRule ["←"] `mul_assocₓ)]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mul_assocₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mul_assocₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `mul_commₓ
   [(Term.hole "_") (Term.paren "(" [`n [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren "(" [`n [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mul_commₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `mul_commₓ
   [(Term.hole "_") (Term.paren "(" [`n [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren "(" [`n [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mul_commₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (tacticFunext__ "funext" [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticFunext__', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.congr "congr" [(numLit "1")] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.congr', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.convert "convert" [] `this ["using" (numLit "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.convert', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   []
   []
   ["["
    [(Tactic.simpLemma [] [] `AlgHom.map_sum)
     ","
     (Tactic.simpLemma [] [] `Finset.sum_range)
     ","
     (Tactic.simpLemma [] ["←"] `Polynomial.nat_cast_mul)]
    "]"]
   [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.location', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Polynomial.nat_cast_mul
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.sum_range
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `AlgHom.map_sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.applyFun
   "apply_fun"
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`p] [])]
     "=>"
     (Term.app
      `Polynomial.aeval
      [(Term.paren "(" [`x [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")") `p])))
   [(Tactic.location "at" (Tactic.locationHyp [`this] []))]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.applyFun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.location', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`p] [])]
    "=>"
    (Term.app
     `Polynomial.aeval
     [(Term.paren "(" [`x [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")") `p])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Polynomial.aeval [(Term.paren "(" [`x [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")") `p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.paren "(" [`x [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Polynomial.aeval
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl [] [] ":=" (Term.app `bernsteinPolynomial.variance [(Data.Real.Basic.termℝ "ℝ") `n]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `bernsteinPolynomial.variance [(Data.Real.Basic.termℝ "ℝ") `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `bernsteinPolynomial.variance
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Mathlib.Tactic.Conv.convRHS
   "conv_rhs"
   []
   []
   "=>"
   (Tactic.Conv.convSeq
    (Tactic.Conv.convSeq1Indented
     [(group
       (Tactic.Conv.convRw__
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `div_mul_cancel [(Term.hole "_") `h']))] "]"))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Mathlib.Tactic.Conv.convRHS', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convRw__', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `div_mul_cancel [(Term.hole "_") `h'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `div_mul_cancel
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Mathlib.Tactic.Conv.convLHS
   "conv_lhs"
   []
   []
   "=>"
   (Tactic.Conv.convSeq
    (Tactic.Conv.convSeq1Indented
     [(group
       (Tactic.Conv.simp
        "simp"
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `Finset.sum_mul) "," (Tactic.simpLemma [] [] `z)] "]"]
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Mathlib.Tactic.Conv.convLHS', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'Lean.Parser.Tactic.discharger'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convSeq1Indented', expected 'Lean.Parser.Tactic.Conv.convSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  variance
  { n : ℕ } ( h : 0 < ( n : ℝ ) ) ( x : I ) : ∑ k : Finₓ n + 1 , ( x - k /ₙ : ℝ ) ^ 2 * bernstein n k x = x * 1 - x / n
  :=
    by
      have h' : ( n : ℝ ) ≠ 0 := ne_of_gtₓ h
        apply_fun fun x : ℝ => x * n using GroupWithZeroₓ.mul_right_injective h'
        apply_fun fun x : ℝ => x * n using GroupWithZeroₓ.mul_right_injective h'
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
            rw [ mul_commₓ _ ( n : ℝ ) , mul_commₓ _ ( n : ℝ ) , ← mul_assocₓ , ← mul_assocₓ ]
            congr 1
            field_simp [ h ]
            ring
        · ring

end bernstein

open bernstein

local postfix:2000 "/ₙ" => z

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    "\nThe `n`-th approximation of a continuous function on `[0,1]` by Bernstein polynomials,\ngiven by `∑ k, f (k/n) * bernstein n k x`.\n-/")]
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
       (Topology.UnitInterval.termI "I")
       ", "
       (Data.Real.Basic.termℝ "ℝ")
       ")")]
     []
     ")")]
   [(Term.typeSpec
     ":"
     (Topology.ContinuousFunction.Basic.«termC(_,_)»
      "C("
      (Topology.UnitInterval.termI "I")
      ", "
      (Data.Real.Basic.termℝ "ℝ")
      ")"))])
  (Command.declValSimple
   ":="
   (Algebra.BigOperators.Basic.«term∑_,_»
    "∑"
    (Lean.explicitBinders
     (Lean.unbracketedExplicitBinders
      [(Lean.binderIdent `k)]
      [":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])]))
    ", "
    (Algebra.Group.Defs.«term_•_»
     (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
     " • "
     (Term.app `bernstein [`n `k])))
   [])
  []
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_,_»
   "∑"
   (Lean.explicitBinders
    (Lean.unbracketedExplicitBinders
     [(Lean.binderIdent `k)]
     [":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])]))
   ", "
   (Algebra.Group.Defs.«term_•_»
    (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
    " • "
    (Term.app `bernstein [`n `k])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.Group.Defs.«term_•_»
   (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
   " • "
   (Term.app `bernstein [`n `k]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `bernstein [`n `k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `bernstein
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
  (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.SpecialFunctions.Bernstein.«term_/ₙ»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.SpecialFunctions.Bernstein.«term_/ₙ»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.SpecialFunctions.Bernstein.«term_/ₙ»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.SpecialFunctions.Bernstein.«term_/ₙ»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.SpecialFunctions.Bernstein.«term_/ₙ»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.SpecialFunctions.Bernstein.«term_/ₙ»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 2000, term))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 2000 >? 1024, (none, [anonymous]) <=? (some 2000, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [`k []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 2000, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1022, (some 1023, term) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The `n`-th approximation of a continuous function on `[0,1]` by Bernstein polynomials,
    given by `∑ k, f (k/n) * bernstein n k x`.
    -/
  def bernsteinApproximation ( n : ℕ ) ( f : C( I , ℝ ) ) : C( I , ℝ ) := ∑ k : Finₓ n + 1 , f k /ₙ • bernstein n k

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
       (Topology.UnitInterval.termI "I")
       ", "
       (Data.Real.Basic.termℝ "ℝ")
       ")")]
     []
     ")")
    (Term.explicitBinder "(" [`x] [":" (Topology.UnitInterval.termI "I")] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app `bernsteinApproximation [`n `f `x])
     "="
     (Algebra.BigOperators.Basic.«term∑_,_»
      "∑"
      (Lean.explicitBinders
       (Lean.unbracketedExplicitBinders
        [(Lean.binderIdent `k)]
        [":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])]))
      ", "
      (Finset.Data.Finset.Fold.«term_*_»
       (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
       "*"
       (Term.app `bernstein [`n `k `x]))))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `bernsteinApproximation)] "]"] []) [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `bernsteinApproximation)] "]"] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `bernsteinApproximation)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `bernsteinApproximation
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.app `bernsteinApproximation [`n `f `x])
   "="
   (Algebra.BigOperators.Basic.«term∑_,_»
    "∑"
    (Lean.explicitBinders
     (Lean.unbracketedExplicitBinders
      [(Lean.binderIdent `k)]
      [":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])]))
    ", "
    (Finset.Data.Finset.Fold.«term_*_»
     (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
     "*"
     (Term.app `bernstein [`n `k `x]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_,_»
   "∑"
   (Lean.explicitBinders
    (Lean.unbracketedExplicitBinders
     [(Lean.binderIdent `k)]
     [":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])]))
   ", "
   (Finset.Data.Finset.Fold.«term_*_»
    (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
    "*"
    (Term.app `bernstein [`n `k `x])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
   "*"
   (Term.app `bernstein [`n `k `x]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `bernstein [`n `k `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `bernstein
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.SpecialFunctions.Bernstein.«term_/ₙ»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.SpecialFunctions.Bernstein.«term_/ₙ»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.SpecialFunctions.Bernstein.«term_/ₙ»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.SpecialFunctions.Bernstein.«term_/ₙ»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.SpecialFunctions.Bernstein.«term_/ₙ»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.SpecialFunctions.Bernstein.«term_/ₙ»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 2000, term))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 2000 >? 1024, (none, [anonymous]) <=? (some 2000, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [`k []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 2000, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    apply
    ( n : ℕ ) ( f : C( I , ℝ ) ) ( x : I ) : bernsteinApproximation n f x = ∑ k : Finₓ n + 1 , f k /ₙ * bernstein n k x
    := by simp [ bernsteinApproximation ]

/-- 
The modulus of (uniform) continuity for `f`, chosen so `|f x - f y| < ε/2` when `|x - y| < δ`.
-/
def δ (f : C(I, ℝ)) (ε : ℝ) (h : 0 < ε) : ℝ :=
  f.modulus (ε / 2) (half_pos h)

/-- 
The set of points `k` so `k/n` is within `δ` of `x`.
-/
def S (f : C(I, ℝ)) (ε : ℝ) (h : 0 < ε) (n : ℕ) (x : I) : Finset (Finₓ (n+1)) :=
  { k : Finₓ (n+1) | dist (k)/ₙ x < δ f ε h }.toFinset

/-- 
If `k ∈ S`, then `f(k/n)` is close to `f x`.
-/
theorem lt_of_mem_S {f : C(I, ℝ)} {ε : ℝ} {h : 0 < ε} {n : ℕ} {x : I} {k : Finₓ (n+1)} (m : k ∈ S f ε h n x) :
    |f (k)/ₙ - f x| < ε / 2 := by
  apply f.dist_lt_of_dist_lt_modulus (ε / 2) (half_pos h)
  simpa [S] using m

/-- 
If `k ∉ S`, then as `δ ≤ |x - k/n|`, we have the inequality `1 ≤ δ^-2 * (x - k/n)^2`.
This particular formulation will be helpful later.
-/
theorem le_of_mem_S_compl {f : C(I, ℝ)} {ε : ℝ} {h : 0 < ε} {n : ℕ} {x : I} {k : Finₓ (n+1)} (m : k ∈ S f ε h n xᶜ) :
    (1 : ℝ) ≤ (δ f ε h^(-2 : ℤ))*x - (k)/ₙ^2 := by
  simp only [Finset.mem_compl, not_ltₓ, Set.mem_to_finset, Set.mem_set_of_eq, S] at m
  field_simp
  erw [le_div_iff (pow_pos f.modulus_pos 2), one_mulₓ]
  apply sq_le_sq
  rw [abs_eq_self.mpr (le_of_ltₓ f.modulus_pos)]
  rw [dist_comm] at m
  exact m

end bernsteinApproximation

open bernsteinApproximation

open BoundedContinuousFunction

open Filter

open_locale TopologicalSpace

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    "\nThe Bernstein approximations\n```\n∑ k : fin (n+1), f (k/n : ℝ) * n.choose k * x^k * (1-x)^(n-k)\n```\nfor a continuous function `f : C([0,1], ℝ)` converge uniformly to `f` as `n` tends to infinity.\n\nThis is the proof given in [Richard Beals' *Analysis, an introduction*][beals-analysis], §7D,\nand reproduced on wikipedia.\n-/")]
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
       (Topology.UnitInterval.termI "I")
       ", "
       (Data.Real.Basic.termℝ "ℝ")
       ")")]
     []
     ")")]
   (Term.typeSpec
    ":"
    (Term.app
     `tendsto
     [(Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`n] [(Term.typeSpec ":" (termℕ "ℕ"))])]
        "=>"
        (Term.app `bernsteinApproximation [`n `f])))
      `at_top
      (Term.app (Topology.Basic.term𝓝 "𝓝") [`f])])))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.simp
         "simp"
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
        [])
       (group (Tactic.intro "intro" [`ε `h]) [])
       (group (Tactic.tacticLet_ "let" (Term.letDecl (Term.letIdDecl `δ [] ":=" (Term.app `δ [`f `ε `h])))) [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`nhds_zero []]
           []
           ":="
           (Term.app
            `tendsto_const_div_at_top_nhds_0_nat
            [(Finset.Data.Finset.Fold.«term_*_»
              (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
              "*"
              (Cardinal.SetTheory.Cardinal.«term_^_»
               `δ
               "^"
               (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))]))))
        [])
       (group
        (Tactic.filterUpwards
         "filter_upwards"
         "["
         [(Term.app `nhds_zero.eventually [(Term.app `gt_mem_nhds [(Term.app `half_pos [`h])])])
          ","
          (Term.app `eventually_gt_at_top [(numLit "0")])]
         "]"
         [])
        [])
       (group (Tactic.intro "intro" [`n `nh `npos']) [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`npos []]
           [(Term.typeSpec
             ":"
             («term_<_»
              (numLit "0")
              "<"
              (Term.paren "(" [`n [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented [(group (Tactic.exactModCast "exact_mod_cast" `npos') [])]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`w₁ []]
           [(Term.typeSpec
             ":"
             («term_≤_»
              (numLit "0")
              "≤"
              (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))))]
           ":="
           (Term.app
            `mul_nonneg
            [(Term.byTactic
              "by"
              (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Lean.Tactic.normNum "norm_num" [] []) [])])))
             (Term.app `norm_nonneg [`f])]))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`w₂ []]
           [(Term.typeSpec
             ":"
             («term_≤_»
              (numLit "0")
              "≤"
              (Finset.Data.Finset.Fold.«term_*_»
               (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
               "*"
               (Cardinal.SetTheory.Cardinal.«term_^_»
                `δ
                "^"
                (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))))]
           ":="
           (Term.app `mul_nonneg [`w₁ `pow_minus_two_nonneg]))))
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `ContinuousMap.norm_lt_iff [(Term.hole "_") `h]))] "]")
         [])
        [])
       (group (Tactic.intro "intro" [`x]) [])
       (group (Tactic.tacticLet_ "let" (Term.letDecl (Term.letIdDecl `S [] ":=" (Term.app `S [`f `ε `h `n `x])))) [])
       (group
        (tacticCalc_
         "calc"
         [(calcStep
           («term_=_»
            (Analysis.NormedSpace.LatticeOrderedGroup.«term|_|»
             "|"
             (Term.app («term_-_» (Term.app `bernsteinApproximation [`n `f]) "-" `f) [`x])
             "|")
            "="
            (Analysis.NormedSpace.LatticeOrderedGroup.«term|_|»
             "|"
             («term_-_» (Term.app `bernsteinApproximation [`n `f `x]) "-" (Term.app `f [`x]))
             "|"))
           ":="
           `rfl)
          (calcStep
           («term_=_»
            (Term.hole "_")
            "="
            (Analysis.NormedSpace.LatticeOrderedGroup.«term|_|»
             "|"
             («term_-_»
              (Term.app `bernsteinApproximation [`n `f `x])
              "-"
              (Finset.Data.Finset.Fold.«term_*_» (Term.app `f [`x]) "*" (numLit "1")))
             "|"))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_oneₓ)] "]") []) [])]))))
          (calcStep
           («term_=_»
            (Term.hole "_")
            "="
            (Analysis.NormedSpace.LatticeOrderedGroup.«term|_|»
             "|"
             («term_-_»
              (Term.app `bernsteinApproximation [`n `f `x])
              "-"
              (Finset.Data.Finset.Fold.«term_*_»
               (Term.app `f [`x])
               "*"
               (Algebra.BigOperators.Basic.«term∑_,_»
                "∑"
                (Lean.explicitBinders
                 (Lean.unbracketedExplicitBinders
                  [(Lean.binderIdent `k)]
                  [":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])]))
                ", "
                (Term.app `bernstein [`n `k `x]))))
             "|"))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `bernstein.probability)] "]") [])
                [])]))))
          (calcStep
           («term_=_»
            (Term.hole "_")
            "="
            (Analysis.NormedSpace.LatticeOrderedGroup.«term|_|»
             "|"
             (Algebra.BigOperators.Basic.«term∑_,_»
              "∑"
              (Lean.explicitBinders
               (Lean.unbracketedExplicitBinders
                [(Lean.binderIdent `k)]
                [":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])]))
              ", "
              (Finset.Data.Finset.Fold.«term_*_»
               («term_-_»
                (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
                "-"
                (Term.app `f [`x]))
               "*"
               (Term.app `bernstein [`n `k `x])))
             "|"))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.simp
                 "simp"
                 []
                 []
                 ["["
                  [(Tactic.simpLemma [] [] `bernsteinApproximation)
                   ","
                   (Tactic.simpLemma [] [] `Finset.mul_sum)
                   ","
                   (Tactic.simpLemma [] [] `sub_mul)]
                  "]"]
                 [])
                [])]))))
          (calcStep
           («term_≤_»
            (Term.hole "_")
            "≤"
            (Algebra.BigOperators.Basic.«term∑_,_»
             "∑"
             (Lean.explicitBinders
              (Lean.unbracketedExplicitBinders
               [(Lean.binderIdent `k)]
               [":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])]))
             ", "
             (Analysis.NormedSpace.LatticeOrderedGroup.«term|_|»
              "|"
              (Finset.Data.Finset.Fold.«term_*_»
               («term_-_»
                (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
                "-"
                (Term.app `f [`x]))
               "*"
               (Term.app `bernstein [`n `k `x]))
              "|")))
           ":="
           (Term.app `Finset.abs_sum_le_sum_abs [(Term.hole "_") (Term.hole "_")]))
          (calcStep
           («term_=_»
            (Term.hole "_")
            "="
            (Algebra.BigOperators.Basic.«term∑_,_»
             "∑"
             (Lean.explicitBinders
              (Lean.unbracketedExplicitBinders
               [(Lean.binderIdent `k)]
               [":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])]))
             ", "
             (Finset.Data.Finset.Fold.«term_*_»
              (Analysis.NormedSpace.LatticeOrderedGroup.«term|_|»
               "|"
               («term_-_»
                (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
                "-"
                (Term.app `f [`x]))
               "|")
              "*"
              (Term.app `bernstein [`n `k `x]))))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.simpRw
                 "simp_rw"
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `abs_mul) "," (Tactic.rwRule [] (Term.app `abs_eq_self.mpr [`bernstein_nonneg]))]
                  "]")
                 [])
                [])]))))
          (calcStep
           («term_=_»
            (Term.hole "_")
            "="
            (Init.Logic.«term_+_»
             (Algebra.BigOperators.Basic.«term∑_in_,_»
              "∑"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
              " in "
              `S
              ", "
              (Finset.Data.Finset.Fold.«term_*_»
               (Analysis.NormedSpace.LatticeOrderedGroup.«term|_|»
                "|"
                («term_-_»
                 (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
                 "-"
                 (Term.app `f [`x]))
                "|")
               "*"
               (Term.app `bernstein [`n `k `x])))
             "+"
             (Algebra.BigOperators.Basic.«term∑_in_,_»
              "∑"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
              " in "
              (Order.BooleanAlgebra.«term_ᶜ» `S "ᶜ")
              ", "
              (Finset.Data.Finset.Fold.«term_*_»
               (Analysis.NormedSpace.LatticeOrderedGroup.«term|_|»
                "|"
                («term_-_»
                 (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
                 "-"
                 (Term.app `f [`x]))
                "|")
               "*"
               (Term.app `bernstein [`n `k `x])))))
           ":="
           (Term.proj (Term.app `S.sum_add_sum_compl [(Term.hole "_")]) "." `symm))
          (calcStep
           («term_<_»
            (Term.hole "_")
            "<"
            (Init.Logic.«term_+_» («term_/_» `ε "/" (numLit "2")) "+" («term_/_» `ε "/" (numLit "2"))))
           ":="
           (Term.app `add_lt_add_of_le_of_lt [(Term.hole "_") (Term.hole "_")]))
          (calcStep («term_=_» (Term.hole "_") "=" `ε) ":=" (Term.app `add_halves [`ε]))])
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (tacticCalc_
              "calc"
              [(calcStep
                («term_≤_»
                 (Algebra.BigOperators.Basic.«term∑_in_,_»
                  "∑"
                  (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                  " in "
                  `S
                  ", "
                  (Finset.Data.Finset.Fold.«term_*_»
                   (Analysis.NormedSpace.LatticeOrderedGroup.«term|_|»
                    "|"
                    («term_-_»
                     (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
                     "-"
                     (Term.app `f [`x]))
                    "|")
                   "*"
                   (Term.app `bernstein [`n `k `x])))
                 "≤"
                 (Algebra.BigOperators.Basic.«term∑_in_,_»
                  "∑"
                  (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                  " in "
                  `S
                  ", "
                  (Finset.Data.Finset.Fold.«term_*_»
                   («term_/_» `ε "/" (numLit "2"))
                   "*"
                   (Term.app `bernstein [`n `k `x]))))
                ":="
                (Term.app
                 `Finset.sum_le_sum
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`k `m] [])]
                    "=>"
                    (Term.app
                     `mul_le_mul_of_nonneg_right
                     [(Term.app `le_of_ltₓ [(Term.app `lt_of_mem_S [`m])]) `bernstein_nonneg])))]))
               (calcStep
                («term_=_»
                 (Term.hole "_")
                 "="
                 (Finset.Data.Finset.Fold.«term_*_»
                  («term_/_» `ε "/" (numLit "2"))
                  "*"
                  (Algebra.BigOperators.Basic.«term∑_in_,_»
                   "∑"
                   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                   " in "
                   `S
                   ", "
                   (Term.app `bernstein [`n `k `x]))))
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.mul_sum)] "]") [])
                     [])]))))
               (calcStep
                («term_≤_»
                 (Term.hole "_")
                 "≤"
                 (Finset.Data.Finset.Fold.«term_*_»
                  («term_/_» `ε "/" (numLit "2"))
                  "*"
                  (Algebra.BigOperators.Basic.«term∑_,_»
                   "∑"
                   (Lean.explicitBinders
                    (Lean.unbracketedExplicitBinders
                     [(Lean.binderIdent `k)]
                     [":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])]))
                   ", "
                   (Term.app `bernstein [`n `k `x]))))
                ":="
                (Term.app
                 `mul_le_mul_of_nonneg_left
                 [(Term.app
                   `Finset.sum_le_univ_sum_of_nonneg
                   [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k] [])] "=>" `bernstein_nonneg))])
                  (Term.app `le_of_ltₓ [(Term.app `half_pos [`h])])]))
               (calcStep
                («term_=_» (Term.hole "_") "=" («term_/_» `ε "/" (numLit "2")))
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [] `bernstein.probability) "," (Tactic.rwRule [] `mul_oneₓ)]
                       "]")
                      [])
                     [])]))))])
             [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (tacticCalc_
              "calc"
              [(calcStep
                («term_≤_»
                 (Algebra.BigOperators.Basic.«term∑_in_,_»
                  "∑"
                  (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                  " in "
                  (Order.BooleanAlgebra.«term_ᶜ» `S "ᶜ")
                  ", "
                  (Finset.Data.Finset.Fold.«term_*_»
                   (Analysis.NormedSpace.LatticeOrderedGroup.«term|_|»
                    "|"
                    («term_-_»
                     (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
                     "-"
                     (Term.app `f [`x]))
                    "|")
                   "*"
                   (Term.app `bernstein [`n `k `x])))
                 "≤"
                 (Algebra.BigOperators.Basic.«term∑_in_,_»
                  "∑"
                  (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                  " in "
                  (Order.BooleanAlgebra.«term_ᶜ» `S "ᶜ")
                  ", "
                  (Finset.Data.Finset.Fold.«term_*_»
                   (Finset.Data.Finset.Fold.«term_*_»
                    (numLit "2")
                    "*"
                    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
                   "*"
                   (Term.app `bernstein [`n `k `x]))))
                ":="
                (Term.app
                 `Finset.sum_le_sum
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`k `m] [])]
                    "=>"
                    (Term.app
                     `mul_le_mul_of_nonneg_right
                     [(Term.app `f.dist_le_two_norm [(Term.hole "_") (Term.hole "_")]) `bernstein_nonneg])))]))
               (calcStep
                («term_=_»
                 (Term.hole "_")
                 "="
                 (Finset.Data.Finset.Fold.«term_*_»
                  (Finset.Data.Finset.Fold.«term_*_»
                   (numLit "2")
                   "*"
                   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
                  "*"
                  (Algebra.BigOperators.Basic.«term∑_in_,_»
                   "∑"
                   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                   " in "
                   (Order.BooleanAlgebra.«term_ᶜ» `S "ᶜ")
                   ", "
                   (Term.app `bernstein [`n `k `x]))))
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.mul_sum)] "]") [])
                     [])]))))
               (calcStep
                («term_≤_»
                 (Term.hole "_")
                 "≤"
                 (Finset.Data.Finset.Fold.«term_*_»
                  (Finset.Data.Finset.Fold.«term_*_»
                   (numLit "2")
                   "*"
                   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
                  "*"
                  (Algebra.BigOperators.Basic.«term∑_in_,_»
                   "∑"
                   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                   " in "
                   (Order.BooleanAlgebra.«term_ᶜ» `S "ᶜ")
                   ", "
                   (Finset.Data.Finset.Fold.«term_*_»
                    (Finset.Data.Finset.Fold.«term_*_»
                     (Cardinal.SetTheory.Cardinal.«term_^_»
                      `δ
                      "^"
                      (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")"))
                     "*"
                     (Cardinal.SetTheory.Cardinal.«term_^_»
                      («term_-_» `x "-" (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
                      "^"
                      (numLit "2")))
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
                      [(Term.simpleBinder [`k `m] [])]
                      "=>"
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(group
                           (Mathlib.Tactic.Conv.convLHS
                            "conv_lhs"
                            []
                            []
                            "=>"
                            (Tactic.Conv.convSeq
                             (Tactic.Conv.convSeq1Indented
                              [(group
                                (Tactic.Conv.convRw__
                                 "rw"
                                 []
                                 (Tactic.rwRuleSeq
                                  "["
                                  [(Tactic.rwRule
                                    ["←"]
                                    (Term.app
                                     `one_mulₓ
                                     [(Term.app `bernstein [(Term.hole "_") (Term.hole "_") (Term.hole "_")])]))]
                                  "]"))
                                [])])))
                           [])
                          (group
                           (Tactic.exact
                            "exact"
                            (Term.app
                             `mul_le_mul_of_nonneg_right
                             [(Term.app `le_of_mem_S_compl [`m]) `bernstein_nonneg]))
                           [])])))))])
                  `w₁]))
               (calcStep
                («term_≤_»
                 (Term.hole "_")
                 "≤"
                 (Finset.Data.Finset.Fold.«term_*_»
                  (Finset.Data.Finset.Fold.«term_*_»
                   (numLit "2")
                   "*"
                   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
                  "*"
                  (Algebra.BigOperators.Basic.«term∑_,_»
                   "∑"
                   (Lean.explicitBinders
                    (Lean.unbracketedExplicitBinders
                     [(Lean.binderIdent `k)]
                     [":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])]))
                   ", "
                   (Finset.Data.Finset.Fold.«term_*_»
                    (Finset.Data.Finset.Fold.«term_*_»
                     (Cardinal.SetTheory.Cardinal.«term_^_»
                      `δ
                      "^"
                      (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")"))
                     "*"
                     (Cardinal.SetTheory.Cardinal.«term_^_»
                      («term_-_» `x "-" (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
                      "^"
                      (numLit "2")))
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
                      [(Term.simpleBinder [`k] [])]
                      "=>"
                      (Term.app
                       `mul_nonneg
                       [(Term.app `mul_nonneg [`pow_minus_two_nonneg (Term.app `sq_nonneg [(Term.hole "_")])])
                        `bernstein_nonneg])))])
                  `w₁]))
               (calcStep
                («term_=_»
                 (Term.hole "_")
                 "="
                 (Finset.Data.Finset.Fold.«term_*_»
                  (Finset.Data.Finset.Fold.«term_*_»
                   (Finset.Data.Finset.Fold.«term_*_»
                    (numLit "2")
                    "*"
                    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
                   "*"
                   (Cardinal.SetTheory.Cardinal.«term_^_»
                    `δ
                    "^"
                    (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))
                  "*"
                  (Algebra.BigOperators.Basic.«term∑_,_»
                   "∑"
                   (Lean.explicitBinders
                    (Lean.unbracketedExplicitBinders
                     [(Lean.binderIdent `k)]
                     [":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])]))
                   ", "
                   (Finset.Data.Finset.Fold.«term_*_»
                    (Cardinal.SetTheory.Cardinal.«term_^_»
                     («term_-_» `x "-" (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
                     "^"
                     (numLit "2"))
                    "*"
                    (Term.app `bernstein [`n `k `x])))))
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Mathlib.Tactic.Conv.convRHS
                      "conv_rhs"
                      []
                      []
                      "=>"
                      (Tactic.Conv.convSeq
                       (Tactic.Conv.convSeq1Indented
                        [(group
                          (Tactic.Conv.convRw__
                           "rw"
                           []
                           (Tactic.rwRuleSeq
                            "["
                            [(Tactic.rwRule [] `mul_assocₓ) "," (Tactic.rwRule [] `Finset.mul_sum)]
                            "]"))
                          [])
                         (group
                          (Tactic.Conv.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] ["←"] `mul_assocₓ)] "]"] [])
                          [])])))
                     [])]))))
               (calcStep
                («term_=_»
                 (Term.hole "_")
                 "="
                 («term_/_»
                  (Finset.Data.Finset.Fold.«term_*_»
                   (Finset.Data.Finset.Fold.«term_*_»
                    (Finset.Data.Finset.Fold.«term_*_»
                     (Finset.Data.Finset.Fold.«term_*_»
                      (numLit "2")
                      "*"
                      (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
                     "*"
                     (Cardinal.SetTheory.Cardinal.«term_^_»
                      `δ
                      "^"
                      (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))
                    "*"
                    `x)
                   "*"
                   («term_-_» (numLit "1") "-" `x))
                  "/"
                  `n))
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `variance [`npos]))] "]")
                      [])
                     [])
                    (group (Tactic.Ring.tacticRing "ring") [])]))))
               (calcStep
                («term_≤_»
                 (Term.hole "_")
                 "≤"
                 («term_/_»
                  (Finset.Data.Finset.Fold.«term_*_»
                   (Finset.Data.Finset.Fold.«term_*_»
                    (numLit "2")
                    "*"
                    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
                   "*"
                   (Cardinal.SetTheory.Cardinal.«term_^_»
                    `δ
                    "^"
                    (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))
                  "/"
                  `n))
                ":="
                (Term.app
                 (Term.proj (Term.app `div_le_div_right [`npos]) "." `mpr)
                 [(Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group (Tactic.apply "apply" (Term.app `mul_nonneg_le_one_le [`w₂])) [])
                      (group
                       (Tactic.apply
                        "apply"
                        (Term.app `mul_nonneg_le_one_le [`w₂ (Term.app `le_reflₓ [(Term.hole "_")])]))
                       [])
                      (group
                       (Tactic.allGoals
                        "all_goals"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented [(group (Tactic.unitInterval "unit_interval") [])])))
                       [])])))]))
               (calcStep («term_<_» (Term.hole "_") "<" («term_/_» `ε "/" (numLit "2"))) ":=" `nh)])
             [])])))
        [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.simp
        "simp"
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
       [])
      (group (Tactic.intro "intro" [`ε `h]) [])
      (group (Tactic.tacticLet_ "let" (Term.letDecl (Term.letIdDecl `δ [] ":=" (Term.app `δ [`f `ε `h])))) [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`nhds_zero []]
          []
          ":="
          (Term.app
           `tendsto_const_div_at_top_nhds_0_nat
           [(Finset.Data.Finset.Fold.«term_*_»
             (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
             "*"
             (Cardinal.SetTheory.Cardinal.«term_^_»
              `δ
              "^"
              (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))]))))
       [])
      (group
       (Tactic.filterUpwards
        "filter_upwards"
        "["
        [(Term.app `nhds_zero.eventually [(Term.app `gt_mem_nhds [(Term.app `half_pos [`h])])])
         ","
         (Term.app `eventually_gt_at_top [(numLit "0")])]
        "]"
        [])
       [])
      (group (Tactic.intro "intro" [`n `nh `npos']) [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`npos []]
          [(Term.typeSpec
            ":"
            («term_<_»
             (numLit "0")
             "<"
             (Term.paren "(" [`n [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.exactModCast "exact_mod_cast" `npos') [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`w₁ []]
          [(Term.typeSpec
            ":"
            («term_≤_»
             (numLit "0")
             "≤"
             (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))))]
          ":="
          (Term.app
           `mul_nonneg
           [(Term.byTactic
             "by"
             (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Lean.Tactic.normNum "norm_num" [] []) [])])))
            (Term.app `norm_nonneg [`f])]))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`w₂ []]
          [(Term.typeSpec
            ":"
            («term_≤_»
             (numLit "0")
             "≤"
             (Finset.Data.Finset.Fold.«term_*_»
              (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
              "*"
              (Cardinal.SetTheory.Cardinal.«term_^_»
               `δ
               "^"
               (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))))]
          ":="
          (Term.app `mul_nonneg [`w₁ `pow_minus_two_nonneg]))))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `ContinuousMap.norm_lt_iff [(Term.hole "_") `h]))] "]")
        [])
       [])
      (group (Tactic.intro "intro" [`x]) [])
      (group (Tactic.tacticLet_ "let" (Term.letDecl (Term.letIdDecl `S [] ":=" (Term.app `S [`f `ε `h `n `x])))) [])
      (group
       (tacticCalc_
        "calc"
        [(calcStep
          («term_=_»
           (Analysis.NormedSpace.LatticeOrderedGroup.«term|_|»
            "|"
            (Term.app («term_-_» (Term.app `bernsteinApproximation [`n `f]) "-" `f) [`x])
            "|")
           "="
           (Analysis.NormedSpace.LatticeOrderedGroup.«term|_|»
            "|"
            («term_-_» (Term.app `bernsteinApproximation [`n `f `x]) "-" (Term.app `f [`x]))
            "|"))
          ":="
          `rfl)
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Analysis.NormedSpace.LatticeOrderedGroup.«term|_|»
            "|"
            («term_-_»
             (Term.app `bernsteinApproximation [`n `f `x])
             "-"
             (Finset.Data.Finset.Fold.«term_*_» (Term.app `f [`x]) "*" (numLit "1")))
            "|"))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_oneₓ)] "]") []) [])]))))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Analysis.NormedSpace.LatticeOrderedGroup.«term|_|»
            "|"
            («term_-_»
             (Term.app `bernsteinApproximation [`n `f `x])
             "-"
             (Finset.Data.Finset.Fold.«term_*_»
              (Term.app `f [`x])
              "*"
              (Algebra.BigOperators.Basic.«term∑_,_»
               "∑"
               (Lean.explicitBinders
                (Lean.unbracketedExplicitBinders
                 [(Lean.binderIdent `k)]
                 [":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])]))
               ", "
               (Term.app `bernstein [`n `k `x]))))
            "|"))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `bernstein.probability)] "]") [])
               [])]))))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Analysis.NormedSpace.LatticeOrderedGroup.«term|_|»
            "|"
            (Algebra.BigOperators.Basic.«term∑_,_»
             "∑"
             (Lean.explicitBinders
              (Lean.unbracketedExplicitBinders
               [(Lean.binderIdent `k)]
               [":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])]))
             ", "
             (Finset.Data.Finset.Fold.«term_*_»
              («term_-_» (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")]) "-" (Term.app `f [`x]))
              "*"
              (Term.app `bernstein [`n `k `x])))
            "|"))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.simp
                "simp"
                []
                []
                ["["
                 [(Tactic.simpLemma [] [] `bernsteinApproximation)
                  ","
                  (Tactic.simpLemma [] [] `Finset.mul_sum)
                  ","
                  (Tactic.simpLemma [] [] `sub_mul)]
                 "]"]
                [])
               [])]))))
         (calcStep
          («term_≤_»
           (Term.hole "_")
           "≤"
           (Algebra.BigOperators.Basic.«term∑_,_»
            "∑"
            (Lean.explicitBinders
             (Lean.unbracketedExplicitBinders
              [(Lean.binderIdent `k)]
              [":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])]))
            ", "
            (Analysis.NormedSpace.LatticeOrderedGroup.«term|_|»
             "|"
             (Finset.Data.Finset.Fold.«term_*_»
              («term_-_» (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")]) "-" (Term.app `f [`x]))
              "*"
              (Term.app `bernstein [`n `k `x]))
             "|")))
          ":="
          (Term.app `Finset.abs_sum_le_sum_abs [(Term.hole "_") (Term.hole "_")]))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Algebra.BigOperators.Basic.«term∑_,_»
            "∑"
            (Lean.explicitBinders
             (Lean.unbracketedExplicitBinders
              [(Lean.binderIdent `k)]
              [":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])]))
            ", "
            (Finset.Data.Finset.Fold.«term_*_»
             (Analysis.NormedSpace.LatticeOrderedGroup.«term|_|»
              "|"
              («term_-_» (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")]) "-" (Term.app `f [`x]))
              "|")
             "*"
             (Term.app `bernstein [`n `k `x]))))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.simpRw
                "simp_rw"
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `abs_mul) "," (Tactic.rwRule [] (Term.app `abs_eq_self.mpr [`bernstein_nonneg]))]
                 "]")
                [])
               [])]))))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Init.Logic.«term_+_»
            (Algebra.BigOperators.Basic.«term∑_in_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
             " in "
             `S
             ", "
             (Finset.Data.Finset.Fold.«term_*_»
              (Analysis.NormedSpace.LatticeOrderedGroup.«term|_|»
               "|"
               («term_-_»
                (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
                "-"
                (Term.app `f [`x]))
               "|")
              "*"
              (Term.app `bernstein [`n `k `x])))
            "+"
            (Algebra.BigOperators.Basic.«term∑_in_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
             " in "
             (Order.BooleanAlgebra.«term_ᶜ» `S "ᶜ")
             ", "
             (Finset.Data.Finset.Fold.«term_*_»
              (Analysis.NormedSpace.LatticeOrderedGroup.«term|_|»
               "|"
               («term_-_»
                (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
                "-"
                (Term.app `f [`x]))
               "|")
              "*"
              (Term.app `bernstein [`n `k `x])))))
          ":="
          (Term.proj (Term.app `S.sum_add_sum_compl [(Term.hole "_")]) "." `symm))
         (calcStep
          («term_<_»
           (Term.hole "_")
           "<"
           (Init.Logic.«term_+_» («term_/_» `ε "/" (numLit "2")) "+" («term_/_» `ε "/" (numLit "2"))))
          ":="
          (Term.app `add_lt_add_of_le_of_lt [(Term.hole "_") (Term.hole "_")]))
         (calcStep («term_=_» (Term.hole "_") "=" `ε) ":=" (Term.app `add_halves [`ε]))])
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (tacticCalc_
             "calc"
             [(calcStep
               («term_≤_»
                (Algebra.BigOperators.Basic.«term∑_in_,_»
                 "∑"
                 (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                 " in "
                 `S
                 ", "
                 (Finset.Data.Finset.Fold.«term_*_»
                  (Analysis.NormedSpace.LatticeOrderedGroup.«term|_|»
                   "|"
                   («term_-_»
                    (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
                    "-"
                    (Term.app `f [`x]))
                   "|")
                  "*"
                  (Term.app `bernstein [`n `k `x])))
                "≤"
                (Algebra.BigOperators.Basic.«term∑_in_,_»
                 "∑"
                 (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                 " in "
                 `S
                 ", "
                 (Finset.Data.Finset.Fold.«term_*_»
                  («term_/_» `ε "/" (numLit "2"))
                  "*"
                  (Term.app `bernstein [`n `k `x]))))
               ":="
               (Term.app
                `Finset.sum_le_sum
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`k `m] [])]
                   "=>"
                   (Term.app
                    `mul_le_mul_of_nonneg_right
                    [(Term.app `le_of_ltₓ [(Term.app `lt_of_mem_S [`m])]) `bernstein_nonneg])))]))
              (calcStep
               («term_=_»
                (Term.hole "_")
                "="
                (Finset.Data.Finset.Fold.«term_*_»
                 («term_/_» `ε "/" (numLit "2"))
                 "*"
                 (Algebra.BigOperators.Basic.«term∑_in_,_»
                  "∑"
                  (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                  " in "
                  `S
                  ", "
                  (Term.app `bernstein [`n `k `x]))))
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.mul_sum)] "]") [])
                    [])]))))
              (calcStep
               («term_≤_»
                (Term.hole "_")
                "≤"
                (Finset.Data.Finset.Fold.«term_*_»
                 («term_/_» `ε "/" (numLit "2"))
                 "*"
                 (Algebra.BigOperators.Basic.«term∑_,_»
                  "∑"
                  (Lean.explicitBinders
                   (Lean.unbracketedExplicitBinders
                    [(Lean.binderIdent `k)]
                    [":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])]))
                  ", "
                  (Term.app `bernstein [`n `k `x]))))
               ":="
               (Term.app
                `mul_le_mul_of_nonneg_left
                [(Term.app
                  `Finset.sum_le_univ_sum_of_nonneg
                  [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k] [])] "=>" `bernstein_nonneg))])
                 (Term.app `le_of_ltₓ [(Term.app `half_pos [`h])])]))
              (calcStep
               («term_=_» (Term.hole "_") "=" («term_/_» `ε "/" (numLit "2")))
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] `bernstein.probability) "," (Tactic.rwRule [] `mul_oneₓ)]
                      "]")
                     [])
                    [])]))))])
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (tacticCalc_
             "calc"
             [(calcStep
               («term_≤_»
                (Algebra.BigOperators.Basic.«term∑_in_,_»
                 "∑"
                 (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                 " in "
                 (Order.BooleanAlgebra.«term_ᶜ» `S "ᶜ")
                 ", "
                 (Finset.Data.Finset.Fold.«term_*_»
                  (Analysis.NormedSpace.LatticeOrderedGroup.«term|_|»
                   "|"
                   («term_-_»
                    (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")])
                    "-"
                    (Term.app `f [`x]))
                   "|")
                  "*"
                  (Term.app `bernstein [`n `k `x])))
                "≤"
                (Algebra.BigOperators.Basic.«term∑_in_,_»
                 "∑"
                 (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                 " in "
                 (Order.BooleanAlgebra.«term_ᶜ» `S "ᶜ")
                 ", "
                 (Finset.Data.Finset.Fold.«term_*_»
                  (Finset.Data.Finset.Fold.«term_*_»
                   (numLit "2")
                   "*"
                   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
                  "*"
                  (Term.app `bernstein [`n `k `x]))))
               ":="
               (Term.app
                `Finset.sum_le_sum
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`k `m] [])]
                   "=>"
                   (Term.app
                    `mul_le_mul_of_nonneg_right
                    [(Term.app `f.dist_le_two_norm [(Term.hole "_") (Term.hole "_")]) `bernstein_nonneg])))]))
              (calcStep
               («term_=_»
                (Term.hole "_")
                "="
                (Finset.Data.Finset.Fold.«term_*_»
                 (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
                 "*"
                 (Algebra.BigOperators.Basic.«term∑_in_,_»
                  "∑"
                  (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                  " in "
                  (Order.BooleanAlgebra.«term_ᶜ» `S "ᶜ")
                  ", "
                  (Term.app `bernstein [`n `k `x]))))
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.mul_sum)] "]") [])
                    [])]))))
              (calcStep
               («term_≤_»
                (Term.hole "_")
                "≤"
                (Finset.Data.Finset.Fold.«term_*_»
                 (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
                 "*"
                 (Algebra.BigOperators.Basic.«term∑_in_,_»
                  "∑"
                  (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                  " in "
                  (Order.BooleanAlgebra.«term_ᶜ» `S "ᶜ")
                  ", "
                  (Finset.Data.Finset.Fold.«term_*_»
                   (Finset.Data.Finset.Fold.«term_*_»
                    (Cardinal.SetTheory.Cardinal.«term_^_»
                     `δ
                     "^"
                     (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")"))
                    "*"
                    (Cardinal.SetTheory.Cardinal.«term_^_»
                     («term_-_» `x "-" (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
                     "^"
                     (numLit "2")))
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
                     [(Term.simpleBinder [`k `m] [])]
                     "=>"
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(group
                          (Mathlib.Tactic.Conv.convLHS
                           "conv_lhs"
                           []
                           []
                           "=>"
                           (Tactic.Conv.convSeq
                            (Tactic.Conv.convSeq1Indented
                             [(group
                               (Tactic.Conv.convRw__
                                "rw"
                                []
                                (Tactic.rwRuleSeq
                                 "["
                                 [(Tactic.rwRule
                                   ["←"]
                                   (Term.app
                                    `one_mulₓ
                                    [(Term.app `bernstein [(Term.hole "_") (Term.hole "_") (Term.hole "_")])]))]
                                 "]"))
                               [])])))
                          [])
                         (group
                          (Tactic.exact
                           "exact"
                           (Term.app
                            `mul_le_mul_of_nonneg_right
                            [(Term.app `le_of_mem_S_compl [`m]) `bernstein_nonneg]))
                          [])])))))])
                 `w₁]))
              (calcStep
               («term_≤_»
                (Term.hole "_")
                "≤"
                (Finset.Data.Finset.Fold.«term_*_»
                 (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
                 "*"
                 (Algebra.BigOperators.Basic.«term∑_,_»
                  "∑"
                  (Lean.explicitBinders
                   (Lean.unbracketedExplicitBinders
                    [(Lean.binderIdent `k)]
                    [":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])]))
                  ", "
                  (Finset.Data.Finset.Fold.«term_*_»
                   (Finset.Data.Finset.Fold.«term_*_»
                    (Cardinal.SetTheory.Cardinal.«term_^_»
                     `δ
                     "^"
                     (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")"))
                    "*"
                    (Cardinal.SetTheory.Cardinal.«term_^_»
                     («term_-_» `x "-" (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
                     "^"
                     (numLit "2")))
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
                     [(Term.simpleBinder [`k] [])]
                     "=>"
                     (Term.app
                      `mul_nonneg
                      [(Term.app `mul_nonneg [`pow_minus_two_nonneg (Term.app `sq_nonneg [(Term.hole "_")])])
                       `bernstein_nonneg])))])
                 `w₁]))
              (calcStep
               («term_=_»
                (Term.hole "_")
                "="
                (Finset.Data.Finset.Fold.«term_*_»
                 (Finset.Data.Finset.Fold.«term_*_»
                  (Finset.Data.Finset.Fold.«term_*_»
                   (numLit "2")
                   "*"
                   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
                  "*"
                  (Cardinal.SetTheory.Cardinal.«term_^_»
                   `δ
                   "^"
                   (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))
                 "*"
                 (Algebra.BigOperators.Basic.«term∑_,_»
                  "∑"
                  (Lean.explicitBinders
                   (Lean.unbracketedExplicitBinders
                    [(Lean.binderIdent `k)]
                    [":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])]))
                  ", "
                  (Finset.Data.Finset.Fold.«term_*_»
                   (Cardinal.SetTheory.Cardinal.«term_^_»
                    («term_-_» `x "-" (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
                    "^"
                    (numLit "2"))
                   "*"
                   (Term.app `bernstein [`n `k `x])))))
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Mathlib.Tactic.Conv.convRHS
                     "conv_rhs"
                     []
                     []
                     "=>"
                     (Tactic.Conv.convSeq
                      (Tactic.Conv.convSeq1Indented
                       [(group
                         (Tactic.Conv.convRw__
                          "rw"
                          []
                          (Tactic.rwRuleSeq
                           "["
                           [(Tactic.rwRule [] `mul_assocₓ) "," (Tactic.rwRule [] `Finset.mul_sum)]
                           "]"))
                         [])
                        (group
                         (Tactic.Conv.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] ["←"] `mul_assocₓ)] "]"] [])
                         [])])))
                    [])]))))
              (calcStep
               («term_=_»
                (Term.hole "_")
                "="
                («term_/_»
                 (Finset.Data.Finset.Fold.«term_*_»
                  (Finset.Data.Finset.Fold.«term_*_»
                   (Finset.Data.Finset.Fold.«term_*_»
                    (Finset.Data.Finset.Fold.«term_*_»
                     (numLit "2")
                     "*"
                     (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
                    "*"
                    (Cardinal.SetTheory.Cardinal.«term_^_»
                     `δ
                     "^"
                     (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))
                   "*"
                   `x)
                  "*"
                  («term_-_» (numLit "1") "-" `x))
                 "/"
                 `n))
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `variance [`npos]))] "]")
                     [])
                    [])
                   (group (Tactic.Ring.tacticRing "ring") [])]))))
              (calcStep
               («term_≤_»
                (Term.hole "_")
                "≤"
                («term_/_»
                 (Finset.Data.Finset.Fold.«term_*_»
                  (Finset.Data.Finset.Fold.«term_*_»
                   (numLit "2")
                   "*"
                   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
                  "*"
                  (Cardinal.SetTheory.Cardinal.«term_^_»
                   `δ
                   "^"
                   (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))
                 "/"
                 `n))
               ":="
               (Term.app
                (Term.proj (Term.app `div_le_div_right [`npos]) "." `mpr)
                [(Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(group (Tactic.apply "apply" (Term.app `mul_nonneg_le_one_le [`w₂])) [])
                     (group
                      (Tactic.apply
                       "apply"
                       (Term.app `mul_nonneg_le_one_le [`w₂ (Term.app `le_reflₓ [(Term.hole "_")])]))
                      [])
                     (group
                      (Tactic.allGoals
                       "all_goals"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented [(group (Tactic.unitInterval "unit_interval") [])])))
                      [])])))]))
              (calcStep («term_<_» (Term.hole "_") "<" («term_/_» `ε "/" (numLit "2"))) ":=" `nh)])
            [])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (tacticCalc_
        "calc"
        [(calcStep
          («term_≤_»
           (Algebra.BigOperators.Basic.«term∑_in_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
            " in "
            (Order.BooleanAlgebra.«term_ᶜ» `S "ᶜ")
            ", "
            (Finset.Data.Finset.Fold.«term_*_»
             (Analysis.NormedSpace.LatticeOrderedGroup.«term|_|»
              "|"
              («term_-_» (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")]) "-" (Term.app `f [`x]))
              "|")
             "*"
             (Term.app `bernstein [`n `k `x])))
           "≤"
           (Algebra.BigOperators.Basic.«term∑_in_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
            " in "
            (Order.BooleanAlgebra.«term_ᶜ» `S "ᶜ")
            ", "
            (Finset.Data.Finset.Fold.«term_*_»
             (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
             "*"
             (Term.app `bernstein [`n `k `x]))))
          ":="
          (Term.app
           `Finset.sum_le_sum
           [(Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`k `m] [])]
              "=>"
              (Term.app
               `mul_le_mul_of_nonneg_right
               [(Term.app `f.dist_le_two_norm [(Term.hole "_") (Term.hole "_")]) `bernstein_nonneg])))]))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Finset.Data.Finset.Fold.«term_*_»
            (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
            "*"
            (Algebra.BigOperators.Basic.«term∑_in_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
             " in "
             (Order.BooleanAlgebra.«term_ᶜ» `S "ᶜ")
             ", "
             (Term.app `bernstein [`n `k `x]))))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.mul_sum)] "]") []) [])]))))
         (calcStep
          («term_≤_»
           (Term.hole "_")
           "≤"
           (Finset.Data.Finset.Fold.«term_*_»
            (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
            "*"
            (Algebra.BigOperators.Basic.«term∑_in_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
             " in "
             (Order.BooleanAlgebra.«term_ᶜ» `S "ᶜ")
             ", "
             (Finset.Data.Finset.Fold.«term_*_»
              (Finset.Data.Finset.Fold.«term_*_»
               (Cardinal.SetTheory.Cardinal.«term_^_»
                `δ
                "^"
                (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")"))
               "*"
               (Cardinal.SetTheory.Cardinal.«term_^_»
                («term_-_» `x "-" (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
                "^"
                (numLit "2")))
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
                [(Term.simpleBinder [`k `m] [])]
                "=>"
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Mathlib.Tactic.Conv.convLHS
                      "conv_lhs"
                      []
                      []
                      "=>"
                      (Tactic.Conv.convSeq
                       (Tactic.Conv.convSeq1Indented
                        [(group
                          (Tactic.Conv.convRw__
                           "rw"
                           []
                           (Tactic.rwRuleSeq
                            "["
                            [(Tactic.rwRule
                              ["←"]
                              (Term.app
                               `one_mulₓ
                               [(Term.app `bernstein [(Term.hole "_") (Term.hole "_") (Term.hole "_")])]))]
                            "]"))
                          [])])))
                     [])
                    (group
                     (Tactic.exact
                      "exact"
                      (Term.app `mul_le_mul_of_nonneg_right [(Term.app `le_of_mem_S_compl [`m]) `bernstein_nonneg]))
                     [])])))))])
            `w₁]))
         (calcStep
          («term_≤_»
           (Term.hole "_")
           "≤"
           (Finset.Data.Finset.Fold.«term_*_»
            (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
            "*"
            (Algebra.BigOperators.Basic.«term∑_,_»
             "∑"
             (Lean.explicitBinders
              (Lean.unbracketedExplicitBinders
               [(Lean.binderIdent `k)]
               [":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])]))
             ", "
             (Finset.Data.Finset.Fold.«term_*_»
              (Finset.Data.Finset.Fold.«term_*_»
               (Cardinal.SetTheory.Cardinal.«term_^_»
                `δ
                "^"
                (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")"))
               "*"
               (Cardinal.SetTheory.Cardinal.«term_^_»
                («term_-_» `x "-" (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
                "^"
                (numLit "2")))
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
                [(Term.simpleBinder [`k] [])]
                "=>"
                (Term.app
                 `mul_nonneg
                 [(Term.app `mul_nonneg [`pow_minus_two_nonneg (Term.app `sq_nonneg [(Term.hole "_")])])
                  `bernstein_nonneg])))])
            `w₁]))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Finset.Data.Finset.Fold.«term_*_»
            (Finset.Data.Finset.Fold.«term_*_»
             (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
             "*"
             (Cardinal.SetTheory.Cardinal.«term_^_»
              `δ
              "^"
              (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))
            "*"
            (Algebra.BigOperators.Basic.«term∑_,_»
             "∑"
             (Lean.explicitBinders
              (Lean.unbracketedExplicitBinders
               [(Lean.binderIdent `k)]
               [":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])]))
             ", "
             (Finset.Data.Finset.Fold.«term_*_»
              (Cardinal.SetTheory.Cardinal.«term_^_»
               («term_-_» `x "-" (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
               "^"
               (numLit "2"))
              "*"
              (Term.app `bernstein [`n `k `x])))))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Mathlib.Tactic.Conv.convRHS
                "conv_rhs"
                []
                []
                "=>"
                (Tactic.Conv.convSeq
                 (Tactic.Conv.convSeq1Indented
                  [(group
                    (Tactic.Conv.convRw__
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_assocₓ) "," (Tactic.rwRule [] `Finset.mul_sum)] "]"))
                    [])
                   (group
                    (Tactic.Conv.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] ["←"] `mul_assocₓ)] "]"] [])
                    [])])))
               [])]))))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           («term_/_»
            (Finset.Data.Finset.Fold.«term_*_»
             (Finset.Data.Finset.Fold.«term_*_»
              (Finset.Data.Finset.Fold.«term_*_»
               (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
               "*"
               (Cardinal.SetTheory.Cardinal.«term_^_»
                `δ
                "^"
                (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))
              "*"
              `x)
             "*"
             («term_-_» (numLit "1") "-" `x))
            "/"
            `n))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `variance [`npos]))] "]") [])
               [])
              (group (Tactic.Ring.tacticRing "ring") [])]))))
         (calcStep
          («term_≤_»
           (Term.hole "_")
           "≤"
           («term_/_»
            (Finset.Data.Finset.Fold.«term_*_»
             (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
             "*"
             (Cardinal.SetTheory.Cardinal.«term_^_»
              `δ
              "^"
              (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))
            "/"
            `n))
          ":="
          (Term.app
           (Term.proj (Term.app `div_le_div_right [`npos]) "." `mpr)
           [(Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group (Tactic.apply "apply" (Term.app `mul_nonneg_le_one_le [`w₂])) [])
                (group
                 (Tactic.apply "apply" (Term.app `mul_nonneg_le_one_le [`w₂ (Term.app `le_reflₓ [(Term.hole "_")])]))
                 [])
                (group
                 (Tactic.allGoals
                  "all_goals"
                  (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.unitInterval "unit_interval") [])])))
                 [])])))]))
         (calcStep («term_<_» (Term.hole "_") "<" («term_/_» `ε "/" (numLit "2"))) ":=" `nh)])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (tacticCalc_
   "calc"
   [(calcStep
     («term_≤_»
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
       " in "
       (Order.BooleanAlgebra.«term_ᶜ» `S "ᶜ")
       ", "
       (Finset.Data.Finset.Fold.«term_*_»
        (Analysis.NormedSpace.LatticeOrderedGroup.«term|_|»
         "|"
         («term_-_» (Term.app `f [(Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ")]) "-" (Term.app `f [`x]))
         "|")
        "*"
        (Term.app `bernstein [`n `k `x])))
      "≤"
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
       " in "
       (Order.BooleanAlgebra.«term_ᶜ» `S "ᶜ")
       ", "
       (Finset.Data.Finset.Fold.«term_*_»
        (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
        "*"
        (Term.app `bernstein [`n `k `x]))))
     ":="
     (Term.app
      `Finset.sum_le_sum
      [(Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`k `m] [])]
         "=>"
         (Term.app
          `mul_le_mul_of_nonneg_right
          [(Term.app `f.dist_le_two_norm [(Term.hole "_") (Term.hole "_")]) `bernstein_nonneg])))]))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Finset.Data.Finset.Fold.«term_*_»
       (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
       "*"
       (Algebra.BigOperators.Basic.«term∑_in_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
        " in "
        (Order.BooleanAlgebra.«term_ᶜ» `S "ᶜ")
        ", "
        (Term.app `bernstein [`n `k `x]))))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.mul_sum)] "]") []) [])]))))
    (calcStep
     («term_≤_»
      (Term.hole "_")
      "≤"
      (Finset.Data.Finset.Fold.«term_*_»
       (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
       "*"
       (Algebra.BigOperators.Basic.«term∑_in_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
        " in "
        (Order.BooleanAlgebra.«term_ᶜ» `S "ᶜ")
        ", "
        (Finset.Data.Finset.Fold.«term_*_»
         (Finset.Data.Finset.Fold.«term_*_»
          (Cardinal.SetTheory.Cardinal.«term_^_»
           `δ
           "^"
           (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")"))
          "*"
          (Cardinal.SetTheory.Cardinal.«term_^_»
           («term_-_» `x "-" (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
           "^"
           (numLit "2")))
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
           [(Term.simpleBinder [`k `m] [])]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Mathlib.Tactic.Conv.convLHS
                 "conv_lhs"
                 []
                 []
                 "=>"
                 (Tactic.Conv.convSeq
                  (Tactic.Conv.convSeq1Indented
                   [(group
                     (Tactic.Conv.convRw__
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule
                         ["←"]
                         (Term.app
                          `one_mulₓ
                          [(Term.app `bernstein [(Term.hole "_") (Term.hole "_") (Term.hole "_")])]))]
                       "]"))
                     [])])))
                [])
               (group
                (Tactic.exact
                 "exact"
                 (Term.app `mul_le_mul_of_nonneg_right [(Term.app `le_of_mem_S_compl [`m]) `bernstein_nonneg]))
                [])])))))])
       `w₁]))
    (calcStep
     («term_≤_»
      (Term.hole "_")
      "≤"
      (Finset.Data.Finset.Fold.«term_*_»
       (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
       "*"
       (Algebra.BigOperators.Basic.«term∑_,_»
        "∑"
        (Lean.explicitBinders
         (Lean.unbracketedExplicitBinders
          [(Lean.binderIdent `k)]
          [":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])]))
        ", "
        (Finset.Data.Finset.Fold.«term_*_»
         (Finset.Data.Finset.Fold.«term_*_»
          (Cardinal.SetTheory.Cardinal.«term_^_»
           `δ
           "^"
           (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")"))
          "*"
          (Cardinal.SetTheory.Cardinal.«term_^_»
           («term_-_» `x "-" (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
           "^"
           (numLit "2")))
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
           [(Term.simpleBinder [`k] [])]
           "=>"
           (Term.app
            `mul_nonneg
            [(Term.app `mul_nonneg [`pow_minus_two_nonneg (Term.app `sq_nonneg [(Term.hole "_")])])
             `bernstein_nonneg])))])
       `w₁]))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Finset.Data.Finset.Fold.«term_*_»
       (Finset.Data.Finset.Fold.«term_*_»
        (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
        "*"
        (Cardinal.SetTheory.Cardinal.«term_^_»
         `δ
         "^"
         (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))
       "*"
       (Algebra.BigOperators.Basic.«term∑_,_»
        "∑"
        (Lean.explicitBinders
         (Lean.unbracketedExplicitBinders
          [(Lean.binderIdent `k)]
          [":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "1"))])]))
        ", "
        (Finset.Data.Finset.Fold.«term_*_»
         (Cardinal.SetTheory.Cardinal.«term_^_»
          («term_-_» `x "-" (Analysis.SpecialFunctions.Bernstein.«term_/ₙ» `k "/ₙ"))
          "^"
          (numLit "2"))
         "*"
         (Term.app `bernstein [`n `k `x])))))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Mathlib.Tactic.Conv.convRHS
           "conv_rhs"
           []
           []
           "=>"
           (Tactic.Conv.convSeq
            (Tactic.Conv.convSeq1Indented
             [(group
               (Tactic.Conv.convRw__
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_assocₓ) "," (Tactic.rwRule [] `Finset.mul_sum)] "]"))
               [])
              (group
               (Tactic.Conv.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] ["←"] `mul_assocₓ)] "]"] [])
               [])])))
          [])]))))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      («term_/_»
       (Finset.Data.Finset.Fold.«term_*_»
        (Finset.Data.Finset.Fold.«term_*_»
         (Finset.Data.Finset.Fold.«term_*_»
          (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
          "*"
          (Cardinal.SetTheory.Cardinal.«term_^_»
           `δ
           "^"
           (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))
         "*"
         `x)
        "*"
        («term_-_» (numLit "1") "-" `x))
       "/"
       `n))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `variance [`npos]))] "]") [])
          [])
         (group (Tactic.Ring.tacticRing "ring") [])]))))
    (calcStep
     («term_≤_»
      (Term.hole "_")
      "≤"
      («term_/_»
       (Finset.Data.Finset.Fold.«term_*_»
        (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
        "*"
        (Cardinal.SetTheory.Cardinal.«term_^_»
         `δ
         "^"
         (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))
       "/"
       `n))
     ":="
     (Term.app
      (Term.proj (Term.app `div_le_div_right [`npos]) "." `mpr)
      [(Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.apply "apply" (Term.app `mul_nonneg_le_one_le [`w₂])) [])
           (group
            (Tactic.apply "apply" (Term.app `mul_nonneg_le_one_le [`w₂ (Term.app `le_reflₓ [(Term.hole "_")])]))
            [])
           (group
            (Tactic.allGoals
             "all_goals"
             (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.unitInterval "unit_interval") [])])))
            [])])))]))
    (calcStep («term_<_» (Term.hole "_") "<" («term_/_» `ε "/" (numLit "2"))) ":=" `nh)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticCalc_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `nh
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_<_» (Term.hole "_") "<" («term_/_» `ε "/" (numLit "2")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_/_» `ε "/" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  `ε
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.app
   (Term.proj (Term.app `div_le_div_right [`npos]) "." `mpr)
   [(Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group (Tactic.apply "apply" (Term.app `mul_nonneg_le_one_le [`w₂])) [])
        (group (Tactic.apply "apply" (Term.app `mul_nonneg_le_one_le [`w₂ (Term.app `le_reflₓ [(Term.hole "_")])])) [])
        (group
         (Tactic.allGoals
          "all_goals"
          (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.unitInterval "unit_interval") [])])))
         [])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.apply "apply" (Term.app `mul_nonneg_le_one_le [`w₂])) [])
      (group (Tactic.apply "apply" (Term.app `mul_nonneg_le_one_le [`w₂ (Term.app `le_reflₓ [(Term.hole "_")])])) [])
      (group
       (Tactic.allGoals
        "all_goals"
        (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.unitInterval "unit_interval") [])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.allGoals
   "all_goals"
   (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.unitInterval "unit_interval") [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.allGoals', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.unitInterval "unit_interval")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.unitInterval', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply "apply" (Term.app `mul_nonneg_le_one_le [`w₂ (Term.app `le_reflₓ [(Term.hole "_")])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `mul_nonneg_le_one_le [`w₂ (Term.app `le_reflₓ [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `le_reflₓ [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `le_reflₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `le_reflₓ [(Term.hole "_")]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `w₂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mul_nonneg_le_one_le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply "apply" (Term.app `mul_nonneg_le_one_le [`w₂]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `mul_nonneg_le_one_le [`w₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `w₂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mul_nonneg_le_one_le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.apply "apply" (Term.app `mul_nonneg_le_one_le [`w₂])) [])
      (group
       (Tactic.apply
        "apply"
        (Term.app `mul_nonneg_le_one_le [`w₂ (Term.paren "(" [(Term.app `le_reflₓ [(Term.hole "_")]) []] ")")]))
       [])
      (group
       (Tactic.allGoals
        "all_goals"
        (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.unitInterval "unit_interval") [])])))
       [])])))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.app `div_le_div_right [`npos]) "." `mpr)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `div_le_div_right [`npos])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `npos
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `div_le_div_right
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `div_le_div_right [`npos]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (Term.hole "_")
   "≤"
   («term_/_»
    (Finset.Data.Finset.Fold.«term_*_»
     (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
     "*"
     (Cardinal.SetTheory.Cardinal.«term_^_»
      `δ
      "^"
      (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))
    "/"
    `n))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_/_»
   (Finset.Data.Finset.Fold.«term_*_»
    (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
    "*"
    (Cardinal.SetTheory.Cardinal.«term_^_»
     `δ
     "^"
     (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))
   "/"
   `n)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  (Finset.Data.Finset.Fold.«term_*_»
   (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
   "*"
   (Cardinal.SetTheory.Cardinal.«term_^_»
    `δ
    "^"
    (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Cardinal.SetTheory.Cardinal.«term_^_»
   `δ
   "^"
   (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cardinal.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (termℤ "ℤ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℤ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term-_» "-" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 100, (some 100, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  `δ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1024, (none, [anonymous]) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥")) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 0, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_»
   (Term.paren
    "("
    [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥")) []]
    ")")
   "*"
   (Cardinal.SetTheory.Cardinal.«term_^_»
    `δ
    "^"
    (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `variance [`npos]))] "]") []) [])
      (group (Tactic.Ring.tacticRing "ring") [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.Ring.tacticRing "ring")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Tactic.Ring.tacticRing', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `variance [`npos]))] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `variance [`npos])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `npos
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `variance
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.hole "_")
   "="
   («term_/_»
    (Finset.Data.Finset.Fold.«term_*_»
     (Finset.Data.Finset.Fold.«term_*_»
      (Finset.Data.Finset.Fold.«term_*_»
       (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
       "*"
       (Cardinal.SetTheory.Cardinal.«term_^_»
        `δ
        "^"
        (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))
      "*"
      `x)
     "*"
     («term_-_» (numLit "1") "-" `x))
    "/"
    `n))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_/_»
   (Finset.Data.Finset.Fold.«term_*_»
    (Finset.Data.Finset.Fold.«term_*_»
     (Finset.Data.Finset.Fold.«term_*_»
      (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
      "*"
      (Cardinal.SetTheory.Cardinal.«term_^_»
       `δ
       "^"
       (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))
     "*"
     `x)
    "*"
    («term_-_» (numLit "1") "-" `x))
   "/"
   `n)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  (Finset.Data.Finset.Fold.«term_*_»
   (Finset.Data.Finset.Fold.«term_*_»
    (Finset.Data.Finset.Fold.«term_*_»
     (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
     "*"
     (Cardinal.SetTheory.Cardinal.«term_^_»
      `δ
      "^"
      (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))
    "*"
    `x)
   "*"
   («term_-_» (numLit "1") "-" `x))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_-_» (numLit "1") "-" `x)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Finset.Data.Finset.Fold.«term_*_»
   (Finset.Data.Finset.Fold.«term_*_»
    (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
    "*"
    (Cardinal.SetTheory.Cardinal.«term_^_»
     `δ
     "^"
     (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))
   "*"
   `x)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Finset.Data.Finset.Fold.«term_*_»
   (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
   "*"
   (Cardinal.SetTheory.Cardinal.«term_^_»
    `δ
    "^"
    (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Cardinal.SetTheory.Cardinal.«term_^_»
   `δ
   "^"
   (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cardinal.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (termℤ "ℤ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℤ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term-_» "-" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 100, (some 100, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  `δ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1024, (none, [anonymous]) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥")) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_»
   (Term.paren
    "("
    [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥")) []]
    ")")
   "*"
   (Cardinal.SetTheory.Cardinal.«term_^_»
    `δ
    "^"
    (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_»
   (Term.paren
    "("
    [(Finset.Data.Finset.Fold.«term_*_»
      (Term.paren
       "("
       [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥")) []]
       ")")
      "*"
      (Cardinal.SetTheory.Cardinal.«term_^_»
       `δ
       "^"
       (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))
     []]
    ")")
   "*"
   `x)
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 0, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_»
   (Term.paren
    "("
    [(Finset.Data.Finset.Fold.«term_*_»
      (Term.paren
       "("
       [(Finset.Data.Finset.Fold.«term_*_»
         (Term.paren
          "("
          [(Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f "∥")) []]
          ")")
         "*"
         (Cardinal.SetTheory.Cardinal.«term_^_»
          `δ
          "^"
          (Term.paren "(" [(«term-_» "-" (numLit "2")) [(Term.typeAscription ":" (termℤ "ℤ"))]] ")")))
        []]
       ")")
      "*"
      `x)
     []]
    ")")
   "*"
   («term_-_» (numLit "1") "-" `x))
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Mathlib.Tactic.Conv.convRHS
        "conv_rhs"
        []
        []
        "=>"
        (Tactic.Conv.convSeq
         (Tactic.Conv.convSeq1Indented
          [(group
            (Tactic.Conv.convRw__
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_assocₓ) "," (Tactic.rwRule [] `Finset.mul_sum)] "]"))
            [])
           (group (Tactic.Conv.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] ["←"] `mul_assocₓ)] "]"] []) [])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Mathlib.Tactic.Conv.convRHS
   "conv_rhs"
   []
   []
   "=>"
   (Tactic.Conv.convSeq
    (Tactic.Conv.convSeq1Indented
     [(group
       (Tactic.Conv.convRw__
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_assocₓ) "," (Tactic.rwRule [] `Finset.mul_sum)] "]"))
       [])
      (group (Tactic.Conv.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] ["←"] `mul_assocₓ)] "]"] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Mathlib.Tactic.Conv.convRHS', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'Lean.Parser.Tactic.discharger'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.Conv.convSeq1Indented', expected 'Lean.Parser.Tactic.Conv.convSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
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
    ( f : C( I , ℝ ) ) : tendsto fun n : ℕ => bernsteinApproximation n f at_top 𝓝 f
    :=
      by
        simp only [ metric.nhds_basis_ball.tendsto_right_iff , Metric.mem_ball , dist_eq_norm ]
          intro ε h
          let δ := δ f ε h
          have nhds_zero := tendsto_const_div_at_top_nhds_0_nat 2 * ∥ f ∥ * δ ^ ( - 2 : ℤ )
          filter_upwards [ nhds_zero.eventually gt_mem_nhds half_pos h , eventually_gt_at_top 0 ]
          intro n nh npos'
          have npos : 0 < ( n : ℝ ) := by exact_mod_cast npos'
          have w₁ : 0 ≤ 2 * ∥ f ∥ := mul_nonneg by norm_num norm_nonneg f
          have w₂ : 0 ≤ 2 * ∥ f ∥ * δ ^ ( - 2 : ℤ ) := mul_nonneg w₁ pow_minus_two_nonneg
          rw [ ContinuousMap.norm_lt_iff _ h ]
          intro x
          let S := S f ε h n x
          calc
            | bernsteinApproximation n f - f x | = | bernsteinApproximation n f x - f x | := rfl
              _ = | bernsteinApproximation n f x - f x * 1 | := by rw [ mul_oneₓ ]
              _ = | bernsteinApproximation n f x - f x * ∑ k : Finₓ n + 1 , bernstein n k x |
                :=
                by rw [ bernstein.probability ]
              _ = | ∑ k : Finₓ n + 1 , f k /ₙ - f x * bernstein n k x |
                :=
                by simp [ bernsteinApproximation , Finset.mul_sum , sub_mul ]
              _ ≤ ∑ k : Finₓ n + 1 , | f k /ₙ - f x * bernstein n k x | := Finset.abs_sum_le_sum_abs _ _
              _ = ∑ k : Finₓ n + 1 , | f k /ₙ - f x | * bernstein n k x
                :=
                by simp_rw [ abs_mul , abs_eq_self.mpr bernstein_nonneg ]
              _ = ∑ k in S , | f k /ₙ - f x | * bernstein n k x + ∑ k in S ᶜ , | f k /ₙ - f x | * bernstein n k x
                :=
                S.sum_add_sum_compl _ . symm
              _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt _ _
              _ = ε := add_halves ε
          ·
            calc
              ∑ k in S , | f k /ₙ - f x | * bernstein n k x ≤ ∑ k in S , ε / 2 * bernstein n k x
                  :=
                  Finset.sum_le_sum fun k m => mul_le_mul_of_nonneg_right le_of_ltₓ lt_of_mem_S m bernstein_nonneg
                _ = ε / 2 * ∑ k in S , bernstein n k x := by rw [ Finset.mul_sum ]
                _ ≤ ε / 2 * ∑ k : Finₓ n + 1 , bernstein n k x
                  :=
                  mul_le_mul_of_nonneg_left
                    Finset.sum_le_univ_sum_of_nonneg fun k => bernstein_nonneg le_of_ltₓ half_pos h
                _ = ε / 2 := by rw [ bernstein.probability , mul_oneₓ ]
          ·
            calc
              ∑ k in S ᶜ , | f k /ₙ - f x | * bernstein n k x ≤ ∑ k in S ᶜ , 2 * ∥ f ∥ * bernstein n k x
                  :=
                  Finset.sum_le_sum fun k m => mul_le_mul_of_nonneg_right f.dist_le_two_norm _ _ bernstein_nonneg
                _ = 2 * ∥ f ∥ * ∑ k in S ᶜ , bernstein n k x := by rw [ Finset.mul_sum ]
                _ ≤ 2 * ∥ f ∥ * ∑ k in S ᶜ , δ ^ ( - 2 : ℤ ) * x - k /ₙ ^ 2 * bernstein n k x
                  :=
                  mul_le_mul_of_nonneg_left
                    Finset.sum_le_sum
                        fun
                          k m
                            =>
                            by
                              conv_lhs => rw [ ← one_mulₓ bernstein _ _ _ ]
                                exact mul_le_mul_of_nonneg_right le_of_mem_S_compl m bernstein_nonneg
                      w₁
                _ ≤ 2 * ∥ f ∥ * ∑ k : Finₓ n + 1 , δ ^ ( - 2 : ℤ ) * x - k /ₙ ^ 2 * bernstein n k x
                  :=
                  mul_le_mul_of_nonneg_left
                    Finset.sum_le_univ_sum_of_nonneg
                        fun k => mul_nonneg mul_nonneg pow_minus_two_nonneg sq_nonneg _ bernstein_nonneg
                      w₁
                _ = 2 * ∥ f ∥ * δ ^ ( - 2 : ℤ ) * ∑ k : Finₓ n + 1 , x - k /ₙ ^ 2 * bernstein n k x
                  :=
                  by conv_rhs => rw [ mul_assocₓ , Finset.mul_sum ] simp only [ ← mul_assocₓ ]
                _ = 2 * ∥ f ∥ * δ ^ ( - 2 : ℤ ) * x * 1 - x / n := by rw [ variance npos ] ring
                _ ≤ 2 * ∥ f ∥ * δ ^ ( - 2 : ℤ ) / n
                  :=
                  div_le_div_right npos . mpr
                    by apply mul_nonneg_le_one_le w₂ apply mul_nonneg_le_one_le w₂ le_reflₓ _ all_goals unit_interval
                _ < ε / 2 := nh

