import Mathbin.Analysis.SpecificLimits
import Mathbin.Analysis.Analytic.Basic
import Mathbin.Analysis.Complex.Basic
import Mathbin.Data.Nat.Choose.Cast

/-!
# Exponential in a Banach algebra

In this file, we define `exp 𝕂 𝔸`, the exponential map in a normed algebra `𝔸` over a nondiscrete
normed field `𝕂`. Although the definition doesn't require `𝔸` to be complete, we need to assume it
for most results.

We then prove some basic results, but we avoid importing derivatives here to minimize dependencies.
Results involving derivatives and comparisons with `real.exp` and `complex.exp` can be found in
`analysis/special_functions/exponential`.

## Main results

We prove most result for an arbitrary field `𝕂`, and then specialize to `𝕂 = ℝ` or `𝕂 = ℂ`.

### General case

- `exp_add_of_commute_of_lt_radius` : if `𝕂` has characteristic zero, then given two commuting
  elements `x` and `y` in the disk of convergence, we have
  `exp 𝕂 𝔸 (x+y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)`
- `exp_add_of_lt_radius` : if `𝕂` has characteristic zero and `𝔸` is commutative, then given two
  elements `x` and `y` in the disk of convergence, we have
  `exp 𝕂 𝔸 (x+y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)`

### `𝕂 = ℝ` or `𝕂 = ℂ`

- `exp_series_radius_eq_top` : the `formal_multilinear_series` defining `exp 𝕂 𝔸` has infinite
  radius of convergence
- `exp_add_of_commute` : given two commuting elements `x` and `y`, we have
  `exp 𝕂 𝔸 (x+y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)`
- `exp_add` : if `𝔸` is commutative, then we have `exp 𝕂 𝔸 (x+y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)`
  for any `x` and `y`

### Other useful compatibility results

- `exp_eq_exp` : if `𝔸` is a normed algebra over two fields `𝕂` and `𝕂'`, then `exp 𝕂 𝔸 = exp 𝕂' 𝔸`

-/


open Filter IsROrC ContinuousMultilinearMap NormedField Asymptotics

open_locale Nat TopologicalSpace BigOperators Ennreal

section AnyFieldAnyAlgebra

variable (𝕂 𝔸 : Type _) [NondiscreteNormedField 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]

/--  In a Banach algebra `𝔸` over a normed field `𝕂`, `exp_series 𝕂 𝔸` is the
`formal_multilinear_series` whose `n`-th term is the map `(xᵢ) : 𝔸ⁿ ↦ (1/n! : 𝕂) • ∏ xᵢ`.
Its sum is the exponential map `exp 𝕂 𝔸 : 𝔸 → 𝔸`. -/
def expSeries : FormalMultilinearSeries 𝕂 𝔸 𝔸 := fun n => (1 / n ! : 𝕂) • ContinuousMultilinearMap.mkPiAlgebraFin 𝕂 n 𝔸

/--  In a Banach algebra `𝔸` over a normed field `𝕂`, `exp 𝕂 𝔸 : 𝔸 → 𝔸` is the exponential map
determined by the action of `𝕂` on `𝔸`.
It is defined as the sum of the `formal_multilinear_series` `exp_series 𝕂 𝔸`. -/
noncomputable def exp (x : 𝔸) : 𝔸 :=
  (expSeries 𝕂 𝔸).Sum x

variable {𝕂 𝔸}

theorem exp_series_apply_eq (x : 𝔸) (n : ℕ) : (expSeries 𝕂 𝔸 n fun _ => x) = (1 / n ! : 𝕂) • (x^n) := by
  simp [expSeries]

theorem exp_series_apply_eq' (x : 𝔸) : (fun n => expSeries 𝕂 𝔸 n fun _ => x) = fun n => (1 / n ! : 𝕂) • (x^n) :=
  funext (exp_series_apply_eq x)

theorem exp_series_apply_eq_field (x : 𝕂) (n : ℕ) : (expSeries 𝕂 𝕂 n fun _ => x) = (x^n) / n ! := by
  rw [div_eq_inv_mul, ← smul_eq_mul, inv_eq_one_div]
  exact exp_series_apply_eq x n

theorem exp_series_apply_eq_field' (x : 𝕂) : (fun n => expSeries 𝕂 𝕂 n fun _ => x) = fun n => (x^n) / n ! :=
  funext (exp_series_apply_eq_field x)

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `exp_series_sum_eq [])
  (Command.declSig
   [(Term.explicitBinder "(" [`x] [":" `𝔸] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app (Term.proj (Term.app `expSeries [`𝕂 `𝔸]) "." `Sum) [`x])
     "="
     (Topology.Algebra.InfiniteSum.«term∑'_,_»
      "∑'"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (termℕ "ℕ")]))
      ", "
      (Algebra.Group.Defs.«term_•_»
       (Term.paren
        "("
        [(«term_/_» (numLit "1") "/" (Nat.Data.Nat.Factorial.Basic.term_! `n "!")) [(Term.typeAscription ":" `𝕂)]]
        ")")
       " • "
       (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `n))))))
  (Command.declValSimple
   ":="
   (Term.app
    `tsum_congr
    [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.app `exp_series_apply_eq [`x `n])))])
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
  (Term.app
   `tsum_congr
   [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.app `exp_series_apply_eq [`x `n])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.app `exp_series_apply_eq [`x `n])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `exp_series_apply_eq [`x `n])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `exp_series_apply_eq
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `tsum_congr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.app (Term.proj (Term.app `expSeries [`𝕂 `𝔸]) "." `Sum) [`x])
   "="
   (Topology.Algebra.InfiniteSum.«term∑'_,_»
    "∑'"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (termℕ "ℕ")]))
    ", "
    (Algebra.Group.Defs.«term_•_»
     (Term.paren
      "("
      [(«term_/_» (numLit "1") "/" (Nat.Data.Nat.Factorial.Basic.term_! `n "!")) [(Term.typeAscription ":" `𝕂)]]
      ")")
     " • "
     (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `n))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Topology.Algebra.InfiniteSum.«term∑'_,_»
   "∑'"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (termℕ "ℕ")]))
   ", "
   (Algebra.Group.Defs.«term_•_»
    (Term.paren
     "("
     [(«term_/_» (numLit "1") "/" (Nat.Data.Nat.Factorial.Basic.term_! `n "!")) [(Term.typeAscription ":" `𝕂)]]
     ")")
    " • "
    (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `n)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Algebra.InfiniteSum.«term∑'_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.Group.Defs.«term_•_»
   (Term.paren
    "("
    [(«term_/_» (numLit "1") "/" (Nat.Data.Nat.Factorial.Basic.term_! `n "!")) [(Term.typeAscription ":" `𝕂)]]
    ")")
   " • "
   (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `n))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `n)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1024, (none, [anonymous]) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 73 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `n) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
  (Term.paren
   "("
   [(«term_/_» (numLit "1") "/" (Nat.Data.Nat.Factorial.Basic.term_! `n "!")) [(Term.typeAscription ":" `𝕂)]]
   ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `𝕂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_/_» (numLit "1") "/" (Nat.Data.Nat.Factorial.Basic.term_! `n "!"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Nat.Data.Nat.Factorial.Basic.term_! `n "!")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Nat.Data.Nat.Factorial.Basic.term_!', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10000, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10000, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 10000, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 73, term) <=? (none, [anonymous])
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
  exp_series_sum_eq
  ( x : 𝔸 ) : expSeries 𝕂 𝔸 . Sum x = ∑' n : ℕ , ( 1 / n ! : 𝕂 ) • x ^ n
  := tsum_congr fun n => exp_series_apply_eq x n

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `exp_series_sum_eq_field [])
  (Command.declSig
   [(Term.explicitBinder "(" [`x] [":" `𝕂] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app (Term.proj (Term.app `expSeries [`𝕂 `𝕂]) "." `Sum) [`x])
     "="
     (Topology.Algebra.InfiniteSum.«term∑'_,_»
      "∑'"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (termℕ "ℕ")]))
      ", "
      («term_/_»
       (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `n)
       "/"
       (Nat.Data.Nat.Factorial.Basic.term_! `n "!"))))))
  (Command.declValSimple
   ":="
   (Term.app
    `tsum_congr
    [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.app `exp_series_apply_eq_field [`x `n])))])
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
  (Term.app
   `tsum_congr
   [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.app `exp_series_apply_eq_field [`x `n])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.app `exp_series_apply_eq_field [`x `n])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `exp_series_apply_eq_field [`x `n])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `exp_series_apply_eq_field
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `tsum_congr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.app (Term.proj (Term.app `expSeries [`𝕂 `𝕂]) "." `Sum) [`x])
   "="
   (Topology.Algebra.InfiniteSum.«term∑'_,_»
    "∑'"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (termℕ "ℕ")]))
    ", "
    («term_/_» (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `n) "/" (Nat.Data.Nat.Factorial.Basic.term_! `n "!"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Topology.Algebra.InfiniteSum.«term∑'_,_»
   "∑'"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (termℕ "ℕ")]))
   ", "
   («term_/_» (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `n) "/" (Nat.Data.Nat.Factorial.Basic.term_! `n "!")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Algebra.InfiniteSum.«term∑'_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_/_» (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `n) "/" (Nat.Data.Nat.Factorial.Basic.term_! `n "!"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Nat.Data.Nat.Factorial.Basic.term_! `n "!")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Nat.Data.Nat.Factorial.Basic.term_!', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10000, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10000, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 10000, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `n)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1024, (none, [anonymous]) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 0, (some 0, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `n) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
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
  exp_series_sum_eq_field
  ( x : 𝕂 ) : expSeries 𝕂 𝕂 . Sum x = ∑' n : ℕ , x ^ n / n !
  := tsum_congr fun n => exp_series_apply_eq_field x n

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `exp_eq_tsum [])
  (Command.declSig
   []
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app `exp [`𝕂 `𝔸])
     "="
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`x] [(Term.typeSpec ":" `𝔸)])]
       "=>"
       (Topology.Algebra.InfiniteSum.«term∑'_,_»
        "∑'"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (termℕ "ℕ")]))
        ", "
        (Algebra.Group.Defs.«term_•_»
         (Term.paren
          "("
          [(«term_/_» (numLit "1") "/" (Nat.Data.Nat.Factorial.Basic.term_! `n "!")) [(Term.typeAscription ":" `𝕂)]]
          ")")
         " • "
         (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `n))))))))
  (Command.declValSimple ":=" (Term.app `funext [`exp_series_sum_eq]) [])
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
  (Term.app `funext [`exp_series_sum_eq])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `exp_series_sum_eq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `funext
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.app `exp [`𝕂 `𝔸])
   "="
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`x] [(Term.typeSpec ":" `𝔸)])]
     "=>"
     (Topology.Algebra.InfiniteSum.«term∑'_,_»
      "∑'"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (termℕ "ℕ")]))
      ", "
      (Algebra.Group.Defs.«term_•_»
       (Term.paren
        "("
        [(«term_/_» (numLit "1") "/" (Nat.Data.Nat.Factorial.Basic.term_! `n "!")) [(Term.typeAscription ":" `𝕂)]]
        ")")
       " • "
       (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `n))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`x] [(Term.typeSpec ":" `𝔸)])]
    "=>"
    (Topology.Algebra.InfiniteSum.«term∑'_,_»
     "∑'"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (termℕ "ℕ")]))
     ", "
     (Algebra.Group.Defs.«term_•_»
      (Term.paren
       "("
       [(«term_/_» (numLit "1") "/" (Nat.Data.Nat.Factorial.Basic.term_! `n "!")) [(Term.typeAscription ":" `𝕂)]]
       ")")
      " • "
      (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `n)))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Topology.Algebra.InfiniteSum.«term∑'_,_»
   "∑'"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (termℕ "ℕ")]))
   ", "
   (Algebra.Group.Defs.«term_•_»
    (Term.paren
     "("
     [(«term_/_» (numLit "1") "/" (Nat.Data.Nat.Factorial.Basic.term_! `n "!")) [(Term.typeAscription ":" `𝕂)]]
     ")")
    " • "
    (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `n)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Algebra.InfiniteSum.«term∑'_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.Group.Defs.«term_•_»
   (Term.paren
    "("
    [(«term_/_» (numLit "1") "/" (Nat.Data.Nat.Factorial.Basic.term_! `n "!")) [(Term.typeAscription ":" `𝕂)]]
    ")")
   " • "
   (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `n))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `n)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1024, (none, [anonymous]) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 73 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `n) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
  (Term.paren
   "("
   [(«term_/_» (numLit "1") "/" (Nat.Data.Nat.Factorial.Basic.term_! `n "!")) [(Term.typeAscription ":" `𝕂)]]
   ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `𝕂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_/_» (numLit "1") "/" (Nat.Data.Nat.Factorial.Basic.term_! `n "!"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Nat.Data.Nat.Factorial.Basic.term_! `n "!")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Nat.Data.Nat.Factorial.Basic.term_!', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10000, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10000, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 10000, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1024, (none, [anonymous]) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
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
theorem exp_eq_tsum : exp 𝕂 𝔸 = fun x : 𝔸 => ∑' n : ℕ , ( 1 / n ! : 𝕂 ) • x ^ n := funext exp_series_sum_eq

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `exp_eq_tsum_field [])
  (Command.declSig
   []
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app `exp [`𝕂 `𝕂])
     "="
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`x] [(Term.typeSpec ":" `𝕂)])]
       "=>"
       (Topology.Algebra.InfiniteSum.«term∑'_,_»
        "∑'"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (termℕ "ℕ")]))
        ", "
        («term_/_»
         (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `n)
         "/"
         (Nat.Data.Nat.Factorial.Basic.term_! `n "!"))))))))
  (Command.declValSimple ":=" (Term.app `funext [`exp_series_sum_eq_field]) [])
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
  (Term.app `funext [`exp_series_sum_eq_field])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `exp_series_sum_eq_field
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `funext
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.app `exp [`𝕂 `𝕂])
   "="
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`x] [(Term.typeSpec ":" `𝕂)])]
     "=>"
     (Topology.Algebra.InfiniteSum.«term∑'_,_»
      "∑'"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (termℕ "ℕ")]))
      ", "
      («term_/_»
       (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `n)
       "/"
       (Nat.Data.Nat.Factorial.Basic.term_! `n "!"))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`x] [(Term.typeSpec ":" `𝕂)])]
    "=>"
    (Topology.Algebra.InfiniteSum.«term∑'_,_»
     "∑'"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (termℕ "ℕ")]))
     ", "
     («term_/_» (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `n) "/" (Nat.Data.Nat.Factorial.Basic.term_! `n "!")))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Topology.Algebra.InfiniteSum.«term∑'_,_»
   "∑'"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (termℕ "ℕ")]))
   ", "
   («term_/_» (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `n) "/" (Nat.Data.Nat.Factorial.Basic.term_! `n "!")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Algebra.InfiniteSum.«term∑'_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_/_» (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `n) "/" (Nat.Data.Nat.Factorial.Basic.term_! `n "!"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Nat.Data.Nat.Factorial.Basic.term_! `n "!")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Nat.Data.Nat.Factorial.Basic.term_!', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10000, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10000, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 10000, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `n)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1024, (none, [anonymous]) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 0, (some 0, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `n) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
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
theorem exp_eq_tsum_field : exp 𝕂 𝕂 = fun x : 𝕂 => ∑' n : ℕ , x ^ n / n ! := funext exp_series_sum_eq_field

-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (n «expr ∉ » ({0} : finset exprℕ()))
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `exp_zero [])
  (Command.declSig [] (Term.typeSpec ":" («term_=_» (Term.app `exp [`𝕂 `𝔸 (numLit "0")]) "=" (numLit "1"))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.tacticSuffices_
         "suffices"
         (Term.sufficesDecl
          []
          («term_=_»
           (Term.app
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`x] [(Term.typeSpec ":" `𝔸)])]
              "=>"
              (Topology.Algebra.InfiniteSum.«term∑'_,_»
               "∑'"
               (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (termℕ "ℕ")]))
               ", "
               (Algebra.Group.Defs.«term_•_»
                (Term.paren
                 "("
                 [(«term_/_» (numLit "1") "/" (Nat.Data.Nat.Factorial.Basic.term_! `n "!"))
                  [(Term.typeAscription ":" `𝕂)]]
                 ")")
                " • "
                (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `n)))))
            [(numLit "0")])
           "="
           (Topology.Algebra.InfiniteSum.«term∑'_,_»
            "∑'"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (termℕ "ℕ")]))
            ", "
            (termIfThenElse "if" («term_=_» `n "=" (numLit "0")) "then" (numLit "1") "else" (numLit "0"))))
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.have''
                "have"
                [`key []]
                [(Term.typeSpec
                  ":"
                  (Term.forall
                   "∀"
                   [(Term.simpleBinder [`n] [])
                    (Term.simpleBinder
                     [(Term.hole "_")]
                     [(Term.typeSpec
                       ":"
                       (Init.Core.«term_∉_»
                        `n
                        " ∉ "
                        (Term.paren
                         "("
                         [(Set.«term{_}» "{" [(numLit "0")] "}")
                          [(Term.typeAscription ":" (Term.app `Finset [(termℕ "ℕ")]))]]
                         ")")))])]
                   ","
                   («term_=_»
                    (termIfThenElse
                     "if"
                     («term_=_» `n "=" (numLit "0"))
                     "then"
                     (Term.paren "(" [(numLit "1") [(Term.typeAscription ":" `𝔸)]] ")")
                     "else"
                     (numLit "0"))
                    "="
                    (numLit "0"))))])
               [])
              (group
               (Tactic.exact
                "exact"
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`n `hn] [])]
                  "=>"
                  (Term.app `if_neg [(Term.app `finset.not_mem_singleton.mp [`hn])]))))
               [])
              (group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `exp_eq_tsum)
                  ","
                  (Tactic.rwRule [] `this)
                  ","
                  (Tactic.rwRule [] (Term.app `tsum_eq_sum [`key]))
                  ","
                  (Tactic.rwRule [] `Finset.sum_singleton)]
                 "]")
                [])
               [])
              (group (Tactic.simp "simp" [] [] [] []) [])])))))
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.app `tsum_congr [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.hole "_")))]))
        [])
       (group
        (Tactic.«tactic_<;>_»
         (Tactic.splitIfs "split_ifs" [] ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h)]])
         "<;>"
         (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] []))
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
       (Tactic.tacticSuffices_
        "suffices"
        (Term.sufficesDecl
         []
         («term_=_»
          (Term.app
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`x] [(Term.typeSpec ":" `𝔸)])]
             "=>"
             (Topology.Algebra.InfiniteSum.«term∑'_,_»
              "∑'"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (termℕ "ℕ")]))
              ", "
              (Algebra.Group.Defs.«term_•_»
               (Term.paren
                "("
                [(«term_/_» (numLit "1") "/" (Nat.Data.Nat.Factorial.Basic.term_! `n "!"))
                 [(Term.typeAscription ":" `𝕂)]]
                ")")
               " • "
               (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `n)))))
           [(numLit "0")])
          "="
          (Topology.Algebra.InfiniteSum.«term∑'_,_»
           "∑'"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (termℕ "ℕ")]))
           ", "
           (termIfThenElse "if" («term_=_» `n "=" (numLit "0")) "then" (numLit "1") "else" (numLit "0"))))
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group
              (Tactic.have''
               "have"
               [`key []]
               [(Term.typeSpec
                 ":"
                 (Term.forall
                  "∀"
                  [(Term.simpleBinder [`n] [])
                   (Term.simpleBinder
                    [(Term.hole "_")]
                    [(Term.typeSpec
                      ":"
                      (Init.Core.«term_∉_»
                       `n
                       " ∉ "
                       (Term.paren
                        "("
                        [(Set.«term{_}» "{" [(numLit "0")] "}")
                         [(Term.typeAscription ":" (Term.app `Finset [(termℕ "ℕ")]))]]
                        ")")))])]
                  ","
                  («term_=_»
                   (termIfThenElse
                    "if"
                    («term_=_» `n "=" (numLit "0"))
                    "then"
                    (Term.paren "(" [(numLit "1") [(Term.typeAscription ":" `𝔸)]] ")")
                    "else"
                    (numLit "0"))
                   "="
                   (numLit "0"))))])
              [])
             (group
              (Tactic.exact
               "exact"
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`n `hn] [])]
                 "=>"
                 (Term.app `if_neg [(Term.app `finset.not_mem_singleton.mp [`hn])]))))
              [])
             (group
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `exp_eq_tsum)
                 ","
                 (Tactic.rwRule [] `this)
                 ","
                 (Tactic.rwRule [] (Term.app `tsum_eq_sum [`key]))
                 ","
                 (Tactic.rwRule [] `Finset.sum_singleton)]
                "]")
               [])
              [])
             (group (Tactic.simp "simp" [] [] [] []) [])])))))
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app `tsum_congr [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.hole "_")))]))
       [])
      (group
       (Tactic.«tactic_<;>_»
        (Tactic.splitIfs "split_ifs" [] ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h)]])
        "<;>"
        (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] []))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic_<;>_»
   (Tactic.splitIfs "split_ifs" [] ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h)]])
   "<;>"
   (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic_<;>_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
  (Tactic.splitIfs "split_ifs" [] ["with" [(Lean.binderIdent `h) (Lean.binderIdent `h)]])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.splitIfs', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.binderIdent', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.binderIdent', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app `tsum_congr [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `tsum_congr [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `tsum_congr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticSuffices_
   "suffices"
   (Term.sufficesDecl
    []
    («term_=_»
     (Term.app
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`x] [(Term.typeSpec ":" `𝔸)])]
        "=>"
        (Topology.Algebra.InfiniteSum.«term∑'_,_»
         "∑'"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (termℕ "ℕ")]))
         ", "
         (Algebra.Group.Defs.«term_•_»
          (Term.paren
           "("
           [(«term_/_» (numLit "1") "/" (Nat.Data.Nat.Factorial.Basic.term_! `n "!")) [(Term.typeAscription ":" `𝕂)]]
           ")")
          " • "
          (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `n)))))
      [(numLit "0")])
     "="
     (Topology.Algebra.InfiniteSum.«term∑'_,_»
      "∑'"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (termℕ "ℕ")]))
      ", "
      (termIfThenElse "if" («term_=_» `n "=" (numLit "0")) "then" (numLit "1") "else" (numLit "0"))))
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group
         (Tactic.have''
          "have"
          [`key []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`n] [])
              (Term.simpleBinder
               [(Term.hole "_")]
               [(Term.typeSpec
                 ":"
                 (Init.Core.«term_∉_»
                  `n
                  " ∉ "
                  (Term.paren
                   "("
                   [(Set.«term{_}» "{" [(numLit "0")] "}") [(Term.typeAscription ":" (Term.app `Finset [(termℕ "ℕ")]))]]
                   ")")))])]
             ","
             («term_=_»
              (termIfThenElse
               "if"
               («term_=_» `n "=" (numLit "0"))
               "then"
               (Term.paren "(" [(numLit "1") [(Term.typeAscription ":" `𝔸)]] ")")
               "else"
               (numLit "0"))
              "="
              (numLit "0"))))])
         [])
        (group
         (Tactic.exact
          "exact"
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`n `hn] [])]
            "=>"
            (Term.app `if_neg [(Term.app `finset.not_mem_singleton.mp [`hn])]))))
         [])
        (group
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule [] `exp_eq_tsum)
            ","
            (Tactic.rwRule [] `this)
            ","
            (Tactic.rwRule [] (Term.app `tsum_eq_sum [`key]))
            ","
            (Tactic.rwRule [] `Finset.sum_singleton)]
           "]")
          [])
         [])
        (group (Tactic.simp "simp" [] [] [] []) [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSuffices_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.sufficesDecl', expected 'Lean.Parser.Term.sufficesDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.fromTerm.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp "simp" [] [] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] `exp_eq_tsum)
     ","
     (Tactic.rwRule [] `this)
     ","
     (Tactic.rwRule [] (Term.app `tsum_eq_sum [`key]))
     ","
     (Tactic.rwRule [] `Finset.sum_singleton)]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.sum_singleton
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `tsum_eq_sum [`key])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `key
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `tsum_eq_sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `exp_eq_tsum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.exact
   "exact"
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`n `hn] [])]
     "=>"
     (Term.app `if_neg [(Term.app `finset.not_mem_singleton.mp [`hn])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`n `hn] [])]
    "=>"
    (Term.app `if_neg [(Term.app `finset.not_mem_singleton.mp [`hn])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `if_neg [(Term.app `finset.not_mem_singleton.mp [`hn])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `finset.not_mem_singleton.mp [`hn])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hn
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `finset.not_mem_singleton.mp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `finset.not_mem_singleton.mp [`hn]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `if_neg
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.have''
   "have"
   [`key []]
   [(Term.typeSpec
     ":"
     (Term.forall
      "∀"
      [(Term.simpleBinder [`n] [])
       (Term.simpleBinder
        [(Term.hole "_")]
        [(Term.typeSpec
          ":"
          (Init.Core.«term_∉_»
           `n
           " ∉ "
           (Term.paren
            "("
            [(Set.«term{_}» "{" [(numLit "0")] "}") [(Term.typeAscription ":" (Term.app `Finset [(termℕ "ℕ")]))]]
            ")")))])]
      ","
      («term_=_»
       (termIfThenElse
        "if"
        («term_=_» `n "=" (numLit "0"))
        "then"
        (Term.paren "(" [(numLit "1") [(Term.typeAscription ":" `𝔸)]] ")")
        "else"
        (numLit "0"))
       "="
       (numLit "0"))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.have''', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder [`n] [])
    (Term.simpleBinder
     [(Term.hole "_")]
     [(Term.typeSpec
       ":"
       (Init.Core.«term_∉_»
        `n
        " ∉ "
        (Term.paren
         "("
         [(Set.«term{_}» "{" [(numLit "0")] "}") [(Term.typeAscription ":" (Term.app `Finset [(termℕ "ℕ")]))]]
         ")")))])]
   ","
   («term_=_»
    (termIfThenElse
     "if"
     («term_=_» `n "=" (numLit "0"))
     "then"
     (Term.paren "(" [(numLit "1") [(Term.typeAscription ":" `𝔸)]] ")")
     "else"
     (numLit "0"))
    "="
    (numLit "0")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (termIfThenElse
    "if"
    («term_=_» `n "=" (numLit "0"))
    "then"
    (Term.paren "(" [(numLit "1") [(Term.typeAscription ":" `𝔸)]] ")")
    "else"
    (numLit "0"))
   "="
   (numLit "0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (termIfThenElse
   "if"
   («term_=_» `n "=" (numLit "0"))
   "then"
   (Term.paren "(" [(numLit "1") [(Term.typeAscription ":" `𝔸)]] ")")
   "else"
   (numLit "0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termIfThenElse', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren "(" [(numLit "1") [(Term.typeAscription ":" `𝔸)]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `𝔸
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» `n "=" (numLit "0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(termIfThenElse
   "if"
   («term_=_» `n "=" (numLit "0"))
   "then"
   (Term.paren "(" [(numLit "1") [(Term.typeAscription ":" `𝔸)]] ")")
   "else"
   (numLit "0"))
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Core.«term_∉_»
   `n
   " ∉ "
   (Term.paren
    "("
    [(Set.«term{_}» "{" [(numLit "0")] "}") [(Term.typeAscription ":" (Term.app `Finset [(termℕ "ℕ")]))]]
    ")"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∉_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren
   "("
   [(Set.«term{_}» "{" [(numLit "0")] "}") [(Term.typeAscription ":" (Term.app `Finset [(termℕ "ℕ")]))]]
   ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Finset [(termℕ "ℕ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (termℕ "ℕ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finset
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Set.«term{_}» "{" [(numLit "0")] "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_}»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 50, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, [anonymous]))
  («term_=_»
   (Term.app
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`x] [(Term.typeSpec ":" `𝔸)])]
      "=>"
      (Topology.Algebra.InfiniteSum.«term∑'_,_»
       "∑'"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (termℕ "ℕ")]))
       ", "
       (Algebra.Group.Defs.«term_•_»
        (Term.paren
         "("
         [(«term_/_» (numLit "1") "/" (Nat.Data.Nat.Factorial.Basic.term_! `n "!")) [(Term.typeAscription ":" `𝕂)]]
         ")")
        " • "
        (Cardinal.SetTheory.Cofinality.«term_^_» `x "^" `n)))))
    [(numLit "0")])
   "="
   (Topology.Algebra.InfiniteSum.«term∑'_,_»
    "∑'"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (termℕ "ℕ")]))
    ", "
    (termIfThenElse "if" («term_=_» `n "=" (numLit "0")) "then" (numLit "1") "else" (numLit "0"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Topology.Algebra.InfiniteSum.«term∑'_,_»
   "∑'"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (termℕ "ℕ")]))
   ", "
   (termIfThenElse "if" («term_=_» `n "=" (numLit "0")) "then" (numLit "1") "else" (numLit "0")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Algebra.InfiniteSum.«term∑'_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (termIfThenElse "if" («term_=_» `n "=" (numLit "0")) "then" (numLit "1") "else" (numLit "0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termIfThenElse', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» `n "=" (numLit "0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
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
  exp_zero
  : exp 𝕂 𝔸 0 = 1
  :=
    by
      suffices
          fun x : 𝔸 => ∑' n : ℕ , ( 1 / n ! : 𝕂 ) • x ^ n 0 = ∑' n : ℕ , if n = 0 then 1 else 0
            by
              have key : ∀ n _ : n ∉ ( { 0 } : Finset ℕ ) , if n = 0 then ( 1 : 𝔸 ) else 0 = 0
                exact fun n hn => if_neg finset.not_mem_singleton.mp hn
                rw [ exp_eq_tsum , this , tsum_eq_sum key , Finset.sum_singleton ]
                simp
        refine' tsum_congr fun n => _
        split_ifs with h h <;> simp [ h ]

theorem norm_exp_series_summable_of_mem_ball (x : 𝔸) (hx : x ∈ Emetric.Ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    Summable fun n => ∥expSeries 𝕂 𝔸 n fun _ => x∥ :=
  (expSeries 𝕂 𝔸).summable_norm_apply hx

theorem norm_exp_series_summable_of_mem_ball' (x : 𝔸) (hx : x ∈ Emetric.Ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    Summable fun n => ∥(1 / n ! : 𝕂) • (x^n)∥ := by
  change Summable (norm ∘ _)
  rw [← exp_series_apply_eq']
  exact norm_exp_series_summable_of_mem_ball x hx

theorem norm_exp_series_field_summable_of_mem_ball (x : 𝕂) (hx : x ∈ Emetric.Ball (0 : 𝕂) (expSeries 𝕂 𝕂).radius) :
    Summable fun n => ∥(x^n) / n !∥ := by
  change Summable (norm ∘ _)
  rw [← exp_series_apply_eq_field']
  exact norm_exp_series_summable_of_mem_ball x hx

section CompleteAlgebra

variable [CompleteSpace 𝔸]

theorem exp_series_summable_of_mem_ball (x : 𝔸) (hx : x ∈ Emetric.Ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    Summable fun n => expSeries 𝕂 𝔸 n fun _ => x :=
  summable_of_summable_norm (norm_exp_series_summable_of_mem_ball x hx)

theorem exp_series_summable_of_mem_ball' (x : 𝔸) (hx : x ∈ Emetric.Ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    Summable fun n => (1 / n ! : 𝕂) • (x^n) :=
  summable_of_summable_norm (norm_exp_series_summable_of_mem_ball' x hx)

theorem exp_series_field_summable_of_mem_ball [CompleteSpace 𝕂] (x : 𝕂)
    (hx : x ∈ Emetric.Ball (0 : 𝕂) (expSeries 𝕂 𝕂).radius) : Summable fun n => (x^n) / n ! :=
  summable_of_summable_norm (norm_exp_series_field_summable_of_mem_ball x hx)

theorem exp_series_has_sum_exp_of_mem_ball (x : 𝔸) (hx : x ∈ Emetric.Ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasSum (fun n => expSeries 𝕂 𝔸 n fun _ => x) (exp 𝕂 𝔸 x) :=
  FormalMultilinearSeries.has_sum (expSeries 𝕂 𝔸) hx

theorem exp_series_has_sum_exp_of_mem_ball' (x : 𝔸) (hx : x ∈ Emetric.Ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasSum (fun n => (1 / n ! : 𝕂) • (x^n)) (exp 𝕂 𝔸 x) := by
  rw [← exp_series_apply_eq']
  exact exp_series_has_sum_exp_of_mem_ball x hx

theorem exp_series_field_has_sum_exp_of_mem_ball [CompleteSpace 𝕂] (x : 𝕂)
    (hx : x ∈ Emetric.Ball (0 : 𝕂) (expSeries 𝕂 𝕂).radius) : HasSum (fun n => (x^n) / n !) (exp 𝕂 𝕂 x) := by
  rw [← exp_series_apply_eq_field']
  exact exp_series_has_sum_exp_of_mem_ball x hx

theorem has_fpower_series_on_ball_exp_of_radius_pos (h : 0 < (expSeries 𝕂 𝔸).radius) :
    HasFpowerSeriesOnBall (exp 𝕂 𝔸) (expSeries 𝕂 𝔸) 0 (expSeries 𝕂 𝔸).radius :=
  (expSeries 𝕂 𝔸).HasFpowerSeriesOnBall h

theorem has_fpower_series_at_exp_zero_of_radius_pos (h : 0 < (expSeries 𝕂 𝔸).radius) :
    HasFpowerSeriesAt (exp 𝕂 𝔸) (expSeries 𝕂 𝔸) 0 :=
  (has_fpower_series_on_ball_exp_of_radius_pos h).HasFpowerSeriesAt

theorem continuous_on_exp : ContinuousOn (exp 𝕂 𝔸) (Emetric.Ball 0 (expSeries 𝕂 𝔸).radius) :=
  FormalMultilinearSeries.continuous_on

theorem analytic_at_exp_of_mem_ball (x : 𝔸) (hx : x ∈ Emetric.Ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    AnalyticAt 𝕂 (exp 𝕂 𝔸) x := by
  by_cases' h : (expSeries 𝕂 𝔸).radius = 0
  ·
    rw [h] at hx
    exact (Ennreal.not_lt_zero hx).elim
  ·
    have h := pos_iff_ne_zero.mpr h
    exact (has_fpower_series_on_ball_exp_of_radius_pos h).analytic_at_of_mem hx

/--  In a Banach-algebra `𝔸` over a normed field `𝕂` of characteristic zero, if `x` and `y` are
in the disk of convergence and commute, then `exp 𝕂 𝔸 (x + y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)`. -/
theorem exp_add_of_commute_of_mem_ball [CharZero 𝕂] {x y : 𝔸} (hxy : Commute x y)
    (hx : x ∈ Emetric.Ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) (hy : y ∈ Emetric.Ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    exp 𝕂 𝔸 (x+y) = exp 𝕂 𝔸 x*exp 𝕂 𝔸 y := by
  rw [exp_eq_tsum,
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (norm_exp_series_summable_of_mem_ball' x hx)
      (norm_exp_series_summable_of_mem_ball' y hy)]
  dsimp only
  conv_lhs => congr ext rw [hxy.add_pow' _, Finset.smul_sum]
  refine' tsum_congr fun n => Finset.sum_congr rfl $ fun kl hkl => _
  rw [nsmul_eq_smul_cast 𝕂, smul_smul, smul_mul_smul, ← finset.nat.mem_antidiagonal.mp hkl, Nat.cast_add_choose,
    finset.nat.mem_antidiagonal.mp hkl]
  congr 1
  have : (n ! : 𝕂) ≠ 0 := nat.cast_ne_zero.mpr n.factorial_ne_zero
  field_simp [this]

end CompleteAlgebra

end AnyFieldAnyAlgebra

section AnyFieldCommAlgebra

variable {𝕂 𝔸 : Type _} [NondiscreteNormedField 𝕂] [NormedCommRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/--  In a commutative Banach-algebra `𝔸` over a normed field `𝕂` of characteristic zero,
`exp 𝕂 𝔸 (x+y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)` for all `x`, `y` in the disk of convergence. -/
theorem exp_add_of_mem_ball [CharZero 𝕂] {x y : 𝔸} (hx : x ∈ Emetric.Ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius)
    (hy : y ∈ Emetric.Ball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) : exp 𝕂 𝔸 (x+y) = exp 𝕂 𝔸 x*exp 𝕂 𝔸 y :=
  exp_add_of_commute_of_mem_ball (Commute.all x y) hx hy

end AnyFieldCommAlgebra

section IsROrC

section AnyAlgebra

variable (𝕂 𝔸 : Type _) [IsROrC 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]

/--  In a normed algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`, the series defining the exponential map
has an infinite radius of convergence. -/
theorem exp_series_radius_eq_top : (expSeries 𝕂 𝔸).radius = ∞ := by
  refine' (expSeries 𝕂 𝔸).radius_eq_top_of_summable_norm fun r => _
  refine' summable_of_norm_bounded_eventually _ (Real.summable_pow_div_factorial r) _
  filter_upwards [eventually_cofinite_ne 0]
  intro n hn
  rw [norm_mul, norm_norm (expSeries 𝕂 𝔸 n), expSeries, norm_smul, norm_div, norm_one, norm_pow, Nnreal.norm_eq,
    norm_eq_abs, abs_cast_nat, mul_commₓ, ← mul_assocₓ, ← mul_div_assoc, mul_oneₓ]
  have : ∥ContinuousMultilinearMap.mkPiAlgebraFin 𝕂 n 𝔸∥ ≤ 1 :=
    norm_mk_pi_algebra_fin_le_of_pos (Nat.pos_of_ne_zeroₓ hn)
  exact mul_le_of_le_one_right (div_nonneg (pow_nonneg r.coe_nonneg n) n !.cast_nonneg) this

theorem exp_series_radius_pos : 0 < (expSeries 𝕂 𝔸).radius := by
  rw [exp_series_radius_eq_top]
  exact WithTop.zero_lt_top

variable {𝕂 𝔸}

section CompleteAlgebra

theorem norm_exp_series_summable (x : 𝔸) : Summable fun n => ∥expSeries 𝕂 𝔸 n fun _ => x∥ :=
  norm_exp_series_summable_of_mem_ball x ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

theorem norm_exp_series_summable' (x : 𝔸) : Summable fun n => ∥(1 / n ! : 𝕂) • (x^n)∥ :=
  norm_exp_series_summable_of_mem_ball' x ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

theorem norm_exp_series_field_summable (x : 𝕂) : Summable fun n => ∥(x^n) / n !∥ :=
  norm_exp_series_field_summable_of_mem_ball x ((exp_series_radius_eq_top 𝕂 𝕂).symm ▸ edist_lt_top _ _)

variable [CompleteSpace 𝔸]

theorem exp_series_summable (x : 𝔸) : Summable fun n => expSeries 𝕂 𝔸 n fun _ => x :=
  summable_of_summable_norm (norm_exp_series_summable x)

theorem exp_series_summable' (x : 𝔸) : Summable fun n => (1 / n ! : 𝕂) • (x^n) :=
  summable_of_summable_norm (norm_exp_series_summable' x)

theorem exp_series_field_summable (x : 𝕂) : Summable fun n => (x^n) / n ! :=
  summable_of_summable_norm (norm_exp_series_field_summable x)

theorem exp_series_has_sum_exp (x : 𝔸) : HasSum (fun n => expSeries 𝕂 𝔸 n fun _ => x) (exp 𝕂 𝔸 x) :=
  exp_series_has_sum_exp_of_mem_ball x ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

theorem exp_series_has_sum_exp' (x : 𝔸) : HasSum (fun n => (1 / n ! : 𝕂) • (x^n)) (exp 𝕂 𝔸 x) :=
  exp_series_has_sum_exp_of_mem_ball' x ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

theorem exp_series_field_has_sum_exp (x : 𝕂) : HasSum (fun n => (x^n) / n !) (exp 𝕂 𝕂 x) :=
  exp_series_field_has_sum_exp_of_mem_ball x ((exp_series_radius_eq_top 𝕂 𝕂).symm ▸ edist_lt_top _ _)

theorem exp_has_fpower_series_on_ball : HasFpowerSeriesOnBall (exp 𝕂 𝔸) (expSeries 𝕂 𝔸) 0 ∞ :=
  exp_series_radius_eq_top 𝕂 𝔸 ▸ has_fpower_series_on_ball_exp_of_radius_pos (exp_series_radius_pos _ _)

theorem exp_has_fpower_series_at_zero : HasFpowerSeriesAt (exp 𝕂 𝔸) (expSeries 𝕂 𝔸) 0 :=
  exp_has_fpower_series_on_ball.HasFpowerSeriesAt

theorem exp_continuous : Continuous (exp 𝕂 𝔸) := by
  rw [continuous_iff_continuous_on_univ, ← Metric.eball_top_eq_univ (0 : 𝔸), ← exp_series_radius_eq_top 𝕂 𝔸]
  exact continuous_on_exp

theorem exp_analytic (x : 𝔸) : AnalyticAt 𝕂 (exp 𝕂 𝔸) x :=
  analytic_at_exp_of_mem_ball x ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

end CompleteAlgebra

attribute [local instance] char_zero_R_or_C

/--  In a Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`, if `x` and `y` commute, then
`exp 𝕂 𝔸 (x+y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)`. -/
theorem exp_add_of_commute [CompleteSpace 𝔸] {x y : 𝔸} (hxy : Commute x y) : exp 𝕂 𝔸 (x+y) = exp 𝕂 𝔸 x*exp 𝕂 𝔸 y :=
  exp_add_of_commute_of_mem_ball hxy ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
    ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

end AnyAlgebra

section CommAlgebra

variable {𝕂 𝔸 : Type _} [IsROrC 𝕂] [NormedCommRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

attribute [local instance] char_zero_R_or_C

/--  In a comutative Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`,
`exp 𝕂 𝔸 (x+y) = (exp 𝕂 𝔸 x) * (exp 𝕂 𝔸 y)`. -/
theorem exp_add {x y : 𝔸} : exp 𝕂 𝔸 (x+y) = exp 𝕂 𝔸 x*exp 𝕂 𝔸 y :=
  exp_add_of_mem_ball ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)
    ((exp_series_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

end CommAlgebra

end IsROrC

section ScalarTower

variable (𝕂 𝕂' 𝔸 : Type _) [NondiscreteNormedField 𝕂] [NondiscreteNormedField 𝕂'] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  [NormedAlgebra 𝕂' 𝔸]

/--  If a normed ring `𝔸` is a normed algebra over two fields, then they define the same
`exp_series` on `𝔸`. -/
theorem exp_series_eq_exp_series (n : ℕ) (x : 𝔸) : (expSeries 𝕂 𝔸 n fun _ => x) = expSeries 𝕂' 𝔸 n fun _ => x := by
  rw [expSeries, expSeries, smul_apply, mk_pi_algebra_fin_apply, List.of_fn_const, List.prod_repeat, smul_apply,
    mk_pi_algebra_fin_apply, List.of_fn_const, List.prod_repeat, one_div, one_div, inv_nat_cast_smul_eq 𝕂 𝕂']

/--  If a normed ring `𝔸` is a normed algebra over two fields, then they define the same
exponential function on `𝔸`. -/
theorem exp_eq_exp : exp 𝕂 𝔸 = exp 𝕂' 𝔸 := by
  ext
  rw [exp, exp]
  refine' tsum_congr fun n => _
  rw [exp_series_eq_exp_series 𝕂 𝕂' 𝔸 n x]

theorem exp_ℝ_ℂ_eq_exp_ℂ_ℂ : exp ℝ ℂ = exp ℂ ℂ :=
  exp_eq_exp ℝ ℂ ℂ

end ScalarTower

