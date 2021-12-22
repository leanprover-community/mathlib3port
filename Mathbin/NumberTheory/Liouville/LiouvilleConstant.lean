import Mathbin.NumberTheory.Liouville.Basic

/-!

# Liouville constants

This file contains a construction of a family of Liouville numbers, indexed by a natural number $m$.
The most important property is that they are examples of transcendental real numbers.
This fact is recorded in `liouville.is_transcendental`.

More precisely, for a real number $m$, Liouville's constant is
$$
\sum_{i=0}^\infty\frac{1}{m^{i!}}.
$$
The series converges only for $1 < m$.  However, there is no restriction on $m$, since,
if the series does not converge, then the sum of the series is defined to be zero.

We prove that, for $m \in \mathbb{N}$ satisfying $2 \le m$, Liouville's constant associated to $m$
is a transcendental number.  Classically, the Liouville number for $m = 2$ is the one called
``Liouville's constant''.

## Implementation notes

The indexing $m$ is eventually a natural number satisfying $2 ≤ m$.  However, we prove the first few
lemmas for $m \in \mathbb{R}$.
-/


noncomputable section

open_locale Nat BigOperators

open Real Finset

namespace Liouville

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    "\nFor a real number `m`, Liouville's constant is\n$$\n\\sum_{i=0}^\\infty\\frac{1}{m^{i!}}.\n$$\nThe series converges only for `1 < m`.  However, there is no restriction on `m`, since,\nif the series does not converge, then the sum of the series is defined to be zero.\n-/")]
  []
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `liouville_number [])
  (Command.optDeclSig
   [(Term.explicitBinder "(" [`m] [":" (Data.Real.Basic.termℝ "ℝ")] [] ")")]
   [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))])
  (Command.declValSimple
   ":="
   (Topology.Algebra.InfiniteSum.«term∑'_,_»
    "∑'"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (termℕ "ℕ")]))
    ", "
    («term_/_»
     (numLit "1")
     "/"
     (Cardinal.SetTheory.Cofinality.«term_^_» `m "^" (Nat.Data.Nat.Factorial.Basic.term_! `i "!"))))
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
  (Topology.Algebra.InfiniteSum.«term∑'_,_»
   "∑'"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (termℕ "ℕ")]))
   ", "
   («term_/_»
    (numLit "1")
    "/"
    (Cardinal.SetTheory.Cofinality.«term_^_» `m "^" (Nat.Data.Nat.Factorial.Basic.term_! `i "!"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Algebra.InfiniteSum.«term∑'_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_/_»
   (numLit "1")
   "/"
   (Cardinal.SetTheory.Cofinality.«term_^_» `m "^" (Nat.Data.Nat.Factorial.Basic.term_! `i "!")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Cardinal.SetTheory.Cofinality.«term_^_» `m "^" (Nat.Data.Nat.Factorial.Basic.term_! `i "!"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Nat.Data.Nat.Factorial.Basic.term_! `i "!")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Nat.Data.Nat.Factorial.Basic.term_!', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10000, term))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10000, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10000, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1024, (none, [anonymous]) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Cardinal.SetTheory.Cofinality.«term_^_» `m "^" (Nat.Data.Nat.Factorial.Basic.term_! `i "!")) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
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
    For a real number `m`, Liouville's constant is
    $$
    \sum_{i=0}^\infty\frac{1}{m^{i!}}.
    $$
    The series converges only for `1 < m`.  However, there is no restriction on `m`, since,
    if the series does not converge, then the sum of the series is defined to be zero.
    -/
  def liouville_number ( m : ℝ ) : ℝ := ∑' i : ℕ , 1 / m ^ i !

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    "\n`liouville_number_initial_terms` is the sum of the first `k + 1` terms of Liouville's constant,\ni.e.\n$$\n\\sum_{i=0}^k\\frac{1}{m^{i!}}.\n$$\n-/")]
  []
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `liouville_number_initial_terms [])
  (Command.optDeclSig
   [(Term.explicitBinder "(" [`m] [":" (Data.Real.Basic.termℝ "ℝ")] [] ")")
    (Term.explicitBinder "(" [`k] [":" (termℕ "ℕ")] [] ")")]
   [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))])
  (Command.declValSimple
   ":="
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
    " in "
    (Term.app `range [(Init.Logic.«term_+_» `k "+" (numLit "1"))])
    ", "
    («term_/_»
     (numLit "1")
     "/"
     (Cardinal.SetTheory.Cofinality.«term_^_» `m "^" (Nat.Data.Nat.Factorial.Basic.term_! `i "!"))))
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
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
   " in "
   (Term.app `range [(Init.Logic.«term_+_» `k "+" (numLit "1"))])
   ", "
   («term_/_»
    (numLit "1")
    "/"
    (Cardinal.SetTheory.Cofinality.«term_^_» `m "^" (Nat.Data.Nat.Factorial.Basic.term_! `i "!"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_/_»
   (numLit "1")
   "/"
   (Cardinal.SetTheory.Cofinality.«term_^_» `m "^" (Nat.Data.Nat.Factorial.Basic.term_! `i "!")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Cardinal.SetTheory.Cofinality.«term_^_» `m "^" (Nat.Data.Nat.Factorial.Basic.term_! `i "!"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Nat.Data.Nat.Factorial.Basic.term_! `i "!")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Nat.Data.Nat.Factorial.Basic.term_!', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10000, term))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10000, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10000, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1024, (none, [anonymous]) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Cardinal.SetTheory.Cofinality.«term_^_» `m "^" (Nat.Data.Nat.Factorial.Basic.term_! `i "!")) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `range [(Init.Logic.«term_+_» `k "+" (numLit "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `k "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `k "+" (numLit "1")) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `range
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
    `liouville_number_initial_terms` is the sum of the first `k + 1` terms of Liouville's constant,
    i.e.
    $$
    \sum_{i=0}^k\frac{1}{m^{i!}}.
    $$
    -/
  def liouville_number_initial_terms ( m : ℝ ) ( k : ℕ ) : ℝ := ∑ i in range k + 1 , 1 / m ^ i !

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    "\n`liouville_number_tail` is the sum of the series of the terms in `liouville_number m`\nstarting from `k+1`, i.e\n$$\n\\sum_{i=k+1}^\\infty\\frac{1}{m^{i!}}.\n$$\n-/")]
  []
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `liouville_number_tail [])
  (Command.optDeclSig
   [(Term.explicitBinder "(" [`m] [":" (Data.Real.Basic.termℝ "ℝ")] [] ")")
    (Term.explicitBinder "(" [`k] [":" (termℕ "ℕ")] [] ")")]
   [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))])
  (Command.declValSimple
   ":="
   (Topology.Algebra.InfiniteSum.«term∑'_,_»
    "∑'"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
    ", "
    («term_/_»
     (numLit "1")
     "/"
     (Cardinal.SetTheory.Cofinality.«term_^_»
      `m
      "^"
      (Nat.Data.Nat.Factorial.Basic.term_!
       (Init.Logic.«term_+_» `i "+" (Init.Logic.«term_+_» `k "+" (numLit "1")))
       "!"))))
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
  (Topology.Algebra.InfiniteSum.«term∑'_,_»
   "∑'"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
   ", "
   («term_/_»
    (numLit "1")
    "/"
    (Cardinal.SetTheory.Cofinality.«term_^_»
     `m
     "^"
     (Nat.Data.Nat.Factorial.Basic.term_!
      (Init.Logic.«term_+_» `i "+" (Init.Logic.«term_+_» `k "+" (numLit "1")))
      "!"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Algebra.InfiniteSum.«term∑'_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_/_»
   (numLit "1")
   "/"
   (Cardinal.SetTheory.Cofinality.«term_^_»
    `m
    "^"
    (Nat.Data.Nat.Factorial.Basic.term_! (Init.Logic.«term_+_» `i "+" (Init.Logic.«term_+_» `k "+" (numLit "1"))) "!")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Cardinal.SetTheory.Cofinality.«term_^_»
   `m
   "^"
   (Nat.Data.Nat.Factorial.Basic.term_! (Init.Logic.«term_+_» `i "+" (Init.Logic.«term_+_» `k "+" (numLit "1"))) "!"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Nat.Data.Nat.Factorial.Basic.term_! (Init.Logic.«term_+_» `i "+" (Init.Logic.«term_+_» `k "+" (numLit "1"))) "!")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Nat.Data.Nat.Factorial.Basic.term_!', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10000, term))
  (Init.Logic.«term_+_» `i "+" (Init.Logic.«term_+_» `k "+" (numLit "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `k "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 10000, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Init.Logic.«term_+_» `i "+" (Init.Logic.«term_+_» `k "+" (numLit "1"))) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10000, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1024, (none, [anonymous]) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Cardinal.SetTheory.Cofinality.«term_^_»
   `m
   "^"
   (Nat.Data.Nat.Factorial.Basic.term_!
    (Term.paren "(" [(Init.Logic.«term_+_» `i "+" (Init.Logic.«term_+_» `k "+" (numLit "1"))) []] ")")
    "!"))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
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
    `liouville_number_tail` is the sum of the series of the terms in `liouville_number m`
    starting from `k+1`, i.e
    $$
    \sum_{i=k+1}^\infty\frac{1}{m^{i!}}.
    $$
    -/
  def liouville_number_tail ( m : ℝ ) ( k : ℕ ) : ℝ := ∑' i , 1 / m ^ i + k + 1 !

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `liouville_number_tail_pos [])
  (Command.declSig
   [(Term.implicitBinder "{" [`m] [":" (Data.Real.Basic.termℝ "ℝ")] "}")
    (Term.explicitBinder "(" [`hm] [":" («term_<_» (numLit "1") "<" `m)] [] ")")
    (Term.explicitBinder "(" [`k] [":" (termℕ "ℕ")] [] ")")]
   (Term.typeSpec ":" («term_<_» (numLit "0") "<" (Term.app `liouville_number_tail [`m `k]))))
  (Command.declValSimple
   ":="
   (calc
    "calc"
    [(calcStep
      («term_=_»
       (Term.paren "(" [(numLit "0") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
       "="
       (Topology.Algebra.InfiniteSum.«term∑'_,_»
        "∑'"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (termℕ "ℕ")]))
        ", "
        (numLit "0")))
      ":="
      (Term.proj `tsum_zero "." `symm))
     (calcStep
      («term_<_» (Term.hole "_") "<" (Term.app `liouville_number_tail [`m `k]))
      ":="
      («term_$__»
       (Term.app
        `tsum_lt_tsum_of_nonneg
        [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" (Term.proj `rfl "." `le)))
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`i] [])]
           "=>"
           (Term.app
            (Term.proj `one_div_nonneg "." `mpr)
            [(Term.app `pow_nonneg [(Term.app (Term.proj `zero_le_one "." `trans) [`hm.le]) (Term.hole "_")])])))
         (Term.app
          (Term.proj `one_div_pos "." `mpr)
          [(Term.app
            `pow_pos
            [(Term.app (Term.proj `zero_lt_one "." `trans) [`hm])
             (Nat.Data.Nat.Factorial.Basic.term_!
              (Init.Logic.«term_+_» (numLit "0") "+" (Init.Logic.«term_+_» `k "+" (numLit "1")))
              "!")])])])
       "$"
       (Term.app
        `summable_one_div_pow_of_le
        [`hm
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`i] [])]
           "=>"
           (Term.app `trans [`le_self_add (Term.app `Nat.self_le_factorial [(Term.hole "_")])])))])))])
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
  (calc
   "calc"
   [(calcStep
     («term_=_»
      (Term.paren "(" [(numLit "0") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
      "="
      (Topology.Algebra.InfiniteSum.«term∑'_,_»
       "∑'"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (termℕ "ℕ")]))
       ", "
       (numLit "0")))
     ":="
     (Term.proj `tsum_zero "." `symm))
    (calcStep
     («term_<_» (Term.hole "_") "<" (Term.app `liouville_number_tail [`m `k]))
     ":="
     («term_$__»
      (Term.app
       `tsum_lt_tsum_of_nonneg
       [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" (Term.proj `rfl "." `le)))
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`i] [])]
          "=>"
          (Term.app
           (Term.proj `one_div_nonneg "." `mpr)
           [(Term.app `pow_nonneg [(Term.app (Term.proj `zero_le_one "." `trans) [`hm.le]) (Term.hole "_")])])))
        (Term.app
         (Term.proj `one_div_pos "." `mpr)
         [(Term.app
           `pow_pos
           [(Term.app (Term.proj `zero_lt_one "." `trans) [`hm])
            (Nat.Data.Nat.Factorial.Basic.term_!
             (Init.Logic.«term_+_» (numLit "0") "+" (Init.Logic.«term_+_» `k "+" (numLit "1")))
             "!")])])])
      "$"
      (Term.app
       `summable_one_div_pow_of_le
       [`hm
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`i] [])]
          "=>"
          (Term.app `trans [`le_self_add (Term.app `Nat.self_le_factorial [(Term.hole "_")])])))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calc', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__»
   (Term.app
    `tsum_lt_tsum_of_nonneg
    [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" (Term.proj `rfl "." `le)))
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`i] [])]
       "=>"
       (Term.app
        (Term.proj `one_div_nonneg "." `mpr)
        [(Term.app `pow_nonneg [(Term.app (Term.proj `zero_le_one "." `trans) [`hm.le]) (Term.hole "_")])])))
     (Term.app
      (Term.proj `one_div_pos "." `mpr)
      [(Term.app
        `pow_pos
        [(Term.app (Term.proj `zero_lt_one "." `trans) [`hm])
         (Nat.Data.Nat.Factorial.Basic.term_!
          (Init.Logic.«term_+_» (numLit "0") "+" (Init.Logic.«term_+_» `k "+" (numLit "1")))
          "!")])])])
   "$"
   (Term.app
    `summable_one_div_pow_of_le
    [`hm
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`i] [])]
       "=>"
       (Term.app `trans [`le_self_add (Term.app `Nat.self_le_factorial [(Term.hole "_")])])))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `summable_one_div_pow_of_le
   [`hm
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`i] [])]
      "=>"
      (Term.app `trans [`le_self_add (Term.app `Nat.self_le_factorial [(Term.hole "_")])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`i] [])]
    "=>"
    (Term.app `trans [`le_self_add (Term.app `Nat.self_le_factorial [(Term.hole "_")])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `trans [`le_self_add (Term.app `Nat.self_le_factorial [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Nat.self_le_factorial [(Term.hole "_")])
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
  `Nat.self_le_factorial
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `Nat.self_le_factorial [(Term.hole "_")]) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `le_self_add
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `trans
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `hm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `summable_one_div_pow_of_le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  (Term.app
   `tsum_lt_tsum_of_nonneg
   [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" (Term.proj `rfl "." `le)))
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`i] [])]
      "=>"
      (Term.app
       (Term.proj `one_div_nonneg "." `mpr)
       [(Term.app `pow_nonneg [(Term.app (Term.proj `zero_le_one "." `trans) [`hm.le]) (Term.hole "_")])])))
    (Term.app
     (Term.proj `one_div_pos "." `mpr)
     [(Term.app
       `pow_pos
       [(Term.app (Term.proj `zero_lt_one "." `trans) [`hm])
        (Nat.Data.Nat.Factorial.Basic.term_!
         (Init.Logic.«term_+_» (numLit "0") "+" (Init.Logic.«term_+_» `k "+" (numLit "1")))
         "!")])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj `one_div_pos "." `mpr)
   [(Term.app
     `pow_pos
     [(Term.app (Term.proj `zero_lt_one "." `trans) [`hm])
      (Nat.Data.Nat.Factorial.Basic.term_!
       (Init.Logic.«term_+_» (numLit "0") "+" (Init.Logic.«term_+_» `k "+" (numLit "1")))
       "!")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `pow_pos
   [(Term.app (Term.proj `zero_lt_one "." `trans) [`hm])
    (Nat.Data.Nat.Factorial.Basic.term_!
     (Init.Logic.«term_+_» (numLit "0") "+" (Init.Logic.«term_+_» `k "+" (numLit "1")))
     "!")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Nat.Data.Nat.Factorial.Basic.term_!', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Nat.Data.Nat.Factorial.Basic.term_!', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Nat.Data.Nat.Factorial.Basic.term_!', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Nat.Data.Nat.Factorial.Basic.term_!', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Nat.Data.Nat.Factorial.Basic.term_!', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Nat.Data.Nat.Factorial.Basic.term_!
   (Init.Logic.«term_+_» (numLit "0") "+" (Init.Logic.«term_+_» `k "+" (numLit "1")))
   "!")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Nat.Data.Nat.Factorial.Basic.term_!', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10000, term))
  (Init.Logic.«term_+_» (numLit "0") "+" (Init.Logic.«term_+_» `k "+" (numLit "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `k "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 10000, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Init.Logic.«term_+_» (numLit "0") "+" (Init.Logic.«term_+_» `k "+" (numLit "1"))) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10000, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app (Term.proj `zero_lt_one "." `trans) [`hm])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `zero_lt_one "." `trans)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `zero_lt_one
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app (Term.proj `zero_lt_one "." `trans) [`hm]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `pow_pos
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `pow_pos
   [(Term.paren "(" [(Term.app (Term.proj `zero_lt_one "." `trans) [`hm]) []] ")")
    (Nat.Data.Nat.Factorial.Basic.term_!
     (Term.paren "(" [(Init.Logic.«term_+_» (numLit "0") "+" (Init.Logic.«term_+_» `k "+" (numLit "1"))) []] ")")
     "!")])
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `one_div_pos "." `mpr)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `one_div_pos
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   (Term.proj `one_div_pos "." `mpr)
   [(Term.paren
     "("
     [(Term.app
       `pow_pos
       [(Term.paren "(" [(Term.app (Term.proj `zero_lt_one "." `trans) [`hm]) []] ")")
        (Nat.Data.Nat.Factorial.Basic.term_!
         (Term.paren "(" [(Init.Logic.«term_+_» (numLit "0") "+" (Init.Logic.«term_+_» `k "+" (numLit "1"))) []] ")")
         "!")])
      []]
     ")")])
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`i] [])]
    "=>"
    (Term.app
     (Term.proj `one_div_nonneg "." `mpr)
     [(Term.app `pow_nonneg [(Term.app (Term.proj `zero_le_one "." `trans) [`hm.le]) (Term.hole "_")])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj `one_div_nonneg "." `mpr)
   [(Term.app `pow_nonneg [(Term.app (Term.proj `zero_le_one "." `trans) [`hm.le]) (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `pow_nonneg [(Term.app (Term.proj `zero_le_one "." `trans) [`hm.le]) (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.app (Term.proj `zero_le_one "." `trans) [`hm.le])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hm.le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `zero_le_one "." `trans)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `zero_le_one
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app (Term.proj `zero_le_one "." `trans) [`hm.le]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `pow_nonneg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `pow_nonneg
   [(Term.paren "(" [(Term.app (Term.proj `zero_le_one "." `trans) [`hm.le]) []] ")") (Term.hole "_")])
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `one_div_nonneg "." `mpr)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `one_div_nonneg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`i] [])]
    "=>"
    (Term.app
     (Term.proj `one_div_nonneg "." `mpr)
     [(Term.paren
       "("
       [(Term.app
         `pow_nonneg
         [(Term.paren "(" [(Term.app (Term.proj `zero_le_one "." `trans) [`hm.le]) []] ")") (Term.hole "_")])
        []]
       ")")])))
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" (Term.proj `rfl "." `le)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `rfl "." `le)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" (Term.proj `rfl "." `le))) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `tsum_lt_tsum_of_nonneg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_<_» (Term.hole "_") "<" (Term.app `liouville_number_tail [`m `k]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `liouville_number_tail [`m `k])
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
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `liouville_number_tail
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.proj `tsum_zero "." `symm)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `tsum_zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.paren "(" [(numLit "0") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
   "="
   (Topology.Algebra.InfiniteSum.«term∑'_,_»
    "∑'"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (termℕ "ℕ")]))
    ", "
    (numLit "0")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Topology.Algebra.InfiniteSum.«term∑'_,_»
   "∑'"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (termℕ "ℕ")]))
   ", "
   (numLit "0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Algebra.InfiniteSum.«term∑'_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
  liouville_number_tail_pos
  { m : ℝ } ( hm : 1 < m ) ( k : ℕ ) : 0 < liouville_number_tail m k
  :=
    calc
      ( 0 : ℝ ) = ∑' i : ℕ , 0 := tsum_zero . symm
        _ < liouville_number_tail m k
          :=
          tsum_lt_tsum_of_nonneg
              fun _ => rfl . le
                fun i => one_div_nonneg . mpr pow_nonneg zero_le_one . trans hm.le _
                one_div_pos . mpr pow_pos zero_lt_one . trans hm 0 + k + 1 !
            $
            summable_one_div_pow_of_le hm fun i => trans le_self_add Nat.self_le_factorial _

/--   Split the sum definining a Liouville number into the first `k` term and the rest. -/
theorem liouville_number_eq_initial_terms_add_tail {m : ℝ} (hm : 1 < m) (k : ℕ) :
    liouville_number m = liouville_number_initial_terms m k+liouville_number_tail m k :=
  (sum_add_tsum_nat_add _ (summable_one_div_pow_of_le hm fun i => i.self_le_factorial)).symm

/-! We now prove two useful inequalities, before collecting everything together. -/


/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment "/--" "  Partial inequality, works with `m ∈ ℝ` satisfying `1 < m`. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `tsum_one_div_pow_factorial_lt [])
  (Command.declSig
   [(Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")
    (Term.implicitBinder "{" [`m] [":" (Data.Real.Basic.termℝ "ℝ")] "}")
    (Term.explicitBinder "(" [`m1] [":" («term_<_» (numLit "1") "<" `m)] [] ")")]
   (Term.typeSpec
    ":"
    («term_<_»
     (Topology.Algebra.InfiniteSum.«term∑'_,_»
      "∑'"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (termℕ "ℕ")]))
      ", "
      («term_/_»
       (numLit "1")
       "/"
       (Cardinal.SetTheory.Cofinality.«term_^_»
        `m
        "^"
        (Nat.Data.Nat.Factorial.Basic.term_!
         (Init.Logic.«term_+_» `i "+" (Init.Logic.«term_+_» `n "+" (numLit "1")))
         "!"))))
     "<"
     (Finset.Data.Finset.Fold.«term_*_»
      (Init.Logic.«term_⁻¹» («term_-_» (numLit "1") "-" («term_/_» (numLit "1") "/" `m)) "⁻¹")
      "*"
      («term_/_»
       (numLit "1")
       "/"
       (Cardinal.SetTheory.Cofinality.«term_^_»
        `m
        "^"
        (Nat.Data.Nat.Factorial.Basic.term_! (Init.Logic.«term_+_» `n "+" (numLit "1")) "!")))))))
  (Command.declValSimple
   ":="
   (Term.have
    "have"
    (Term.haveDecl
     (Term.haveIdDecl
      [`m0 []]
      [(Term.typeSpec ":" («term_<_» (numLit "0") "<" `m))]
      ":="
      (Term.app (Term.proj `zero_lt_one "." `trans) [`m1])))
    []
    (Term.have
     "have"
     (Term.haveDecl
      (Term.haveIdDecl
       [`mi []]
       [(Term.typeSpec
         ":"
         («term_<_» (Algebra.Abs.«term|_|» "|" («term_/_» (numLit "1") "/" `m) "|") "<" (numLit "1")))]
       ":="
       (Term.app
        (Term.proj
         (Term.app `le_of_eqₓ [(Term.app `abs_of_pos [(Term.app (Term.proj `one_div_pos "." `mpr) [`m0])])])
         "."
         `trans_lt)
        [(Term.app (Term.proj (Term.app `div_lt_one [`m0]) "." `mpr) [`m1])])))
     []
     (calc
      "calc"
      [(calcStep
        («term_<_»
         (Topology.Algebra.InfiniteSum.«term∑'_,_»
          "∑'"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
          ", "
          («term_/_»
           (numLit "1")
           "/"
           (Cardinal.SetTheory.Cofinality.«term_^_»
            `m
            "^"
            (Nat.Data.Nat.Factorial.Basic.term_!
             (Init.Logic.«term_+_» `i "+" (Init.Logic.«term_+_» `n "+" (numLit "1")))
             "!"))))
         "<"
         (Topology.Algebra.InfiniteSum.«term∑'_,_»
          "∑'"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
          ", "
          («term_/_»
           (numLit "1")
           "/"
           (Cardinal.SetTheory.Cofinality.«term_^_»
            `m
            "^"
            (Init.Logic.«term_+_»
             `i
             "+"
             (Nat.Data.Nat.Factorial.Basic.term_! (Init.Logic.«term_+_» `n "+" (numLit "1")) "!"))))))
        ":="
        (Term.app
         `tsum_lt_tsum_of_nonneg
         [(Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`b] [])]
            "=>"
            (Term.app (Term.proj `one_div_nonneg "." `mpr) [(Term.app `pow_nonneg [`m0.le (Term.hole "_")])])))
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`b] [])]
            "=>"
            (Term.app
             `one_div_pow_le_one_div_pow_of_le
             [`m1.le (Term.app `b.add_factorial_succ_le_factorial_add_succ [`n])])))
          (Term.app
           `one_div_pow_strict_mono
           [`m1 (Term.app `n.add_factorial_succ_lt_factorial_add_succ [(Term.proj `rfl "." `le)])])
          (Term.app
           `summable_one_div_pow_of_le
           [`m1 (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j] [])] "=>" (Term.app `Nat.Le.intro [`rfl])))])]))
       (calcStep
        («term_=_»
         (Term.hole "_")
         "="
         (Topology.Algebra.InfiniteSum.«term∑'_,_»
          "∑'"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
          ", "
          (Finset.Data.Finset.Fold.«term_*_»
           (Cardinal.SetTheory.Cofinality.«term_^_» («term_/_» (numLit "1") "/" `m) "^" `i)
           "*"
           («term_/_»
            (numLit "1")
            "/"
            (Cardinal.SetTheory.Cofinality.«term_^_»
             `m
             "^"
             (Nat.Data.Nat.Factorial.Basic.term_! (Init.Logic.«term_+_» `n "+" (numLit "1")) "!"))))))
        ":="
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.congr "congr" [] []) [])
            (group (Tactic.ext "ext" [(Tactic.rcasesPat.one `i)] []) [])
            (group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `pow_addₓ)
                ","
                (Tactic.rwRule ["←"] `div_div_eq_div_mul)
                ","
                (Tactic.rwRule [] `div_eq_mul_one_div)
                ","
                (Tactic.rwRule ["←"] (Term.app `one_div_pow [`i]))]
               "]")
              [])
             [])]))))
       (calcStep
        («term_=_»
         (Term.hole "_")
         "="
         (Finset.Data.Finset.Fold.«term_*_»
          (Topology.Algebra.InfiniteSum.«term∑'_,_»
           "∑'"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
           ", "
           (Cardinal.SetTheory.Cofinality.«term_^_» («term_/_» (numLit "1") "/" `m) "^" `i))
          "*"
          («term_/_»
           (numLit "1")
           "/"
           (Cardinal.SetTheory.Cofinality.«term_^_»
            `m
            "^"
            (Nat.Data.Nat.Factorial.Basic.term_! (Init.Logic.«term_+_» `n "+" (numLit "1")) "!")))))
        ":="
        `tsum_mul_right)
       (calcStep
        («term_=_»
         (Term.hole "_")
         "="
         (Finset.Data.Finset.Fold.«term_*_»
          (Init.Logic.«term_⁻¹» («term_-_» (numLit "1") "-" («term_/_» (numLit "1") "/" `m)) "⁻¹")
          "*"
          («term_/_»
           (numLit "1")
           "/"
           (Cardinal.SetTheory.Cofinality.«term_^_»
            `m
            "^"
            (Nat.Data.Nat.Factorial.Basic.term_! (Init.Logic.«term_+_» `n "+" (numLit "1")) "!")))))
        ":="
        (Term.app
         (Term.proj `mul_eq_mul_right_iff "." `mpr)
         [(Term.app `Or.inl [(Term.app `tsum_geometric_of_abs_lt_1 [`mi])])]))])))
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
  (Term.have
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`m0 []]
     [(Term.typeSpec ":" («term_<_» (numLit "0") "<" `m))]
     ":="
     (Term.app (Term.proj `zero_lt_one "." `trans) [`m1])))
   []
   (Term.have
    "have"
    (Term.haveDecl
     (Term.haveIdDecl
      [`mi []]
      [(Term.typeSpec ":" («term_<_» (Algebra.Abs.«term|_|» "|" («term_/_» (numLit "1") "/" `m) "|") "<" (numLit "1")))]
      ":="
      (Term.app
       (Term.proj
        (Term.app `le_of_eqₓ [(Term.app `abs_of_pos [(Term.app (Term.proj `one_div_pos "." `mpr) [`m0])])])
        "."
        `trans_lt)
       [(Term.app (Term.proj (Term.app `div_lt_one [`m0]) "." `mpr) [`m1])])))
    []
    (calc
     "calc"
     [(calcStep
       («term_<_»
        (Topology.Algebra.InfiniteSum.«term∑'_,_»
         "∑'"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
         ", "
         («term_/_»
          (numLit "1")
          "/"
          (Cardinal.SetTheory.Cofinality.«term_^_»
           `m
           "^"
           (Nat.Data.Nat.Factorial.Basic.term_!
            (Init.Logic.«term_+_» `i "+" (Init.Logic.«term_+_» `n "+" (numLit "1")))
            "!"))))
        "<"
        (Topology.Algebra.InfiniteSum.«term∑'_,_»
         "∑'"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
         ", "
         («term_/_»
          (numLit "1")
          "/"
          (Cardinal.SetTheory.Cofinality.«term_^_»
           `m
           "^"
           (Init.Logic.«term_+_»
            `i
            "+"
            (Nat.Data.Nat.Factorial.Basic.term_! (Init.Logic.«term_+_» `n "+" (numLit "1")) "!"))))))
       ":="
       (Term.app
        `tsum_lt_tsum_of_nonneg
        [(Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`b] [])]
           "=>"
           (Term.app (Term.proj `one_div_nonneg "." `mpr) [(Term.app `pow_nonneg [`m0.le (Term.hole "_")])])))
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`b] [])]
           "=>"
           (Term.app
            `one_div_pow_le_one_div_pow_of_le
            [`m1.le (Term.app `b.add_factorial_succ_le_factorial_add_succ [`n])])))
         (Term.app
          `one_div_pow_strict_mono
          [`m1 (Term.app `n.add_factorial_succ_lt_factorial_add_succ [(Term.proj `rfl "." `le)])])
         (Term.app
          `summable_one_div_pow_of_le
          [`m1 (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j] [])] "=>" (Term.app `Nat.Le.intro [`rfl])))])]))
      (calcStep
       («term_=_»
        (Term.hole "_")
        "="
        (Topology.Algebra.InfiniteSum.«term∑'_,_»
         "∑'"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
         ", "
         (Finset.Data.Finset.Fold.«term_*_»
          (Cardinal.SetTheory.Cofinality.«term_^_» («term_/_» (numLit "1") "/" `m) "^" `i)
          "*"
          («term_/_»
           (numLit "1")
           "/"
           (Cardinal.SetTheory.Cofinality.«term_^_»
            `m
            "^"
            (Nat.Data.Nat.Factorial.Basic.term_! (Init.Logic.«term_+_» `n "+" (numLit "1")) "!"))))))
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.congr "congr" [] []) [])
           (group (Tactic.ext "ext" [(Tactic.rcasesPat.one `i)] []) [])
           (group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `pow_addₓ)
               ","
               (Tactic.rwRule ["←"] `div_div_eq_div_mul)
               ","
               (Tactic.rwRule [] `div_eq_mul_one_div)
               ","
               (Tactic.rwRule ["←"] (Term.app `one_div_pow [`i]))]
              "]")
             [])
            [])]))))
      (calcStep
       («term_=_»
        (Term.hole "_")
        "="
        (Finset.Data.Finset.Fold.«term_*_»
         (Topology.Algebra.InfiniteSum.«term∑'_,_»
          "∑'"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
          ", "
          (Cardinal.SetTheory.Cofinality.«term_^_» («term_/_» (numLit "1") "/" `m) "^" `i))
         "*"
         («term_/_»
          (numLit "1")
          "/"
          (Cardinal.SetTheory.Cofinality.«term_^_»
           `m
           "^"
           (Nat.Data.Nat.Factorial.Basic.term_! (Init.Logic.«term_+_» `n "+" (numLit "1")) "!")))))
       ":="
       `tsum_mul_right)
      (calcStep
       («term_=_»
        (Term.hole "_")
        "="
        (Finset.Data.Finset.Fold.«term_*_»
         (Init.Logic.«term_⁻¹» («term_-_» (numLit "1") "-" («term_/_» (numLit "1") "/" `m)) "⁻¹")
         "*"
         («term_/_»
          (numLit "1")
          "/"
          (Cardinal.SetTheory.Cofinality.«term_^_»
           `m
           "^"
           (Nat.Data.Nat.Factorial.Basic.term_! (Init.Logic.«term_+_» `n "+" (numLit "1")) "!")))))
       ":="
       (Term.app
        (Term.proj `mul_eq_mul_right_iff "." `mpr)
        [(Term.app `Or.inl [(Term.app `tsum_geometric_of_abs_lt_1 [`mi])])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'Lean.Parser.Term.have.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.have
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`mi []]
     [(Term.typeSpec ":" («term_<_» (Algebra.Abs.«term|_|» "|" («term_/_» (numLit "1") "/" `m) "|") "<" (numLit "1")))]
     ":="
     (Term.app
      (Term.proj
       (Term.app `le_of_eqₓ [(Term.app `abs_of_pos [(Term.app (Term.proj `one_div_pos "." `mpr) [`m0])])])
       "."
       `trans_lt)
      [(Term.app (Term.proj (Term.app `div_lt_one [`m0]) "." `mpr) [`m1])])))
   []
   (calc
    "calc"
    [(calcStep
      («term_<_»
       (Topology.Algebra.InfiniteSum.«term∑'_,_»
        "∑'"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
        ", "
        («term_/_»
         (numLit "1")
         "/"
         (Cardinal.SetTheory.Cofinality.«term_^_»
          `m
          "^"
          (Nat.Data.Nat.Factorial.Basic.term_!
           (Init.Logic.«term_+_» `i "+" (Init.Logic.«term_+_» `n "+" (numLit "1")))
           "!"))))
       "<"
       (Topology.Algebra.InfiniteSum.«term∑'_,_»
        "∑'"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
        ", "
        («term_/_»
         (numLit "1")
         "/"
         (Cardinal.SetTheory.Cofinality.«term_^_»
          `m
          "^"
          (Init.Logic.«term_+_»
           `i
           "+"
           (Nat.Data.Nat.Factorial.Basic.term_! (Init.Logic.«term_+_» `n "+" (numLit "1")) "!"))))))
      ":="
      (Term.app
       `tsum_lt_tsum_of_nonneg
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`b] [])]
          "=>"
          (Term.app (Term.proj `one_div_nonneg "." `mpr) [(Term.app `pow_nonneg [`m0.le (Term.hole "_")])])))
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`b] [])]
          "=>"
          (Term.app
           `one_div_pow_le_one_div_pow_of_le
           [`m1.le (Term.app `b.add_factorial_succ_le_factorial_add_succ [`n])])))
        (Term.app
         `one_div_pow_strict_mono
         [`m1 (Term.app `n.add_factorial_succ_lt_factorial_add_succ [(Term.proj `rfl "." `le)])])
        (Term.app
         `summable_one_div_pow_of_le
         [`m1 (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j] [])] "=>" (Term.app `Nat.Le.intro [`rfl])))])]))
     (calcStep
      («term_=_»
       (Term.hole "_")
       "="
       (Topology.Algebra.InfiniteSum.«term∑'_,_»
        "∑'"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
        ", "
        (Finset.Data.Finset.Fold.«term_*_»
         (Cardinal.SetTheory.Cofinality.«term_^_» («term_/_» (numLit "1") "/" `m) "^" `i)
         "*"
         («term_/_»
          (numLit "1")
          "/"
          (Cardinal.SetTheory.Cofinality.«term_^_»
           `m
           "^"
           (Nat.Data.Nat.Factorial.Basic.term_! (Init.Logic.«term_+_» `n "+" (numLit "1")) "!"))))))
      ":="
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group (Tactic.congr "congr" [] []) [])
          (group (Tactic.ext "ext" [(Tactic.rcasesPat.one `i)] []) [])
          (group
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `pow_addₓ)
              ","
              (Tactic.rwRule ["←"] `div_div_eq_div_mul)
              ","
              (Tactic.rwRule [] `div_eq_mul_one_div)
              ","
              (Tactic.rwRule ["←"] (Term.app `one_div_pow [`i]))]
             "]")
            [])
           [])]))))
     (calcStep
      («term_=_»
       (Term.hole "_")
       "="
       (Finset.Data.Finset.Fold.«term_*_»
        (Topology.Algebra.InfiniteSum.«term∑'_,_»
         "∑'"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
         ", "
         (Cardinal.SetTheory.Cofinality.«term_^_» («term_/_» (numLit "1") "/" `m) "^" `i))
        "*"
        («term_/_»
         (numLit "1")
         "/"
         (Cardinal.SetTheory.Cofinality.«term_^_»
          `m
          "^"
          (Nat.Data.Nat.Factorial.Basic.term_! (Init.Logic.«term_+_» `n "+" (numLit "1")) "!")))))
      ":="
      `tsum_mul_right)
     (calcStep
      («term_=_»
       (Term.hole "_")
       "="
       (Finset.Data.Finset.Fold.«term_*_»
        (Init.Logic.«term_⁻¹» («term_-_» (numLit "1") "-" («term_/_» (numLit "1") "/" `m)) "⁻¹")
        "*"
        («term_/_»
         (numLit "1")
         "/"
         (Cardinal.SetTheory.Cofinality.«term_^_»
          `m
          "^"
          (Nat.Data.Nat.Factorial.Basic.term_! (Init.Logic.«term_+_» `n "+" (numLit "1")) "!")))))
      ":="
      (Term.app
       (Term.proj `mul_eq_mul_right_iff "." `mpr)
       [(Term.app `Or.inl [(Term.app `tsum_geometric_of_abs_lt_1 [`mi])])]))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'Lean.Parser.Term.have.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (calc
   "calc"
   [(calcStep
     («term_<_»
      (Topology.Algebra.InfiniteSum.«term∑'_,_»
       "∑'"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
       ", "
       («term_/_»
        (numLit "1")
        "/"
        (Cardinal.SetTheory.Cofinality.«term_^_»
         `m
         "^"
         (Nat.Data.Nat.Factorial.Basic.term_!
          (Init.Logic.«term_+_» `i "+" (Init.Logic.«term_+_» `n "+" (numLit "1")))
          "!"))))
      "<"
      (Topology.Algebra.InfiniteSum.«term∑'_,_»
       "∑'"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
       ", "
       («term_/_»
        (numLit "1")
        "/"
        (Cardinal.SetTheory.Cofinality.«term_^_»
         `m
         "^"
         (Init.Logic.«term_+_»
          `i
          "+"
          (Nat.Data.Nat.Factorial.Basic.term_! (Init.Logic.«term_+_» `n "+" (numLit "1")) "!"))))))
     ":="
     (Term.app
      `tsum_lt_tsum_of_nonneg
      [(Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`b] [])]
         "=>"
         (Term.app (Term.proj `one_div_nonneg "." `mpr) [(Term.app `pow_nonneg [`m0.le (Term.hole "_")])])))
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`b] [])]
         "=>"
         (Term.app
          `one_div_pow_le_one_div_pow_of_le
          [`m1.le (Term.app `b.add_factorial_succ_le_factorial_add_succ [`n])])))
       (Term.app
        `one_div_pow_strict_mono
        [`m1 (Term.app `n.add_factorial_succ_lt_factorial_add_succ [(Term.proj `rfl "." `le)])])
       (Term.app
        `summable_one_div_pow_of_le
        [`m1 (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j] [])] "=>" (Term.app `Nat.Le.intro [`rfl])))])]))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Topology.Algebra.InfiniteSum.«term∑'_,_»
       "∑'"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
       ", "
       (Finset.Data.Finset.Fold.«term_*_»
        (Cardinal.SetTheory.Cofinality.«term_^_» («term_/_» (numLit "1") "/" `m) "^" `i)
        "*"
        («term_/_»
         (numLit "1")
         "/"
         (Cardinal.SetTheory.Cofinality.«term_^_»
          `m
          "^"
          (Nat.Data.Nat.Factorial.Basic.term_! (Init.Logic.«term_+_» `n "+" (numLit "1")) "!"))))))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.congr "congr" [] []) [])
         (group (Tactic.ext "ext" [(Tactic.rcasesPat.one `i)] []) [])
         (group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `pow_addₓ)
             ","
             (Tactic.rwRule ["←"] `div_div_eq_div_mul)
             ","
             (Tactic.rwRule [] `div_eq_mul_one_div)
             ","
             (Tactic.rwRule ["←"] (Term.app `one_div_pow [`i]))]
            "]")
           [])
          [])]))))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Finset.Data.Finset.Fold.«term_*_»
       (Topology.Algebra.InfiniteSum.«term∑'_,_»
        "∑'"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
        ", "
        (Cardinal.SetTheory.Cofinality.«term_^_» («term_/_» (numLit "1") "/" `m) "^" `i))
       "*"
       («term_/_»
        (numLit "1")
        "/"
        (Cardinal.SetTheory.Cofinality.«term_^_»
         `m
         "^"
         (Nat.Data.Nat.Factorial.Basic.term_! (Init.Logic.«term_+_» `n "+" (numLit "1")) "!")))))
     ":="
     `tsum_mul_right)
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Finset.Data.Finset.Fold.«term_*_»
       (Init.Logic.«term_⁻¹» («term_-_» (numLit "1") "-" («term_/_» (numLit "1") "/" `m)) "⁻¹")
       "*"
       («term_/_»
        (numLit "1")
        "/"
        (Cardinal.SetTheory.Cofinality.«term_^_»
         `m
         "^"
         (Nat.Data.Nat.Factorial.Basic.term_! (Init.Logic.«term_+_» `n "+" (numLit "1")) "!")))))
     ":="
     (Term.app
      (Term.proj `mul_eq_mul_right_iff "." `mpr)
      [(Term.app `Or.inl [(Term.app `tsum_geometric_of_abs_lt_1 [`mi])])]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calc', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj `mul_eq_mul_right_iff "." `mpr)
   [(Term.app `Or.inl [(Term.app `tsum_geometric_of_abs_lt_1 [`mi])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Or.inl [(Term.app `tsum_geometric_of_abs_lt_1 [`mi])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `tsum_geometric_of_abs_lt_1 [`mi])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mi
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `tsum_geometric_of_abs_lt_1
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `tsum_geometric_of_abs_lt_1 [`mi]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Or.inl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `Or.inl [(Term.paren "(" [(Term.app `tsum_geometric_of_abs_lt_1 [`mi]) []] ")")]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `mul_eq_mul_right_iff "." `mpr)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `mul_eq_mul_right_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.hole "_")
   "="
   (Finset.Data.Finset.Fold.«term_*_»
    (Init.Logic.«term_⁻¹» («term_-_» (numLit "1") "-" («term_/_» (numLit "1") "/" `m)) "⁻¹")
    "*"
    («term_/_»
     (numLit "1")
     "/"
     (Cardinal.SetTheory.Cofinality.«term_^_»
      `m
      "^"
      (Nat.Data.Nat.Factorial.Basic.term_! (Init.Logic.«term_+_» `n "+" (numLit "1")) "!")))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   (Init.Logic.«term_⁻¹» («term_-_» (numLit "1") "-" («term_/_» (numLit "1") "/" `m)) "⁻¹")
   "*"
   («term_/_»
    (numLit "1")
    "/"
    (Cardinal.SetTheory.Cofinality.«term_^_»
     `m
     "^"
     (Nat.Data.Nat.Factorial.Basic.term_! (Init.Logic.«term_+_» `n "+" (numLit "1")) "!"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_/_»
   (numLit "1")
   "/"
   (Cardinal.SetTheory.Cofinality.«term_^_»
    `m
    "^"
    (Nat.Data.Nat.Factorial.Basic.term_! (Init.Logic.«term_+_» `n "+" (numLit "1")) "!")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Cardinal.SetTheory.Cofinality.«term_^_»
   `m
   "^"
   (Nat.Data.Nat.Factorial.Basic.term_! (Init.Logic.«term_+_» `n "+" (numLit "1")) "!"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Nat.Data.Nat.Factorial.Basic.term_! (Init.Logic.«term_+_» `n "+" (numLit "1")) "!")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Nat.Data.Nat.Factorial.Basic.term_!', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10000, term))
  (Init.Logic.«term_+_» `n "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 10000, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10000, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1024, (none, [anonymous]) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Cardinal.SetTheory.Cofinality.«term_^_»
   `m
   "^"
   (Nat.Data.Nat.Factorial.Basic.term_! (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")") "!"))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Init.Logic.«term_⁻¹» («term_-_» (numLit "1") "-" («term_/_» (numLit "1") "/" `m)) "⁻¹")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_⁻¹»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  («term_-_» (numLit "1") "-" («term_/_» (numLit "1") "/" `m))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_/_» (numLit "1") "/" `m)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term_-_» (numLit "1") "-" («term_/_» (numLit "1") "/" `m)) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  `tsum_mul_right
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.hole "_")
   "="
   (Finset.Data.Finset.Fold.«term_*_»
    (Topology.Algebra.InfiniteSum.«term∑'_,_»
     "∑'"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
     ", "
     (Cardinal.SetTheory.Cofinality.«term_^_» («term_/_» (numLit "1") "/" `m) "^" `i))
    "*"
    («term_/_»
     (numLit "1")
     "/"
     (Cardinal.SetTheory.Cofinality.«term_^_»
      `m
      "^"
      (Nat.Data.Nat.Factorial.Basic.term_! (Init.Logic.«term_+_» `n "+" (numLit "1")) "!")))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   (Topology.Algebra.InfiniteSum.«term∑'_,_»
    "∑'"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
    ", "
    (Cardinal.SetTheory.Cofinality.«term_^_» («term_/_» (numLit "1") "/" `m) "^" `i))
   "*"
   («term_/_»
    (numLit "1")
    "/"
    (Cardinal.SetTheory.Cofinality.«term_^_»
     `m
     "^"
     (Nat.Data.Nat.Factorial.Basic.term_! (Init.Logic.«term_+_» `n "+" (numLit "1")) "!"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_/_»
   (numLit "1")
   "/"
   (Cardinal.SetTheory.Cofinality.«term_^_»
    `m
    "^"
    (Nat.Data.Nat.Factorial.Basic.term_! (Init.Logic.«term_+_» `n "+" (numLit "1")) "!")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Cardinal.SetTheory.Cofinality.«term_^_»
   `m
   "^"
   (Nat.Data.Nat.Factorial.Basic.term_! (Init.Logic.«term_+_» `n "+" (numLit "1")) "!"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Nat.Data.Nat.Factorial.Basic.term_! (Init.Logic.«term_+_» `n "+" (numLit "1")) "!")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Nat.Data.Nat.Factorial.Basic.term_!', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10000, term))
  (Init.Logic.«term_+_» `n "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 10000, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10000, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1024, (none, [anonymous]) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Cardinal.SetTheory.Cofinality.«term_^_»
   `m
   "^"
   (Nat.Data.Nat.Factorial.Basic.term_! (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")") "!"))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Topology.Algebra.InfiniteSum.«term∑'_,_»
   "∑'"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
   ", "
   (Cardinal.SetTheory.Cofinality.«term_^_» («term_/_» (numLit "1") "/" `m) "^" `i))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Algebra.InfiniteSum.«term∑'_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Cardinal.SetTheory.Cofinality.«term_^_» («term_/_» (numLit "1") "/" `m) "^" `i)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cofinality.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  («term_/_» (numLit "1") "/" `m)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1 >? 70, (some 71, term) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 0, (some 0, term) <=? (none, [anonymous])
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
/-- Partial inequality, works with `m ∈ ℝ` satisfying `1 < m`. -/
  theorem
    tsum_one_div_pow_factorial_lt
    ( n : ℕ ) { m : ℝ } ( m1 : 1 < m ) : ∑' i : ℕ , 1 / m ^ i + n + 1 ! < 1 - 1 / m ⁻¹ * 1 / m ^ n + 1 !
    :=
      have
        m0 : 0 < m := zero_lt_one . trans m1
        have
          mi : | 1 / m | < 1 := le_of_eqₓ abs_of_pos one_div_pos . mpr m0 . trans_lt div_lt_one m0 . mpr m1
          calc
            ∑' i , 1 / m ^ i + n + 1 ! < ∑' i , 1 / m ^ i + n + 1 !
                :=
                tsum_lt_tsum_of_nonneg
                  fun b => one_div_nonneg . mpr pow_nonneg m0.le _
                    fun b => one_div_pow_le_one_div_pow_of_le m1.le b.add_factorial_succ_le_factorial_add_succ n
                    one_div_pow_strict_mono m1 n.add_factorial_succ_lt_factorial_add_succ rfl . le
                    summable_one_div_pow_of_le m1 fun j => Nat.Le.intro rfl
              _ = ∑' i , 1 / m ^ i * 1 / m ^ n + 1 !
                :=
                by congr ext i rw [ pow_addₓ , ← div_div_eq_div_mul , div_eq_mul_one_div , ← one_div_pow i ]
              _ = ∑' i , 1 / m ^ i * 1 / m ^ n + 1 ! := tsum_mul_right
              _ = 1 - 1 / m ⁻¹ * 1 / m ^ n + 1 ! := mul_eq_mul_right_iff . mpr Or.inl tsum_geometric_of_abs_lt_1 mi

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:57:31: expecting tactic arg
theorem aux_calc (n : ℕ) {m : ℝ} (hm : 2 ≤ m) : ((1 - 1 / m)⁻¹*1 / (m^(n+1)!)) ≤ 1 / ((m^n !)^n) :=
  calc ((1 - 1 / m)⁻¹*1 / (m^(n+1)!)) ≤ 2*1 / (m^(n+1)!) :=
    mul_mono_nonneg (one_div_nonneg.mpr (pow_nonneg (zero_le_two.trans hm) _)) (sub_one_div_inv_le_two hm)
    _ = 2 / (m^(n+1)!) := mul_one_div 2 _
    _ = 2 / (m^n !*n+1) := congr_argₓ ((· / ·) 2) (congr_argₓ (pow m) (mul_commₓ _ _))
    _ ≤ 1 / (m^n !*n) := by
    apply (div_le_div_iff _ _).mpr
    conv_rhs => rw [one_mulₓ, mul_addₓ, pow_addₓ, mul_oneₓ, pow_mulₓ, mul_commₓ, ← pow_mulₓ]
    apply (mul_le_mul_right _).mpr
    any_goals {
    }
    exact trans (trans hm (pow_oneₓ _).symm.le) (pow_mono (one_le_two.trans hm) n.factorial_pos)
    _ = 1 / ((m^n !)^n) := congr_argₓ ((· / ·) 1) (pow_mulₓ m n ! n)
    

/-!  Starting from here, we specialize to the case in which `m` is a natural number. -/


/--   The sum of the `k` initial terms of the Liouville number to base `m` is a ratio of natural
numbers where the denominator is `m ^ k!`. -/
theorem liouville_number_rat_initial_terms {m : ℕ} (hm : 0 < m) (k : ℕ) :
    ∃ p : ℕ, liouville_number_initial_terms m k = p / (m^k !) := by
  induction' k with k h
  ·
    exact
      ⟨1, by
        rw [liouville_number_initial_terms, range_one, sum_singleton, Nat.cast_one]⟩
  ·
    rcases h with ⟨p_k, h_k⟩
    use (p_k*m^(k+1)! - k !)+1
    unfold liouville_number_initial_terms  at h_k⊢
    rw [sum_range_succ, h_k, div_add_div, div_eq_div_iff, add_mulₓ]
    ·
      norm_cast
      rw [add_mulₓ, one_mulₓ, Nat.factorial_succ,
        show (k.succ*k !) - k ! = (k.succ - 1)*k !by
          rw [tsub_mul, one_mulₓ],
        Nat.succ_sub_one, add_mulₓ, one_mulₓ, pow_addₓ]
      simp [mul_assocₓ]
    refine' mul_ne_zero_iff.mpr ⟨_, _⟩
    all_goals
      exact pow_ne_zero _ (nat.cast_ne_zero.mpr hm.ne.symm)

theorem is_liouville {m : ℕ} (hm : 2 ≤ m) : Liouville (liouville_number m) := by
  have mZ1 : 1 < (m : ℤ) := by
    norm_cast
    exact one_lt_two.trans_le hm
  have m1 : 1 < (m : ℝ) := by
    norm_cast
    exact one_lt_two.trans_le hm
  intro n
  rcases liouville_number_rat_initial_terms (zero_lt_two.trans_le hm) n with ⟨p, hp⟩
  refine' ⟨p, m^n !, one_lt_pow mZ1 n.factorial_ne_zero, _⟩
  push_cast
  rw [liouville_number_eq_initial_terms_add_tail m1 n, ← hp, add_sub_cancel',
    abs_of_nonneg (liouville_number_tail_pos m1 _).le]
  exact
    ⟨((lt_add_iff_pos_right _).mpr (liouville_number_tail_pos m1 n)).Ne.symm,
      (tsum_one_div_pow_factorial_lt n m1).trans_le (aux_calc _ (nat.cast_two.symm.le.trans (nat.cast_le.mpr hm)))⟩

theorem is_transcendental {m : ℕ} (hm : 2 ≤ m) : _root_.transcendental ℤ (liouville_number m) :=
  Transcendental (is_liouville hm)

end Liouville

