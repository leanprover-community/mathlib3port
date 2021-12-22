import Mathbin.Analysis.Calculus.FormalMultilinearSeries
import Mathbin.Data.Equiv.Fin

/-!
# Analytic functions

A function is analytic in one dimension around `0` if it can be written as a converging power series
`Σ pₙ zⁿ`. This definition can be extended to any dimension (even in infinite dimension) by
requiring that `pₙ` is a continuous `n`-multilinear map. In general, `pₙ` is not unique (in two
dimensions, taking `p₂ (x, y) (x', y') = x y'` or `y x'` gives the same map when applied to a
vector `(x, y) (x, y)`). A way to guarantee uniqueness is to take a symmetric `pₙ`, but this is not
always possible in nonzero characteristic (in characteristic 2, the previous example has no
symmetric representative). Therefore, we do not insist on symmetry or uniqueness in the definition,
and we only require the existence of a converging series.

The general framework is important to say that the exponential map on bounded operators on a Banach
space is analytic, as well as the inverse on invertible operators.

## Main definitions

Let `p` be a formal multilinear series from `E` to `F`, i.e., `p n` is a multilinear map on `E^n`
for `n : ℕ`.

* `p.radius`: the largest `r : ℝ≥0∞` such that `∥p n∥ * r^n` grows subexponentially, defined as
  a liminf.
* `p.le_radius_of_bound`, `p.le_radius_of_bound_nnreal`, `p.le_radius_of_is_O`: if `∥p n∥ * r ^ n`
  is bounded above, then `r ≤ p.radius`;
* `p.is_o_of_lt_radius`, `p.norm_mul_pow_le_mul_pow_of_lt_radius`, `p.is_o_one_of_lt_radius`,
  `p.norm_mul_pow_le_of_lt_radius`, `p.nnnorm_mul_pow_le_of_lt_radius`: if `r < p.radius`, then
  `∥p n∥ * r ^ n` tends to zero exponentially;
* `p.lt_radius_of_is_O`: if `r ≠ 0` and `∥p n∥ * r ^ n = O(a ^ n)` for some `-1 < a < 1`, then
  `r < p.radius`;
* `p.partial_sum n x`: the sum `∑_{i = 0}^{n-1} pᵢ xⁱ`.
* `p.sum x`: the sum `∑'_{i = 0}^{∞} pᵢ xⁱ`.

Additionally, let `f` be a function from `E` to `F`.

* `has_fpower_series_on_ball f p x r`: on the ball of center `x` with radius `r`,
  `f (x + y) = ∑'_n pₙ yⁿ`.
* `has_fpower_series_at f p x`: on some ball of center `x` with positive radius, holds
  `has_fpower_series_on_ball f p x r`.
* `analytic_at 𝕜 f x`: there exists a power series `p` such that holds
  `has_fpower_series_at f p x`.

We develop the basic properties of these notions, notably:
* If a function admits a power series, it is continuous (see
  `has_fpower_series_on_ball.continuous_on` and `has_fpower_series_at.continuous_at` and
  `analytic_at.continuous_at`).
* In a complete space, the sum of a formal power series with positive radius is well defined on the
  disk of convergence, see `formal_multilinear_series.has_fpower_series_on_ball`.
* If a function admits a power series in a ball, then it is analytic at any point `y` of this ball,
  and the power series there can be expressed in terms of the initial power series `p` as
  `p.change_origin y`. See `has_fpower_series_on_ball.change_origin`. It follows in particular that
  the set of points at which a given function is analytic is open, see `is_open_analytic_at`.

## Implementation details

We only introduce the radius of convergence of a power series, as `p.radius`.
For a power series in finitely many dimensions, there is a finer (directional, coordinate-dependent)
notion, describing the polydisk of convergence. This notion is more specific, and not necessary to
build the general theory. We do not define it here.
-/


noncomputable section

variable {𝕜 : Type _} [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E] {F : Type _}
  [NormedGroup F] [NormedSpace 𝕜 F] {G : Type _} [NormedGroup G] [NormedSpace 𝕜 G]

open_locale TopologicalSpace Classical BigOperators Nnreal Filter Ennreal

open Set Filter Asymptotics

/-! ### The radius of a formal multilinear series -/


namespace FormalMultilinearSeries

variable (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0 }

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " The radius of a formal multilinear series is the largest `r` such that the sum `Σ ∥pₙ∥ ∥y∥ⁿ`\nconverges for all `∥y∥ < r`. This implies that `Σ pₙ yⁿ` converges for all `∥y∥ < r`, but these\ndefinitions are *not* equivalent in general. -/")]
  []
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `radius [])
  (Command.optDeclSig
   [(Term.explicitBinder "(" [`p] [":" (Term.app `FormalMultilinearSeries [`𝕜 `E `F])] [] ")")]
   [(Term.typeSpec ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))])
  (Command.declValSimple
   ":="
   (Order.CompleteLattice.«term⨆_,_»
    "⨆"
    (Lean.explicitBinders
     [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `r)] ":" (Data.Real.Nnreal.«termℝ≥0» " ℝ≥0 ") ")")
      (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `C)] ":" (Data.Real.Basic.termℝ "ℝ") ")")
      (Lean.bracketedExplicitBinders
       "("
       [(Lean.binderIdent `hr)]
       ":"
       (Term.forall
        "∀"
        [(Term.simpleBinder [`n] [])]
        ","
        («term_≤_»
         (Finset.Data.Finset.Fold.«term_*_»
          (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p [`n]) "∥")
          "*"
          («term_^_» `r "^" `n))
         "≤"
         `C))
       ")")])
    ", "
    (Term.paren "(" [`r [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]] ")"))
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
  (Order.CompleteLattice.«term⨆_,_»
   "⨆"
   (Lean.explicitBinders
    [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `r)] ":" (Data.Real.Nnreal.«termℝ≥0» " ℝ≥0 ") ")")
     (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `C)] ":" (Data.Real.Basic.termℝ "ℝ") ")")
     (Lean.bracketedExplicitBinders
      "("
      [(Lean.binderIdent `hr)]
      ":"
      (Term.forall
       "∀"
       [(Term.simpleBinder [`n] [])]
       ","
       («term_≤_»
        (Finset.Data.Finset.Fold.«term_*_»
         (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p [`n]) "∥")
         "*"
         («term_^_» `r "^" `n))
        "≤"
        `C))
      ")")])
   ", "
   (Term.paren "(" [`r [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]] ")"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.CompleteLattice.«term⨆_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren "(" [`r [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Ennreal.«termℝ≥0∞»', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `r
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
    The radius of a formal multilinear series is the largest `r` such that the sum `Σ ∥pₙ∥ ∥y∥ⁿ`
    converges for all `∥y∥ < r`. This implies that `Σ pₙ yⁿ` converges for all `∥y∥ < r`, but these
    definitions are *not* equivalent in general. -/
  def
    radius
    ( p : FormalMultilinearSeries 𝕜 E F ) : ℝ≥0∞
    := ⨆ ( r : ℝ≥0 ) ( C : ℝ ) ( hr : ∀ n , ∥ p n ∥ * r ^ n ≤ C ) , ( r : ℝ≥0∞ )

/--  If `∥pₙ∥ rⁿ` is bounded in `n`, then the radius of `p` is at least `r`. -/
theorem le_radius_of_bound (C : ℝ) {r : ℝ≥0 } (h : ∀ n : ℕ, (∥p n∥*r ^ n) ≤ C) : (r : ℝ≥0∞) ≤ p.radius :=
  le_supr_of_le r $ le_supr_of_le C $ le_supr (fun _ => (r : ℝ≥0∞)) h

/--  If `∥pₙ∥ rⁿ` is bounded in `n`, then the radius of `p` is at least `r`. -/
theorem le_radius_of_bound_nnreal (C : ℝ≥0 ) {r : ℝ≥0 } (h : ∀ n : ℕ, (∥p n∥₊*r ^ n) ≤ C) : (r : ℝ≥0∞) ≤ p.radius :=
  p.le_radius_of_bound C $ fun n => by
    exact_mod_cast h n

/--  If `∥pₙ∥ rⁿ = O(1)`, as `n → ∞`, then the radius of `p` is at least `r`. -/
theorem le_radius_of_is_O (h : is_O (fun n => ∥p n∥*r ^ n) (fun n => (1 : ℝ)) at_top) : ↑r ≤ p.radius :=
  Exists.elim (is_O_one_nat_at_top_iff.1 h) $ fun C hC => p.le_radius_of_bound C $ fun n => (le_abs_self _).trans (hC n)

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `le_radius_of_eventually_le [])
  (Command.declSig
   [(Term.simpleBinder [`C] [])
    (Term.explicitBinder
     "("
     [`h]
     [":"
      (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
       "∀ᶠ"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
       " in "
       `at_top
       ", "
       («term_≤_»
        (Finset.Data.Finset.Fold.«term_*_»
         (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p [`n]) "∥")
         "*"
         («term_^_» `r "^" `n))
        "≤"
        `C))]
     []
     ")")]
   (Term.typeSpec ":" («term_≤_» (Init.Coe.«term↑_» "↑" `r) "≤" `p.radius)))
  (Command.declValSimple
   ":="
   («term_$__»
    `p.le_radius_of_is_O
    "$"
    («term_$__»
     (Term.app `is_O.of_bound [`C])
     "$"
     («term_$__»
      `h.mono
      "$"
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`n `hn] [])]
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] []) [])]))))))))
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
  («term_$__»
   `p.le_radius_of_is_O
   "$"
   («term_$__»
    (Term.app `is_O.of_bound [`C])
    "$"
    («term_$__»
     `h.mono
     "$"
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`n `hn] [])]
       "=>"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] []) [])]))))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__»
   (Term.app `is_O.of_bound [`C])
   "$"
   («term_$__»
    `h.mono
    "$"
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`n `hn] [])]
      "=>"
      (Term.byTactic
       "by"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] []) [])])))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__»
   `h.mono
   "$"
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`n `hn] [])]
     "=>"
     (Term.byTactic
      "by"
      (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] []) [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`n `hn] [])]
    "=>"
    (Term.byTactic
     "by"
     (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] []) [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simpa "simpa" [] [] [] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpa', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  `h.mono
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  (Term.app `is_O.of_bound [`C])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `C
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `is_O.of_bound
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  `p.le_radius_of_is_O
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_≤_» (Init.Coe.«term↑_» "↑" `r) "≤" `p.radius)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `p.radius
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Init.Coe.«term↑_» "↑" `r)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `r
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 999 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 999, (some 999, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.simpleBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.explicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
   "∀ᶠ"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
   " in "
   `at_top
   ", "
   («term_≤_»
    (Finset.Data.Finset.Fold.«term_*_»
     (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p [`n]) "∥")
     "*"
     («term_^_» `r "^" `n))
    "≤"
    `C))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (Finset.Data.Finset.Fold.«term_*_»
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p [`n]) "∥")
    "*"
    («term_^_» `r "^" `n))
   "≤"
   `C)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `C
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Finset.Data.Finset.Fold.«term_*_»
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p [`n]) "∥")
   "*"
   («term_^_» `r "^" `n))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_^_» `r "^" `n)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `r
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p [`n]) "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `p [`n])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_»
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p [`n]) "∥")
   "*"
   («term_^_» `r "^" `n))
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `at_top
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
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
  le_radius_of_eventually_le
  C ( h : ∀ᶠ n in at_top , ∥ p n ∥ * r ^ n ≤ C ) : ↑ r ≤ p.radius
  := p.le_radius_of_is_O $ is_O.of_bound C $ h.mono $ fun n hn => by simpa

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `le_radius_of_summable_nnnorm [])
  (Command.declSig
   [(Term.explicitBinder
     "("
     [`h]
     [":"
      (Term.app
       `Summable
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`n] [])]
          "=>"
          (Finset.Data.Finset.Fold.«term_*_»
           (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" (Term.app `p [`n]) "∥₊")
           "*"
           («term_^_» `r "^" `n))))])]
     []
     ")")]
   (Term.typeSpec ":" («term_≤_» (Init.Coe.«term↑_» "↑" `r) "≤" `p.radius)))
  (Command.declValSimple
   ":="
   («term_$__»
    (Term.app
     `p.le_radius_of_bound_nnreal
     [(Topology.Algebra.InfiniteSum.«term∑'_,_»
       "∑'"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
       ", "
       (Finset.Data.Finset.Fold.«term_*_»
        (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" (Term.app `p [`n]) "∥₊")
        "*"
        («term_^_» `r "^" `n)))])
    "$"
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.app `le_tsum' [`h (Term.hole "_")]))))
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
  («term_$__»
   (Term.app
    `p.le_radius_of_bound_nnreal
    [(Topology.Algebra.InfiniteSum.«term∑'_,_»
      "∑'"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
      ", "
      (Finset.Data.Finset.Fold.«term_*_»
       (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" (Term.app `p [`n]) "∥₊")
       "*"
       («term_^_» `r "^" `n)))])
   "$"
   (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.app `le_tsum' [`h (Term.hole "_")]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.app `le_tsum' [`h (Term.hole "_")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `le_tsum' [`h (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `le_tsum'
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
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  (Term.app
   `p.le_radius_of_bound_nnreal
   [(Topology.Algebra.InfiniteSum.«term∑'_,_»
     "∑'"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
     ", "
     (Finset.Data.Finset.Fold.«term_*_»
      (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" (Term.app `p [`n]) "∥₊")
      "*"
      («term_^_» `r "^" `n)))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Algebra.InfiniteSum.«term∑'_,_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Algebra.InfiniteSum.«term∑'_,_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Algebra.InfiniteSum.«term∑'_,_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Algebra.InfiniteSum.«term∑'_,_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Algebra.InfiniteSum.«term∑'_,_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Topology.Algebra.InfiniteSum.«term∑'_,_»
   "∑'"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
   ", "
   (Finset.Data.Finset.Fold.«term_*_»
    (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" (Term.app `p [`n]) "∥₊")
    "*"
    («term_^_» `r "^" `n)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Algebra.InfiniteSum.«term∑'_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" (Term.app `p [`n]) "∥₊")
   "*"
   («term_^_» `r "^" `n))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_^_» `r "^" `n)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `r
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" (Term.app `p [`n]) "∥₊")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥₊»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `p [`n])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
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
  le_radius_of_summable_nnnorm
  ( h : Summable fun n => ∥ p n ∥₊ * r ^ n ) : ↑ r ≤ p.radius
  := p.le_radius_of_bound_nnreal ∑' n , ∥ p n ∥₊ * r ^ n $ fun n => le_tsum' h _

theorem le_radius_of_summable (h : Summable fun n => ∥p n∥*r ^ n) : ↑r ≤ p.radius :=
  p.le_radius_of_summable_nnnorm $ by
    simp only [← coe_nnnorm] at h
    exact_mod_cast h

theorem radius_eq_top_of_forall_nnreal_is_O (h : ∀ r : ℝ≥0 , is_O (fun n => ∥p n∥*r ^ n) (fun n => (1 : ℝ)) at_top) :
    p.radius = ∞ :=
  Ennreal.eq_top_of_forall_nnreal_le $ fun r => p.le_radius_of_is_O (h r)

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `radius_eq_top_of_eventually_eq_zero [])
  (Command.declSig
   [(Term.explicitBinder
     "("
     [`h]
     [":"
      (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
       "∀ᶠ"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
       " in "
       `at_top
       ", "
       («term_=_» (Term.app `p [`n]) "=" (numLit "0")))]
     []
     ")")]
   (Term.typeSpec ":" («term_=_» `p.radius "=" (Data.Real.Ennreal.«term∞» "∞"))))
  (Command.declValSimple
   ":="
   («term_$__»
    `p.radius_eq_top_of_forall_nnreal_is_O
    "$"
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`r] [])]
      "=>"
      (Term.app
       (Term.proj (Term.app `is_O_zero [(Term.hole "_") (Term.hole "_")]) "." `congr')
       [(«term_$__»
         `h.mono
         "$"
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`n `hn] [])]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `hn)] "]"] []) [])]))))))
        `eventually_eq.rfl]))))
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
  («term_$__»
   `p.radius_eq_top_of_forall_nnreal_is_O
   "$"
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`r] [])]
     "=>"
     (Term.app
      (Term.proj (Term.app `is_O_zero [(Term.hole "_") (Term.hole "_")]) "." `congr')
      [(«term_$__»
        `h.mono
        "$"
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`n `hn] [])]
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `hn)] "]"] []) [])]))))))
       `eventually_eq.rfl]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`r] [])]
    "=>"
    (Term.app
     (Term.proj (Term.app `is_O_zero [(Term.hole "_") (Term.hole "_")]) "." `congr')
     [(«term_$__»
       `h.mono
       "$"
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`n `hn] [])]
         "=>"
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `hn)] "]"] []) [])]))))))
      `eventually_eq.rfl])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj (Term.app `is_O_zero [(Term.hole "_") (Term.hole "_")]) "." `congr')
   [(«term_$__»
     `h.mono
     "$"
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`n `hn] [])]
       "=>"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `hn)] "]"] []) [])]))))))
    `eventually_eq.rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `eventually_eq.rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  («term_$__»
   `h.mono
   "$"
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`n `hn] [])]
     "=>"
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `hn)] "]"] []) [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`n `hn] [])]
    "=>"
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `hn)] "]"] []) [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `hn)] "]"] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `hn)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hn
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  `h.mono
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term_$__»
   `h.mono
   "$"
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`n `hn] [])]
     "=>"
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `hn)] "]"] []) [])]))))))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.app `is_O_zero [(Term.hole "_") (Term.hole "_")]) "." `congr')
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `is_O_zero [(Term.hole "_") (Term.hole "_")])
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
  `is_O_zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `is_O_zero [(Term.hole "_") (Term.hole "_")]) []]
 ")")
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
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  `p.radius_eq_top_of_forall_nnreal_is_O
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_» `p.radius "=" (Data.Real.Ennreal.«term∞» "∞"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Data.Real.Ennreal.«term∞» "∞")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Ennreal.«term∞»', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `p.radius
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.simpleBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.explicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
   "∀ᶠ"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
   " in "
   `at_top
   ", "
   («term_=_» (Term.app `p [`n]) "=" (numLit "0")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» (Term.app `p [`n]) "=" (numLit "0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `p [`n])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `at_top
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
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
  radius_eq_top_of_eventually_eq_zero
  ( h : ∀ᶠ n in at_top , p n = 0 ) : p.radius = ∞
  :=
    p.radius_eq_top_of_forall_nnreal_is_O
      $
      fun r => is_O_zero _ _ . congr' h.mono $ fun n hn => by simp [ hn ] eventually_eq.rfl

theorem radius_eq_top_of_forall_image_add_eq_zero (n : ℕ) (hn : ∀ m, p (m+n) = 0) : p.radius = ∞ :=
  p.radius_eq_top_of_eventually_eq_zero $ mem_at_top_sets.2 ⟨n, fun k hk => tsub_add_cancel_of_le hk ▸ hn _⟩

/--  For `r` strictly smaller than the radius of `p`, then `∥pₙ∥ rⁿ` tends to zero exponentially:
for some `0 < a < 1`, `∥p n∥ rⁿ = o(aⁿ)`. -/
theorem is_o_of_lt_radius (h : ↑r < p.radius) : ∃ a ∈ Ioo (0 : ℝ) 1, is_o (fun n => ∥p n∥*r ^ n) (pow a) at_top := by
  rw [(tfae_exists_lt_is_o_pow (fun n => ∥p n∥*r ^ n) 1).out 1 4]
  simp only [radius, lt_supr_iff] at h
  rcases h with ⟨t, C, hC, rt⟩
  rw [Ennreal.coe_lt_coe, ← Nnreal.coe_lt_coe] at rt
  have : 0 < (t : ℝ)
  exact r.coe_nonneg.trans_lt rt
  rw [← div_lt_one this] at rt
  refine' ⟨_, rt, C, Or.inr zero_lt_one, fun n => _⟩
  calc |∥p n∥*r ^ n| = (∥p n∥*t ^ n)*(r / t) ^ n := by
    field_simp [mul_right_commₓ, abs_mul, this.ne']_ ≤ C*(r / t) ^ n :=
    mul_le_mul_of_nonneg_right (hC n) (pow_nonneg (div_nonneg r.2 t.2) _)

/--  For `r` strictly smaller than the radius of `p`, then `∥pₙ∥ rⁿ = o(1)`. -/
theorem is_o_one_of_lt_radius (h : ↑r < p.radius) : is_o (fun n => ∥p n∥*r ^ n) (fun _ => 1 : ℕ → ℝ) at_top :=
  let ⟨a, ha, hp⟩ := p.is_o_of_lt_radius h
  hp.trans $ (is_o_pow_pow_of_lt_left ha.1.le ha.2).congr (fun n => rfl) one_pow

/--  For `r` strictly smaller than the radius of `p`, then `∥pₙ∥ rⁿ` tends to zero exponentially:
for some `0 < a < 1` and `C > 0`,  `∥p n∥ * r ^ n ≤ C * a ^ n`. -/
theorem norm_mul_pow_le_mul_pow_of_lt_radius (h : ↑r < p.radius) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C > 0, ∀ n, (∥p n∥*r ^ n) ≤ C*a ^ n := by
  rcases((tfae_exists_lt_is_o_pow (fun n => ∥p n∥*r ^ n) 1).out 1 5).mp (p.is_o_of_lt_radius h) with ⟨a, ha, C, hC, H⟩
  exact ⟨a, ha, C, hC, fun n => (le_abs_self _).trans (H n)⟩

/--  If `r ≠ 0` and `∥pₙ∥ rⁿ = O(aⁿ)` for some `-1 < a < 1`, then `r < p.radius`. -/
theorem lt_radius_of_is_O (h₀ : r ≠ 0) {a : ℝ} (ha : a ∈ Ioo (-1 : ℝ) 1)
    (hp : is_O (fun n => ∥p n∥*r ^ n) (pow a) at_top) : ↑r < p.radius := by
  rcases((tfae_exists_lt_is_o_pow (fun n => ∥p n∥*r ^ n) 1).out 2 5).mp ⟨a, ha, hp⟩ with ⟨a, ha, C, hC, hp⟩
  rw [← pos_iff_ne_zero, ← Nnreal.coe_pos] at h₀
  lift a to ℝ≥0 using ha.1.le
  have : (r : ℝ) < r / a := by
    simpa only [div_one] using (div_lt_div_left h₀ zero_lt_one ha.1).2 ha.2
  norm_cast  at this
  rw [← Ennreal.coe_lt_coe] at this
  refine' this.trans_le (p.le_radius_of_bound C $ fun n => _)
  rw [Nnreal.coe_div, div_pow, ← mul_div_assoc, div_le_iff (pow_pos ha.1 n)]
  exact (le_abs_self _).trans (hp n)

/--  For `r` strictly smaller than the radius of `p`, then `∥pₙ∥ rⁿ` is bounded. -/
theorem norm_mul_pow_le_of_lt_radius (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0 } (h : (r : ℝ≥0∞) < p.radius) :
    ∃ C > 0, ∀ n, (∥p n∥*r ^ n) ≤ C :=
  let ⟨a, ha, C, hC, h⟩ := p.norm_mul_pow_le_mul_pow_of_lt_radius h
  ⟨C, hC, fun n => (h n).trans $ mul_le_of_le_one_right hC.lt.le (pow_le_one _ ha.1.le ha.2.le)⟩

/--  For `r` strictly smaller than the radius of `p`, then `∥pₙ∥ rⁿ` is bounded. -/
theorem norm_le_div_pow_of_pos_of_lt_radius (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0 } (h0 : 0 < r)
    (h : (r : ℝ≥0∞) < p.radius) : ∃ C > 0, ∀ n, ∥p n∥ ≤ C / r ^ n :=
  let ⟨C, hC, hp⟩ := p.norm_mul_pow_le_of_lt_radius h
  ⟨C, hC, fun n => Iff.mpr (le_div_iff (pow_pos h0 _)) (hp n)⟩

/--  For `r` strictly smaller than the radius of `p`, then `∥pₙ∥ rⁿ` is bounded. -/
theorem nnnorm_mul_pow_le_of_lt_radius (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0 } (h : (r : ℝ≥0∞) < p.radius) :
    ∃ C > 0, ∀ n, (∥p n∥₊*r ^ n) ≤ C :=
  let ⟨C, hC, hp⟩ := p.norm_mul_pow_le_of_lt_radius h
  ⟨⟨C, hC.lt.le⟩, hC, by
    exact_mod_cast hp⟩

theorem le_radius_of_tendsto (p : FormalMultilinearSeries 𝕜 E F) {l : ℝ}
    (h : tendsto (fun n => ∥p n∥*r ^ n) at_top (𝓝 l)) : ↑r ≤ p.radius :=
  p.le_radius_of_is_O (is_O_one_of_tendsto _ h)

theorem le_radius_of_summable_norm (p : FormalMultilinearSeries 𝕜 E F) (hs : Summable fun n => ∥p n∥*r ^ n) :
    ↑r ≤ p.radius :=
  p.le_radius_of_tendsto hs.tendsto_at_top_zero

theorem not_summable_norm_of_radius_lt_nnnorm (p : FormalMultilinearSeries 𝕜 E F) {x : E} (h : p.radius < ∥x∥₊) :
    ¬Summable fun n => ∥p n∥*∥x∥ ^ n := fun hs => not_le_of_lt h (p.le_radius_of_summable_norm hs)

theorem summable_norm_mul_pow (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0 } (h : ↑r < p.radius) :
    Summable fun n : ℕ => ∥p n∥*r ^ n := by
  obtain ⟨a, ha : a ∈ Ioo (0 : ℝ) 1, C, hC : 0 < C, hp⟩ := p.norm_mul_pow_le_mul_pow_of_lt_radius h
  exact
    summable_of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg r.coe_nonneg _)) hp
      ((summable_geometric_of_lt_1 ha.1.le ha.2).mul_left _)

theorem summable_norm_apply (p : FormalMultilinearSeries 𝕜 E F) {x : E} (hx : x ∈ Emetric.Ball (0 : E) p.radius) :
    Summable fun n : ℕ => ∥p n fun _ => x∥ := by
  rw [mem_emetric_ball_zero_iff] at hx
  refine'
    summable_of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ((p n).le_op_norm _).trans_eq _)
      (p.summable_norm_mul_pow hx)
  simp

theorem summable_nnnorm_mul_pow (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0 } (h : ↑r < p.radius) :
    Summable fun n : ℕ => ∥p n∥₊*r ^ n := by
  rw [← Nnreal.summable_coe]
  push_cast
  exact p.summable_norm_mul_pow h

protected theorem Summable [CompleteSpace F] (p : FormalMultilinearSeries 𝕜 E F) {x : E}
    (hx : x ∈ Emetric.Ball (0 : E) p.radius) : Summable fun n : ℕ => p n fun _ => x :=
  summable_of_summable_norm (p.summable_norm_apply hx)

theorem radius_eq_top_of_summable_norm (p : FormalMultilinearSeries 𝕜 E F)
    (hs : ∀ r : ℝ≥0 , Summable fun n => ∥p n∥*r ^ n) : p.radius = ∞ :=
  Ennreal.eq_top_of_forall_nnreal_le fun r => p.le_radius_of_summable_norm (hs r)

theorem radius_eq_top_iff_summable_norm (p : FormalMultilinearSeries 𝕜 E F) :
    p.radius = ∞ ↔ ∀ r : ℝ≥0 , Summable fun n => ∥p n∥*r ^ n := by
  constructor
  ·
    intro h r
    obtain ⟨a, ha : a ∈ Ioo (0 : ℝ) 1, C, hC : 0 < C, hp⟩ :=
      p.norm_mul_pow_le_mul_pow_of_lt_radius (show (r : ℝ≥0∞) < p.radius from h.symm ▸ Ennreal.coe_lt_top)
    refine'
      summable_of_norm_bounded (fun n => (C : ℝ)*a ^ n) ((summable_geometric_of_lt_1 ha.1.le ha.2).mul_left _) fun n =>
        _
    specialize hp n
    rwa [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg r.coe_nonneg n))]
  ·
    exact p.radius_eq_top_of_summable_norm

/--  If the radius of `p` is positive, then `∥pₙ∥` grows at most geometrically. -/
theorem le_mul_pow_of_radius_pos (p : FormalMultilinearSeries 𝕜 E F) (h : 0 < p.radius) :
    ∃ (C r : _)(hC : 0 < C)(hr : 0 < r), ∀ n, ∥p n∥ ≤ C*r ^ n := by
  rcases Ennreal.lt_iff_exists_nnreal_btwn.1 h with ⟨r, r0, rlt⟩
  have rpos : 0 < (r : ℝ) := by
    simp [Ennreal.coe_pos.1 r0]
  rcases norm_le_div_pow_of_pos_of_lt_radius p rpos rlt with ⟨C, Cpos, hCp⟩
  refine'
    ⟨C, r⁻¹, Cpos, by
      simp [rpos], fun n => _⟩
  convert hCp n
  exact inv_pow₀ _ _

/--  The radius of the sum of two formal series is at least the minimum of their two radii. -/
theorem min_radius_le_radius_add (p q : FormalMultilinearSeries 𝕜 E F) : min p.radius q.radius ≤ (p+q).radius := by
  refine' Ennreal.le_of_forall_nnreal_lt fun r hr => _
  rw [lt_min_iff] at hr
  have := ((p.is_o_one_of_lt_radius hr.1).add (q.is_o_one_of_lt_radius hr.2)).IsO
  refine' (p+q).le_radius_of_is_O ((is_O_of_le _ $ fun n => _).trans this)
  rw [← add_mulₓ, NormedField.norm_mul, NormedField.norm_mul, norm_norm]
  exact mul_le_mul_of_nonneg_right ((norm_add_le _ _).trans (le_abs_self _)) (norm_nonneg _)

@[simp]
theorem radius_neg (p : FormalMultilinearSeries 𝕜 E F) : (-p).radius = p.radius := by
  simp [radius]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " Given a formal multilinear series `p` and a vector `x`, then `p.sum x` is the sum `Σ pₙ xⁿ`. A\npriori, it only behaves well when `∥x∥ < p.radius`. -/")]
  []
  [(Command.protected "protected")]
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `Sum [])
  (Command.optDeclSig
   [(Term.explicitBinder "(" [`p] [":" (Term.app `FormalMultilinearSeries [`𝕜 `E `F])] [] ")")
    (Term.explicitBinder "(" [`x] [":" `E] [] ")")]
   [(Term.typeSpec ":" `F)])
  (Command.declValSimple
   ":="
   (Topology.Algebra.InfiniteSum.«term∑'_,_»
    "∑'"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (termℕ "ℕ")]))
    ", "
    (Term.app `p [`n (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i] [])] "=>" `x))]))
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
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (termℕ "ℕ")]))
   ", "
   (Term.app `p [`n (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i] [])] "=>" `x))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Algebra.InfiniteSum.«term∑'_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `p [`n (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i] [])] "=>" `x))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i] [])] "=>" `x))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
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
      Given a formal multilinear series `p` and a vector `x`, then `p.sum x` is the sum `Σ pₙ xⁿ`. A
      priori, it only behaves well when `∥x∥ < p.radius`. -/
    protected
  def Sum ( p : FormalMultilinearSeries 𝕜 E F ) ( x : E ) : F := ∑' n : ℕ , p n fun i => x

protected theorem HasSum [CompleteSpace F] (p : FormalMultilinearSeries 𝕜 E F) {x : E}
    (hx : x ∈ Emetric.Ball (0 : E) p.radius) : HasSum (fun n : ℕ => p n fun _ => x) (p.sum x) :=
  (p.summable hx).HasSum

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " Given a formal multilinear series `p` and a vector `x`, then `p.partial_sum n x` is the sum\n`Σ pₖ xᵏ` for `k ∈ {0,..., n-1}`. -/")]
  []
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `partial_sum [])
  (Command.optDeclSig
   [(Term.explicitBinder "(" [`p] [":" (Term.app `FormalMultilinearSeries [`𝕜 `E `F])] [] ")")
    (Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")
    (Term.explicitBinder "(" [`x] [":" `E] [] ")")]
   [(Term.typeSpec ":" `F)])
  (Command.declValSimple
   ":="
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
    " in "
    (Term.app `Finset.range [`n])
    ", "
    (Term.app
     `p
     [`k
      (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i] [(Term.typeSpec ":" (Term.app `Finₓ [`k]))])] "=>" `x))]))
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
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
   " in "
   (Term.app `Finset.range [`n])
   ", "
   (Term.app
    `p
    [`k
     (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i] [(Term.typeSpec ":" (Term.app `Finₓ [`k]))])] "=>" `x))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `p
   [`k (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i] [(Term.typeSpec ":" (Term.app `Finₓ [`k]))])] "=>" `x))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i] [(Term.typeSpec ":" (Term.app `Finₓ [`k]))])] "=>" `x))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Finₓ [`k])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Finset.range [`n])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finset.range
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
    Given a formal multilinear series `p` and a vector `x`, then `p.partial_sum n x` is the sum
    `Σ pₖ xᵏ` for `k ∈ {0,..., n-1}`. -/
  def
    partial_sum
    ( p : FormalMultilinearSeries 𝕜 E F ) ( n : ℕ ) ( x : E ) : F
    := ∑ k in Finset.range n , p k fun i : Finₓ k => x

/--  The partial sums of a formal multilinear series are continuous. -/
theorem partial_sum_continuous (p : FormalMultilinearSeries 𝕜 E F) (n : ℕ) : Continuous (p.partial_sum n) := by
  continuity

end FormalMultilinearSeries

/-! ### Expanding a function as a power series -/


section

variable {f g : E → F} {p pf pg : FormalMultilinearSeries 𝕜 E F} {x : E} {r r' : ℝ≥0∞}

/--  Given a function `f : E → F` and a formal multilinear series `p`, we say that `f` has `p` as
a power series on the ball of radius `r > 0` around `x` if `f (x + y) = ∑' pₙ yⁿ` for all `∥y∥ < r`.
-/
structure HasFpowerSeriesOnBall (f : E → F) (p : FormalMultilinearSeries 𝕜 E F) (x : E) (r : ℝ≥0∞) : Prop where
  r_le : r ≤ p.radius
  r_pos : 0 < r
  HasSum : ∀ {y}, y ∈ Emetric.Ball (0 : E) r → HasSum (fun n : ℕ => p n fun i : Finₓ n => y) (f (x+y))

/--  Given a function `f : E → F` and a formal multilinear series `p`, we say that `f` has `p` as
a power series around `x` if `f (x + y) = ∑' pₙ yⁿ` for all `y` in a neighborhood of `0`. -/
def HasFpowerSeriesAt (f : E → F) (p : FormalMultilinearSeries 𝕜 E F) (x : E) :=
  ∃ r, HasFpowerSeriesOnBall f p x r

variable (𝕜)

/--  Given a function `f : E → F`, we say that `f` is analytic at `x` if it admits a convergent power
series expansion around `x`. -/
def AnalyticAt (f : E → F) (x : E) :=
  ∃ p : FormalMultilinearSeries 𝕜 E F, HasFpowerSeriesAt f p x

variable {𝕜}

theorem HasFpowerSeriesOnBall.has_fpower_series_at (hf : HasFpowerSeriesOnBall f p x r) : HasFpowerSeriesAt f p x :=
  ⟨r, hf⟩

theorem HasFpowerSeriesAt.analytic_at (hf : HasFpowerSeriesAt f p x) : AnalyticAt 𝕜 f x :=
  ⟨p, hf⟩

theorem HasFpowerSeriesOnBall.analytic_at (hf : HasFpowerSeriesOnBall f p x r) : AnalyticAt 𝕜 f x :=
  hf.has_fpower_series_at.analytic_at

theorem HasFpowerSeriesOnBall.has_sum_sub (hf : HasFpowerSeriesOnBall f p x r) {y : E} (hy : y ∈ Emetric.Ball x r) :
    HasSum (fun n : ℕ => p n fun i => y - x) (f y) :=
  have : y - x ∈ Emetric.Ball (0 : E) r := by
    simpa [edist_eq_coe_nnnorm_sub] using hy
  by
  simpa only [add_sub_cancel'_right] using hf.has_sum this

theorem HasFpowerSeriesOnBall.radius_pos (hf : HasFpowerSeriesOnBall f p x r) : 0 < p.radius :=
  lt_of_lt_of_leₓ hf.r_pos hf.r_le

theorem HasFpowerSeriesAt.radius_pos (hf : HasFpowerSeriesAt f p x) : 0 < p.radius :=
  let ⟨r, hr⟩ := hf
  hr.radius_pos

theorem HasFpowerSeriesOnBall.mono (hf : HasFpowerSeriesOnBall f p x r) (r'_pos : 0 < r') (hr : r' ≤ r) :
    HasFpowerSeriesOnBall f p x r' :=
  ⟨le_transₓ hr hf.1, r'_pos, fun y hy => hf.has_sum (Emetric.ball_subset_ball hr hy)⟩

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `HasFpowerSeriesAt.eventually [])
  (Command.declSig
   [(Term.explicitBinder "(" [`hf] [":" (Term.app `HasFpowerSeriesAt [`f `p `x])] [] ")")]
   (Term.typeSpec
    ":"
    (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
     "∀ᶠ"
     (Lean.explicitBinders
      (Lean.unbracketedExplicitBinders [(Lean.binderIdent `r)] [":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞")]))
     " in "
     (Topology.Basic.«term𝓝[>]_» "𝓝[>] " (numLit "0"))
     ", "
     (Term.app `HasFpowerSeriesOnBall [`f `p `x `r]))))
  (Command.declValSimple
   ":="
   (Term.let
    "let"
    (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`r "," `hr] "⟩") [] [] ":=" `hf))
    []
    («term_$__»
     (Term.app
      `mem_of_superset
      [(Term.app `Ioo_mem_nhds_within_Ioi [(Term.app (Term.proj `left_mem_Ico "." (fieldIdx "2")) [`hr.r_pos])])])
     "$"
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`r' `hr'] [])]
       "=>"
       (Term.app
        `hr.mono
        [(Term.proj `hr' "." (fieldIdx "1")) (Term.proj (Term.proj `hr' "." (fieldIdx "2")) "." `le)])))))
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
  (Term.let
   "let"
   (Term.letDecl (Term.letPatDecl (Term.anonymousCtor "⟨" [`r "," `hr] "⟩") [] [] ":=" `hf))
   []
   («term_$__»
    (Term.app
     `mem_of_superset
     [(Term.app `Ioo_mem_nhds_within_Ioi [(Term.app (Term.proj `left_mem_Ico "." (fieldIdx "2")) [`hr.r_pos])])])
    "$"
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`r' `hr'] [])]
      "=>"
      (Term.app
       `hr.mono
       [(Term.proj `hr' "." (fieldIdx "1")) (Term.proj (Term.proj `hr' "." (fieldIdx "2")) "." `le)])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'Lean.Parser.Term.let.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__»
   (Term.app
    `mem_of_superset
    [(Term.app `Ioo_mem_nhds_within_Ioi [(Term.app (Term.proj `left_mem_Ico "." (fieldIdx "2")) [`hr.r_pos])])])
   "$"
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`r' `hr'] [])]
     "=>"
     (Term.app
      `hr.mono
      [(Term.proj `hr' "." (fieldIdx "1")) (Term.proj (Term.proj `hr' "." (fieldIdx "2")) "." `le)]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`r' `hr'] [])]
    "=>"
    (Term.app `hr.mono [(Term.proj `hr' "." (fieldIdx "1")) (Term.proj (Term.proj `hr' "." (fieldIdx "2")) "." `le)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `hr.mono [(Term.proj `hr' "." (fieldIdx "1")) (Term.proj (Term.proj `hr' "." (fieldIdx "2")) "." `le)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.proj `hr' "." (fieldIdx "2")) "." `le)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `hr' "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hr'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `hr' "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hr'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hr.mono
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
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  (Term.app
   `mem_of_superset
   [(Term.app `Ioo_mem_nhds_within_Ioi [(Term.app (Term.proj `left_mem_Ico "." (fieldIdx "2")) [`hr.r_pos])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Ioo_mem_nhds_within_Ioi [(Term.app (Term.proj `left_mem_Ico "." (fieldIdx "2")) [`hr.r_pos])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj `left_mem_Ico "." (fieldIdx "2")) [`hr.r_pos])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hr.r_pos
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `left_mem_Ico "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `left_mem_Ico
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app (Term.proj `left_mem_Ico "." (fieldIdx "2")) [`hr.r_pos]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Ioo_mem_nhds_within_Ioi
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `Ioo_mem_nhds_within_Ioi
   [(Term.paren "(" [(Term.app (Term.proj `left_mem_Ico "." (fieldIdx "2")) [`hr.r_pos]) []] ")")])
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mem_of_superset
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letDecl', expected 'Lean.Parser.Term.letDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letPatDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  `hf
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`r "," `hr] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `r
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
   "∀ᶠ"
   (Lean.explicitBinders
    (Lean.unbracketedExplicitBinders [(Lean.binderIdent `r)] [":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞")]))
   " in "
   (Topology.Basic.«term𝓝[>]_» "𝓝[>] " (numLit "0"))
   ", "
   (Term.app `HasFpowerSeriesOnBall [`f `p `x `r]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `HasFpowerSeriesOnBall [`f `p `x `r])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `r
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `HasFpowerSeriesOnBall
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Topology.Basic.«term𝓝[>]_» "𝓝[>] " (numLit "0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Basic.«term𝓝[>]_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 100, term) <=? (none, [anonymous])
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
protected
  theorem
    HasFpowerSeriesAt.eventually
    ( hf : HasFpowerSeriesAt f p x ) : ∀ᶠ r : ℝ≥0∞ in 𝓝[>] 0 , HasFpowerSeriesOnBall f p x r
    :=
      let
        ⟨ r , hr ⟩ := hf
        mem_of_superset Ioo_mem_nhds_within_Ioi left_mem_Ico . 2 hr.r_pos $ fun r' hr' => hr.mono hr' . 1 hr' . 2 . le

theorem HasFpowerSeriesOnBall.add (hf : HasFpowerSeriesOnBall f pf x r) (hg : HasFpowerSeriesOnBall g pg x r) :
    HasFpowerSeriesOnBall (f+g) (pf+pg) x r :=
  { r_le := le_transₓ (le_min_iff.2 ⟨hf.r_le, hg.r_le⟩) (pf.min_radius_le_radius_add pg), r_pos := hf.r_pos,
    HasSum := fun y hy => (hf.has_sum hy).add (hg.has_sum hy) }

theorem HasFpowerSeriesAt.add (hf : HasFpowerSeriesAt f pf x) (hg : HasFpowerSeriesAt g pg x) :
    HasFpowerSeriesAt (f+g) (pf+pg) x := by
  rcases(hf.eventually.and hg.eventually).exists with ⟨r, hr⟩
  exact ⟨r, hr.1.add hr.2⟩

theorem AnalyticAt.add (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x) : AnalyticAt 𝕜 (f+g) x :=
  let ⟨pf, hpf⟩ := hf
  let ⟨qf, hqf⟩ := hg
  (hpf.add hqf).AnalyticAt

theorem HasFpowerSeriesOnBall.neg (hf : HasFpowerSeriesOnBall f pf x r) : HasFpowerSeriesOnBall (-f) (-pf) x r :=
  { r_le := by
      rw [pf.radius_neg]
      exact hf.r_le,
    r_pos := hf.r_pos, HasSum := fun y hy => (hf.has_sum hy).neg }

theorem HasFpowerSeriesAt.neg (hf : HasFpowerSeriesAt f pf x) : HasFpowerSeriesAt (-f) (-pf) x :=
  let ⟨rf, hrf⟩ := hf
  hrf.neg.has_fpower_series_at

theorem AnalyticAt.neg (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (-f) x :=
  let ⟨pf, hpf⟩ := hf
  hpf.neg.analytic_at

theorem HasFpowerSeriesOnBall.sub (hf : HasFpowerSeriesOnBall f pf x r) (hg : HasFpowerSeriesOnBall g pg x r) :
    HasFpowerSeriesOnBall (f - g) (pf - pg) x r := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem HasFpowerSeriesAt.sub (hf : HasFpowerSeriesAt f pf x) (hg : HasFpowerSeriesAt g pg x) :
    HasFpowerSeriesAt (f - g) (pf - pg) x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem AnalyticAt.sub (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x) : AnalyticAt 𝕜 (f - g) x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (i «expr ≠ » 0)
theorem HasFpowerSeriesOnBall.coeff_zero (hf : HasFpowerSeriesOnBall f pf x r) (v : Finₓ 0 → E) : pf 0 v = f x := by
  have v_eq : v = fun i => 0 := Subsingleton.elimₓ _ _
  have zero_mem : (0 : E) ∈ Emetric.Ball (0 : E) r := by
    simp [hf.r_pos]
  have : ∀ i _ : i ≠ 0, (pf i fun j => 0) = 0 := by
    intro i hi
    have : 0 < i := pos_iff_ne_zero.2 hi
    exact ContinuousMultilinearMap.map_coord_zero _ (⟨0, this⟩ : Finₓ i) rfl
  have A := (hf.has_sum zero_mem).unique (has_sum_single _ this)
  simpa [v_eq] using A.symm

theorem HasFpowerSeriesAt.coeff_zero (hf : HasFpowerSeriesAt f pf x) (v : Finₓ 0 → E) : pf 0 v = f x :=
  let ⟨rf, hrf⟩ := hf
  hrf.coeff_zero v

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " If a function admits a power series expansion, then it is exponentially close to the partial\nsums of this power series on strict subdisks of the disk of convergence.\n\nThis version provides an upper estimate that decreases both in `∥y∥` and `n`. See also\n`has_fpower_series_on_ball.uniform_geometric_approx` for a weaker version. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `HasFpowerSeriesOnBall.uniform_geometric_approx' [])
  (Command.declSig
   [(Term.implicitBinder "{" [`r'] [":" (Data.Real.Nnreal.«termℝ≥0» " ℝ≥0 ")] "}")
    (Term.explicitBinder "(" [`hf] [":" (Term.app `HasFpowerSeriesOnBall [`f `p `x `r])] [] ")")
    (Term.explicitBinder
     "("
     [`h]
     [":"
      («term_<_» (Term.paren "(" [`r' [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]] ")") "<" `r)]
     []
     ")")]
   (Term.typeSpec
    ":"
    (Mathlib.ExtendedBinder.«term∃___,_»
     "∃"
     `a
     («binderTerm∈_»
      "∈"
      (Term.app
       `Ioo
       [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")") (numLit "1")]))
     ","
     (Mathlib.ExtendedBinder.«term∃___,_»
      "∃"
      `C
      (Mathlib.ExtendedBinder.«binderTerm>_» ">" (numLit "0"))
      ","
      (Term.forall
       "∀"
       []
       ","
       (Mathlib.ExtendedBinder.«term∀___,_»
        "∀"
        `y
        («binderTerm∈_»
         "∈"
         (Term.app `Metric.Ball [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `E)]] ")") `r']))
        ","
        (Term.forall
         "∀"
         []
         ","
         (Term.forall
          "∀"
          [(Term.simpleBinder [`n] [])]
          ","
          («term_≤_»
           (Analysis.Normed.Group.Basic.«term∥_∥»
            "∥"
            («term_-_» (Term.app `f [(Init.Logic.«term_+_» `x "+" `y)]) "-" (Term.app `p.partial_sum [`n `y]))
            "∥")
           "≤"
           (Finset.Data.Finset.Fold.«term_*_»
            `C
            "*"
            («term_^_»
             (Finset.Data.Finset.Fold.«term_*_»
              `a
              "*"
              («term_/_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥") "/" `r'))
             "^"
             `n)))))))))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.obtain
         "obtain"
         [(Tactic.rcasesPatMed
           [(Tactic.rcasesPat.tuple
             "⟨"
             [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ha)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `C)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hC)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hp)]) [])]
             "⟩")])]
         [":"
          (Mathlib.ExtendedBinder.«term∃___,_»
           "∃"
           `a
           («binderTerm∈_»
            "∈"
            (Term.app
             `Ioo
             [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
              (numLit "1")]))
           ","
           (Mathlib.ExtendedBinder.«term∃___,_»
            "∃"
            `C
            (Mathlib.ExtendedBinder.«binderTerm>_» ">" (numLit "0"))
            ","
            (Term.forall
             "∀"
             [(Term.simpleBinder [`n] [])]
             ","
             («term_≤_»
              (Finset.Data.Finset.Fold.«term_*_»
               (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p [`n]) "∥")
               "*"
               («term_^_» `r' "^" `n))
              "≤"
              (Finset.Data.Finset.Fold.«term_*_» `C "*" («term_^_» `a "^" `n))))))]
         [":=" [(Term.app `p.norm_mul_pow_le_mul_pow_of_lt_radius [(Term.app `h.trans_le [`hf.r_le])])]])
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [`a
           ","
           `ha
           ","
           («term_/_» `C "/" («term_-_» (numLit "1") "-" `a))
           ","
           (Term.app
            `div_pos
            [`hC (Term.app (Term.proj `sub_pos "." (fieldIdx "2")) [(Term.proj `ha "." (fieldIdx "2"))])])
           ","
           (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`y `hy `n] [])] "=>" (Term.hole "_")))]
          "⟩"))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`yr' []]
           [(Term.typeSpec ":" («term_<_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥") "<" `r'))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.«tactic·._»
                 "·"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ball_zero_eq)] "]")
                      [(Tactic.location "at" (Tactic.locationHyp [`hy] []))])
                     [])
                    (group (Tactic.exact "exact" `hy) [])])))
                [])]))))))
        [])
       (group
        (Tactic.have''
         "have"
         [`hr'0 []]
         [(Term.typeSpec
           ":"
           («term_<_»
            (numLit "0")
            "<"
            (Term.paren "(" [`r' [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")))])
        [])
       (group
        (Tactic.exact "exact" (Term.app (Term.proj (Term.app `norm_nonneg [(Term.hole "_")]) "." `trans_lt) [`yr']))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             (Init.Core.«term_∈_»
              `y
              " ∈ "
              (Term.app `Emetric.Ball [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `E)]] ")") `r])))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.refine'
                 "refine'"
                 (Term.app
                  (Term.proj `mem_emetric_ball_zero_iff "." (fieldIdx "2"))
                  [(Term.app `lt_transₓ [(Term.hole "_") `h])]))
                [])
               (group (Tactic.exactModCast "exact_mod_cast" `yr') [])]))))))
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `norm_sub_rev) "," (Tactic.rwRule ["←"] `mul_div_right_comm)] "]")
         [])
        [])
       (group
        (Tactic.have''
         "have"
         [`ya []]
         [(Term.typeSpec
           ":"
           («term_≤_»
            (Finset.Data.Finset.Fold.«term_*_»
             `a
             "*"
             («term_/_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥") "/" (Init.Coe.«term↑_» "↑" `r')))
            "≤"
            `a))])
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.app
          `mul_le_of_le_one_right
          [(Term.proj (Term.proj `ha "." (fieldIdx "1")) "." `le)
           (Term.app `div_le_one_of_le [`yr'.le `r'.coe_nonneg])]))
        [])
       (group
        (Tactic.tacticSuffices_
         "suffices"
         (Term.sufficesDecl
          []
          («term_≤_»
           (Analysis.Normed.Group.Basic.«term∥_∥»
            "∥"
            («term_-_» (Term.app `p.partial_sum [`n `y]) "-" (Term.app `f [(Init.Logic.«term_+_» `x "+" `y)]))
            "∥")
           "≤"
           («term_/_»
            (Finset.Data.Finset.Fold.«term_*_»
             `C
             "*"
             («term_^_»
              (Finset.Data.Finset.Fold.«term_*_»
               `a
               "*"
               («term_/_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥") "/" `r'))
              "^"
              `n))
            "/"
            («term_-_»
             (numLit "1")
             "-"
             (Finset.Data.Finset.Fold.«term_*_»
              `a
              "*"
              («term_/_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥") "/" `r')))))
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.refine' "refine'" (Term.app `this.trans [(Term.hole "_")])) [])
              (group
               (Tactic.«tactic_<;>_»
                (Tactic.applyRules
                 "apply_rules"
                 []
                 "["
                 [`div_le_div_of_le_left
                  ","
                  (Term.proj `sub_pos "." (fieldIdx "2"))
                  ","
                  `div_nonneg
                  ","
                  `mul_nonneg
                  ","
                  `pow_nonneg
                  ","
                  `hC.lt.le
                  ","
                  (Term.proj (Term.proj `ha "." (fieldIdx "1")) "." `le)
                  ","
                  `norm_nonneg
                  ","
                  `Nnreal.coe_nonneg
                  ","
                  (Term.proj `ha "." (fieldIdx "2"))
                  ","
                  (Term.proj (Term.app `sub_le_sub_iff_left [(Term.hole "_")]) "." (fieldIdx "2"))]
                 "]"
                 [])
                "<;>"
                (Tactic.tacticInfer_instance "infer_instance"))
               [])])))))
        [])
       (group
        (Tactic.apply
         "apply"
         (Term.app
          `norm_sub_le_of_geometric_bound_of_has_sum
          [(Term.app `ya.trans_lt [(Term.proj `ha "." (fieldIdx "2"))])
           (Term.hole "_")
           (Term.app `hf.has_sum [`this])]))
        [])
       (group (Tactic.intro "intro" [`n]) [])
       (group
        (tacticCalc_
         "calc"
         [(calcStep
           («term_≤_»
            (Analysis.Normed.Group.Basic.«term∥_∥»
             "∥"
             (Term.app
              (Term.app `p [`n])
              [(Term.fun
                "fun"
                (Term.basicFun [(Term.simpleBinder [`i] [(Term.typeSpec ":" (Term.app `Finₓ [`n]))])] "=>" `y))])
             "∥")
            "≤"
            (Finset.Data.Finset.Fold.«term_*_»
             (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p [`n]) "∥")
             "*"
             (Algebra.BigOperators.Basic.«term∏_,_»
              "∏"
              (Lean.explicitBinders
               (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (Term.app `Finₓ [`n])]))
              ", "
              (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥"))))
           ":="
           (Term.app `ContinuousMultilinearMap.le_op_norm [(Term.hole "_") (Term.hole "_")]))
          (calcStep
           («term_=_»
            (Term.hole "_")
            "="
            (Finset.Data.Finset.Fold.«term_*_»
             (Finset.Data.Finset.Fold.«term_*_»
              (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p [`n]) "∥")
              "*"
              («term_^_» `r' "^" `n))
             "*"
             («term_^_» («term_/_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥") "/" `r') "^" `n)))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.fieldSimp
                 "field_simp"
                 []
                 []
                 ["[" [(Tactic.simpLemma [] [] `hr'0.ne') "," (Tactic.simpLemma [] [] `mul_right_commₓ)] "]"]
                 []
                 [])
                [])]))))
          (calcStep
           («term_≤_»
            (Term.hole "_")
            "≤"
            (Finset.Data.Finset.Fold.«term_*_»
             (Finset.Data.Finset.Fold.«term_*_» `C "*" («term_^_» `a "^" `n))
             "*"
             («term_^_» («term_/_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥") "/" `r') "^" `n)))
           ":="
           (Term.app
            `mul_le_mul_of_nonneg_right
            [(Term.app `hp [`n])
             (Term.app
              `pow_nonneg
              [(Term.app `div_nonneg [(Term.app `norm_nonneg [(Term.hole "_")]) `r'.coe_nonneg]) (Term.hole "_")])]))
          (calcStep
           («term_≤_»
            (Term.hole "_")
            "≤"
            (Finset.Data.Finset.Fold.«term_*_»
             `C
             "*"
             («term_^_»
              (Finset.Data.Finset.Fold.«term_*_»
               `a
               "*"
               («term_/_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥") "/" `r'))
              "^"
              `n)))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_powₓ) "," (Tactic.rwRule [] `mul_assocₓ)] "]")
                 [])
                [])]))))])
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
       (Tactic.obtain
        "obtain"
        [(Tactic.rcasesPatMed
          [(Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ha)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `C)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hC)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hp)]) [])]
            "⟩")])]
        [":"
         (Mathlib.ExtendedBinder.«term∃___,_»
          "∃"
          `a
          («binderTerm∈_»
           "∈"
           (Term.app
            `Ioo
            [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")") (numLit "1")]))
          ","
          (Mathlib.ExtendedBinder.«term∃___,_»
           "∃"
           `C
           (Mathlib.ExtendedBinder.«binderTerm>_» ">" (numLit "0"))
           ","
           (Term.forall
            "∀"
            [(Term.simpleBinder [`n] [])]
            ","
            («term_≤_»
             (Finset.Data.Finset.Fold.«term_*_»
              (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p [`n]) "∥")
              "*"
              («term_^_» `r' "^" `n))
             "≤"
             (Finset.Data.Finset.Fold.«term_*_» `C "*" («term_^_» `a "^" `n))))))]
        [":=" [(Term.app `p.norm_mul_pow_le_mul_pow_of_lt_radius [(Term.app `h.trans_le [`hf.r_le])])]])
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.anonymousCtor
         "⟨"
         [`a
          ","
          `ha
          ","
          («term_/_» `C "/" («term_-_» (numLit "1") "-" `a))
          ","
          (Term.app
           `div_pos
           [`hC (Term.app (Term.proj `sub_pos "." (fieldIdx "2")) [(Term.proj `ha "." (fieldIdx "2"))])])
          ","
          (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`y `hy `n] [])] "=>" (Term.hole "_")))]
         "⟩"))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`yr' []]
          [(Term.typeSpec ":" («term_<_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥") "<" `r'))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ball_zero_eq)] "]")
                     [(Tactic.location "at" (Tactic.locationHyp [`hy] []))])
                    [])
                   (group (Tactic.exact "exact" `hy) [])])))
               [])]))))))
       [])
      (group
       (Tactic.have''
        "have"
        [`hr'0 []]
        [(Term.typeSpec
          ":"
          («term_<_»
           (numLit "0")
           "<"
           (Term.paren "(" [`r' [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")))])
       [])
      (group
       (Tactic.exact "exact" (Term.app (Term.proj (Term.app `norm_nonneg [(Term.hole "_")]) "." `trans_lt) [`yr']))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            (Init.Core.«term_∈_»
             `y
             " ∈ "
             (Term.app `Emetric.Ball [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `E)]] ")") `r])))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.refine'
                "refine'"
                (Term.app
                 (Term.proj `mem_emetric_ball_zero_iff "." (fieldIdx "2"))
                 [(Term.app `lt_transₓ [(Term.hole "_") `h])]))
               [])
              (group (Tactic.exactModCast "exact_mod_cast" `yr') [])]))))))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `norm_sub_rev) "," (Tactic.rwRule ["←"] `mul_div_right_comm)] "]")
        [])
       [])
      (group
       (Tactic.have''
        "have"
        [`ya []]
        [(Term.typeSpec
          ":"
          («term_≤_»
           (Finset.Data.Finset.Fold.«term_*_»
            `a
            "*"
            («term_/_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥") "/" (Init.Coe.«term↑_» "↑" `r')))
           "≤"
           `a))])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.app
         `mul_le_of_le_one_right
         [(Term.proj (Term.proj `ha "." (fieldIdx "1")) "." `le)
          (Term.app `div_le_one_of_le [`yr'.le `r'.coe_nonneg])]))
       [])
      (group
       (Tactic.tacticSuffices_
        "suffices"
        (Term.sufficesDecl
         []
         («term_≤_»
          (Analysis.Normed.Group.Basic.«term∥_∥»
           "∥"
           («term_-_» (Term.app `p.partial_sum [`n `y]) "-" (Term.app `f [(Init.Logic.«term_+_» `x "+" `y)]))
           "∥")
          "≤"
          («term_/_»
           (Finset.Data.Finset.Fold.«term_*_»
            `C
            "*"
            («term_^_»
             (Finset.Data.Finset.Fold.«term_*_»
              `a
              "*"
              («term_/_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥") "/" `r'))
             "^"
             `n))
           "/"
           («term_-_»
            (numLit "1")
            "-"
            (Finset.Data.Finset.Fold.«term_*_»
             `a
             "*"
             («term_/_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥") "/" `r')))))
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group (Tactic.refine' "refine'" (Term.app `this.trans [(Term.hole "_")])) [])
             (group
              (Tactic.«tactic_<;>_»
               (Tactic.applyRules
                "apply_rules"
                []
                "["
                [`div_le_div_of_le_left
                 ","
                 (Term.proj `sub_pos "." (fieldIdx "2"))
                 ","
                 `div_nonneg
                 ","
                 `mul_nonneg
                 ","
                 `pow_nonneg
                 ","
                 `hC.lt.le
                 ","
                 (Term.proj (Term.proj `ha "." (fieldIdx "1")) "." `le)
                 ","
                 `norm_nonneg
                 ","
                 `Nnreal.coe_nonneg
                 ","
                 (Term.proj `ha "." (fieldIdx "2"))
                 ","
                 (Term.proj (Term.app `sub_le_sub_iff_left [(Term.hole "_")]) "." (fieldIdx "2"))]
                "]"
                [])
               "<;>"
               (Tactic.tacticInfer_instance "infer_instance"))
              [])])))))
       [])
      (group
       (Tactic.apply
        "apply"
        (Term.app
         `norm_sub_le_of_geometric_bound_of_has_sum
         [(Term.app `ya.trans_lt [(Term.proj `ha "." (fieldIdx "2"))]) (Term.hole "_") (Term.app `hf.has_sum [`this])]))
       [])
      (group (Tactic.intro "intro" [`n]) [])
      (group
       (tacticCalc_
        "calc"
        [(calcStep
          («term_≤_»
           (Analysis.Normed.Group.Basic.«term∥_∥»
            "∥"
            (Term.app
             (Term.app `p [`n])
             [(Term.fun
               "fun"
               (Term.basicFun [(Term.simpleBinder [`i] [(Term.typeSpec ":" (Term.app `Finₓ [`n]))])] "=>" `y))])
            "∥")
           "≤"
           (Finset.Data.Finset.Fold.«term_*_»
            (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p [`n]) "∥")
            "*"
            (Algebra.BigOperators.Basic.«term∏_,_»
             "∏"
             (Lean.explicitBinders
              (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (Term.app `Finₓ [`n])]))
             ", "
             (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥"))))
          ":="
          (Term.app `ContinuousMultilinearMap.le_op_norm [(Term.hole "_") (Term.hole "_")]))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Finset.Data.Finset.Fold.«term_*_»
            (Finset.Data.Finset.Fold.«term_*_»
             (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p [`n]) "∥")
             "*"
             («term_^_» `r' "^" `n))
            "*"
            («term_^_» («term_/_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥") "/" `r') "^" `n)))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.fieldSimp
                "field_simp"
                []
                []
                ["[" [(Tactic.simpLemma [] [] `hr'0.ne') "," (Tactic.simpLemma [] [] `mul_right_commₓ)] "]"]
                []
                [])
               [])]))))
         (calcStep
          («term_≤_»
           (Term.hole "_")
           "≤"
           (Finset.Data.Finset.Fold.«term_*_»
            (Finset.Data.Finset.Fold.«term_*_» `C "*" («term_^_» `a "^" `n))
            "*"
            («term_^_» («term_/_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥") "/" `r') "^" `n)))
          ":="
          (Term.app
           `mul_le_mul_of_nonneg_right
           [(Term.app `hp [`n])
            (Term.app
             `pow_nonneg
             [(Term.app `div_nonneg [(Term.app `norm_nonneg [(Term.hole "_")]) `r'.coe_nonneg]) (Term.hole "_")])]))
         (calcStep
          («term_≤_»
           (Term.hole "_")
           "≤"
           (Finset.Data.Finset.Fold.«term_*_»
            `C
            "*"
            («term_^_»
             (Finset.Data.Finset.Fold.«term_*_»
              `a
              "*"
              («term_/_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥") "/" `r'))
             "^"
             `n)))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_powₓ) "," (Tactic.rwRule [] `mul_assocₓ)] "]")
                [])
               [])]))))])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
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
      (Analysis.Normed.Group.Basic.«term∥_∥»
       "∥"
       (Term.app
        (Term.app `p [`n])
        [(Term.fun
          "fun"
          (Term.basicFun [(Term.simpleBinder [`i] [(Term.typeSpec ":" (Term.app `Finₓ [`n]))])] "=>" `y))])
       "∥")
      "≤"
      (Finset.Data.Finset.Fold.«term_*_»
       (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p [`n]) "∥")
       "*"
       (Algebra.BigOperators.Basic.«term∏_,_»
        "∏"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (Term.app `Finₓ [`n])]))
        ", "
        (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥"))))
     ":="
     (Term.app `ContinuousMultilinearMap.le_op_norm [(Term.hole "_") (Term.hole "_")]))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Finset.Data.Finset.Fold.«term_*_»
       (Finset.Data.Finset.Fold.«term_*_»
        (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p [`n]) "∥")
        "*"
        («term_^_» `r' "^" `n))
       "*"
       («term_^_» («term_/_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥") "/" `r') "^" `n)))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.fieldSimp
           "field_simp"
           []
           []
           ["[" [(Tactic.simpLemma [] [] `hr'0.ne') "," (Tactic.simpLemma [] [] `mul_right_commₓ)] "]"]
           []
           [])
          [])]))))
    (calcStep
     («term_≤_»
      (Term.hole "_")
      "≤"
      (Finset.Data.Finset.Fold.«term_*_»
       (Finset.Data.Finset.Fold.«term_*_» `C "*" («term_^_» `a "^" `n))
       "*"
       («term_^_» («term_/_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥") "/" `r') "^" `n)))
     ":="
     (Term.app
      `mul_le_mul_of_nonneg_right
      [(Term.app `hp [`n])
       (Term.app
        `pow_nonneg
        [(Term.app `div_nonneg [(Term.app `norm_nonneg [(Term.hole "_")]) `r'.coe_nonneg]) (Term.hole "_")])]))
    (calcStep
     («term_≤_»
      (Term.hole "_")
      "≤"
      (Finset.Data.Finset.Fold.«term_*_»
       `C
       "*"
       («term_^_»
        (Finset.Data.Finset.Fold.«term_*_»
         `a
         "*"
         («term_/_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥") "/" `r'))
        "^"
        `n)))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_powₓ) "," (Tactic.rwRule [] `mul_assocₓ)] "]")
           [])
          [])]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticCalc_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_powₓ) "," (Tactic.rwRule [] `mul_assocₓ)] "]")
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_powₓ) "," (Tactic.rwRule [] `mul_assocₓ)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mul_assocₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mul_powₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (Term.hole "_")
   "≤"
   (Finset.Data.Finset.Fold.«term_*_»
    `C
    "*"
    («term_^_»
     (Finset.Data.Finset.Fold.«term_*_» `a "*" («term_/_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥") "/" `r'))
     "^"
     `n)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   `C
   "*"
   («term_^_»
    (Finset.Data.Finset.Fold.«term_*_» `a "*" («term_/_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥") "/" `r'))
    "^"
    `n))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_^_»
   (Finset.Data.Finset.Fold.«term_*_» `a "*" («term_/_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥") "/" `r'))
   "^"
   `n)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Finset.Data.Finset.Fold.«term_*_» `a "*" («term_/_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥") "/" `r'))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_/_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥") "/" `r')
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `r'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1022, (some 0, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_» `a "*" («term_/_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥") "/" `r')) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `C
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.app
   `mul_le_mul_of_nonneg_right
   [(Term.app `hp [`n])
    (Term.app
     `pow_nonneg
     [(Term.app `div_nonneg [(Term.app `norm_nonneg [(Term.hole "_")]) `r'.coe_nonneg]) (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `pow_nonneg
   [(Term.app `div_nonneg [(Term.app `norm_nonneg [(Term.hole "_")]) `r'.coe_nonneg]) (Term.hole "_")])
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
  (Term.app `div_nonneg [(Term.app `norm_nonneg [(Term.hole "_")]) `r'.coe_nonneg])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `r'.coe_nonneg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `norm_nonneg [(Term.hole "_")])
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
  `norm_nonneg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `norm_nonneg [(Term.hole "_")]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `div_nonneg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `div_nonneg [(Term.paren "(" [(Term.app `norm_nonneg [(Term.hole "_")]) []] ")") `r'.coe_nonneg]) []]
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
   [(Term.paren
     "("
     [(Term.app `div_nonneg [(Term.paren "(" [(Term.app `norm_nonneg [(Term.hole "_")]) []] ")") `r'.coe_nonneg]) []]
     ")")
    (Term.hole "_")])
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `hp [`n])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `hp [`n]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mul_le_mul_of_nonneg_right
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (Term.hole "_")
   "≤"
   (Finset.Data.Finset.Fold.«term_*_»
    (Finset.Data.Finset.Fold.«term_*_» `C "*" («term_^_» `a "^" `n))
    "*"
    («term_^_» («term_/_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥") "/" `r') "^" `n)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   (Finset.Data.Finset.Fold.«term_*_» `C "*" («term_^_» `a "^" `n))
   "*"
   («term_^_» («term_/_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥") "/" `r') "^" `n))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_^_» («term_/_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥") "/" `r') "^" `n)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  («term_/_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥") "/" `r')
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `r'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 70, (some 71, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term_/_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥") "/" `r') []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Finset.Data.Finset.Fold.«term_*_» `C "*" («term_^_» `a "^" `n))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_^_» `a "^" `n)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `C
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_» `C "*" («term_^_» `a "^" `n)) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.fieldSimp
        "field_simp"
        []
        []
        ["[" [(Tactic.simpLemma [] [] `hr'0.ne') "," (Tactic.simpLemma [] [] `mul_right_commₓ)] "]"]
        []
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.fieldSimp
   "field_simp"
   []
   []
   ["[" [(Tactic.simpLemma [] [] `hr'0.ne') "," (Tactic.simpLemma [] [] `mul_right_commₓ)] "]"]
   []
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.fieldSimp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mul_right_commₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hr'0.ne'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.hole "_")
   "="
   (Finset.Data.Finset.Fold.«term_*_»
    (Finset.Data.Finset.Fold.«term_*_»
     (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p [`n]) "∥")
     "*"
     («term_^_» `r' "^" `n))
    "*"
    («term_^_» («term_/_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥") "/" `r') "^" `n)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   (Finset.Data.Finset.Fold.«term_*_»
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p [`n]) "∥")
    "*"
    («term_^_» `r' "^" `n))
   "*"
   («term_^_» («term_/_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥") "/" `r') "^" `n))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_^_» («term_/_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥") "/" `r') "^" `n)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  («term_/_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥") "/" `r')
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `r'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 70, (some 71, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term_/_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥") "/" `r') []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Finset.Data.Finset.Fold.«term_*_»
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p [`n]) "∥")
   "*"
   («term_^_» `r' "^" `n))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_^_» `r' "^" `n)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `r'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p [`n]) "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `p [`n])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_»
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p [`n]) "∥")
   "*"
   («term_^_» `r' "^" `n))
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.app `ContinuousMultilinearMap.le_op_norm [(Term.hole "_") (Term.hole "_")])
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
  `ContinuousMultilinearMap.le_op_norm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (Analysis.Normed.Group.Basic.«term∥_∥»
    "∥"
    (Term.app
     (Term.app `p [`n])
     [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i] [(Term.typeSpec ":" (Term.app `Finₓ [`n]))])] "=>" `y))])
    "∥")
   "≤"
   (Finset.Data.Finset.Fold.«term_*_»
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p [`n]) "∥")
    "*"
    (Algebra.BigOperators.Basic.«term∏_,_»
     "∏"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (Term.app `Finₓ [`n])]))
     ", "
     (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p [`n]) "∥")
   "*"
   (Algebra.BigOperators.Basic.«term∏_,_»
    "∏"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (Term.app `Finₓ [`n])]))
    ", "
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∏_,_»
   "∏"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" (Term.app `Finₓ [`n])]))
   ", "
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∏_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `y "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
/--
    If a function admits a power series expansion, then it is exponentially close to the partial
    sums of this power series on strict subdisks of the disk of convergence.
    
    This version provides an upper estimate that decreases both in `∥y∥` and `n`. See also
    `has_fpower_series_on_ball.uniform_geometric_approx` for a weaker version. -/
  theorem
    HasFpowerSeriesOnBall.uniform_geometric_approx'
    { r' : ℝ≥0 } ( hf : HasFpowerSeriesOnBall f p x r ) ( h : ( r' : ℝ≥0∞ ) < r )
      :
        ∃
          a
          ∈ Ioo ( 0 : ℝ ) 1
          ,
          ∃
            C
            > 0
            ,
            ∀ , ∀ y ∈ Metric.Ball ( 0 : E ) r' , ∀ , ∀ n , ∥ f x + y - p.partial_sum n y ∥ ≤ C * a * ∥ y ∥ / r' ^ n
    :=
      by
        obtain
            ⟨ a , ha , C , hC , hp ⟩
            : ∃ a ∈ Ioo ( 0 : ℝ ) 1 , ∃ C > 0 , ∀ n , ∥ p n ∥ * r' ^ n ≤ C * a ^ n
            := p.norm_mul_pow_le_mul_pow_of_lt_radius h.trans_le hf.r_le
          refine' ⟨ a , ha , C / 1 - a , div_pos hC sub_pos . 2 ha . 2 , fun y hy n => _ ⟩
          have yr' : ∥ y ∥ < r' := by · rw [ ball_zero_eq ] at hy exact hy
          have hr'0 : 0 < ( r' : ℝ )
          exact norm_nonneg _ . trans_lt yr'
          have
            : y ∈ Emetric.Ball ( 0 : E ) r := by refine' mem_emetric_ball_zero_iff . 2 lt_transₓ _ h exact_mod_cast yr'
          rw [ norm_sub_rev , ← mul_div_right_comm ]
          have ya : a * ∥ y ∥ / ↑ r' ≤ a
          exact mul_le_of_le_one_right ha . 1 . le div_le_one_of_le yr'.le r'.coe_nonneg
          suffices
            ∥ p.partial_sum n y - f x + y ∥ ≤ C * a * ∥ y ∥ / r' ^ n / 1 - a * ∥ y ∥ / r'
              by
                refine' this.trans _
                  apply_rules
                      [
                      div_le_div_of_le_left
                        ,
                        sub_pos . 2
                        ,
                        div_nonneg
                        ,
                        mul_nonneg
                        ,
                        pow_nonneg
                        ,
                        hC.lt.le
                        ,
                        ha . 1 . le
                        ,
                        norm_nonneg
                        ,
                        Nnreal.coe_nonneg
                        ,
                        ha . 2
                        ,
                        sub_le_sub_iff_left _ . 2
                      ]
                    <;>
                    infer_instance
          apply norm_sub_le_of_geometric_bound_of_has_sum ya.trans_lt ha . 2 _ hf.has_sum this
          intro n
          calc
            ∥ p n fun i : Finₓ n => y ∥ ≤ ∥ p n ∥ * ∏ i : Finₓ n , ∥ y ∥ := ContinuousMultilinearMap.le_op_norm _ _
              _ = ∥ p n ∥ * r' ^ n * ∥ y ∥ / r' ^ n := by field_simp [ hr'0.ne' , mul_right_commₓ ]
              _ ≤ C * a ^ n * ∥ y ∥ / r' ^ n
                :=
                mul_le_mul_of_nonneg_right hp n pow_nonneg div_nonneg norm_nonneg _ r'.coe_nonneg _
              _ ≤ C * a * ∥ y ∥ / r' ^ n := by rw [ mul_powₓ , mul_assocₓ ]

/--  If a function admits a power series expansion, then it is exponentially close to the partial
sums of this power series on strict subdisks of the disk of convergence. -/
theorem HasFpowerSeriesOnBall.uniform_geometric_approx {r' : ℝ≥0 } (hf : HasFpowerSeriesOnBall f p x r)
    (h : (r' : ℝ≥0∞) < r) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C > 0, ∀, ∀ y ∈ Metric.Ball (0 : E) r', ∀, ∀ n, ∥f (x+y) - p.partial_sum n y∥ ≤ C*a ^ n := by
  obtain ⟨a, ha, C, hC, hp⟩ :
    ∃ a ∈ Ioo (0 : ℝ) 1,
      ∃ C > 0, ∀, ∀ y ∈ Metric.Ball (0 : E) r', ∀, ∀ n, ∥f (x+y) - p.partial_sum n y∥ ≤ C*(a*∥y∥ / r') ^ n
  exact hf.uniform_geometric_approx' h
  refine' ⟨a, ha, C, hC, fun y hy n => (hp y hy n).trans _⟩
  have yr' : ∥y∥ < r' := by
    rwa [ball_zero_eq] at hy
  refine' mul_le_mul_of_nonneg_left (pow_le_pow_of_le_left _ _ _) hC.lt.le
  exacts[mul_nonneg ha.1.le (div_nonneg (norm_nonneg y) r'.coe_nonneg),
    mul_le_of_le_one_right ha.1.le (div_le_one_of_le yr'.le r'.coe_nonneg)]

/--  Taylor formula for an analytic function, `is_O` version. -/
theorem HasFpowerSeriesAt.is_O_sub_partial_sum_pow (hf : HasFpowerSeriesAt f p x) (n : ℕ) :
    is_O (fun y : E => f (x+y) - p.partial_sum n y) (fun y => ∥y∥ ^ n) (𝓝 0) := by
  rcases hf with ⟨r, hf⟩
  rcases Ennreal.lt_iff_exists_nnreal_btwn.1 hf.r_pos with ⟨r', r'0, h⟩
  obtain ⟨a, ha, C, hC, hp⟩ :
    ∃ a ∈ Ioo (0 : ℝ) 1,
      ∃ C > 0, ∀, ∀ y ∈ Metric.Ball (0 : E) r', ∀, ∀ n, ∥f (x+y) - p.partial_sum n y∥ ≤ C*(a*∥y∥ / r') ^ n
  exact hf.uniform_geometric_approx' h
  refine' is_O_iff.2 ⟨C*(a / r') ^ n, _⟩
  replace r'0 : 0 < (r' : ℝ)
  ·
    exact_mod_cast r'0
  filter_upwards [Metric.ball_mem_nhds (0 : E) r'0]
  intro y hy
  simpa [mul_powₓ, mul_div_assoc, mul_assocₓ, div_mul_eq_mul_div] using hp y hy n

attribute [-instance] Unique.subsingleton Pi.subsingleton

/--  If `f` has formal power series `∑ n, pₙ` on a ball of radius `r`, then for `y, z` in any smaller
ball, the norm of the difference `f y - f z - p 1 (λ _, y - z)` is bounded above by
`C * (max ∥y - x∥ ∥z - x∥) * ∥y - z∥`. This lemma formulates this property using `is_O` and
`filter.principal` on `E × E`. -/
theorem HasFpowerSeriesOnBall.is_O_image_sub_image_sub_deriv_principal (hf : HasFpowerSeriesOnBall f p x r)
    (hr : r' < r) :
    is_O (fun y : E × E => f y.1 - f y.2 - p 1 fun _ => y.1 - y.2) (fun y => ∥y - (x, x)∥*∥y.1 - y.2∥)
      (𝓟 $ Emetric.Ball (x, x) r') :=
  by
  lift r' to ℝ≥0 using ne_top_of_lt hr
  rcases(zero_le r').eq_or_lt with (rfl | hr'0)
  ·
    simp only [is_O_bot, Emetric.ball_zero, principal_empty, Ennreal.coe_zero]
  obtain ⟨a, ha, C, hC : 0 < C, hp⟩ : ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C > 0, ∀ n : ℕ, (∥p n∥*↑r' ^ n) ≤ C*a ^ n
  exact p.norm_mul_pow_le_mul_pow_of_lt_radius (hr.trans_le hf.r_le)
  simp only [← le_div_iff (pow_pos (Nnreal.coe_pos.2 hr'0) _)] at hp
  set L : E × E → ℝ := fun y => ((C*(a / r') ^ 2)*∥y - (x, x)∥*∥y.1 - y.2∥)*(a / (1 - a) ^ 2)+2 / (1 - a)
  have hL : ∀, ∀ y ∈ Emetric.Ball (x, x) r', ∀, ∥f y.1 - f y.2 - p 1 fun _ => y.1 - y.2∥ ≤ L y := by
    intro y hy'
    have hy : y ∈ (Emetric.Ball x r).Prod (Emetric.Ball x r) := by
      rw [Emetric.ball_prod_same]
      exact Emetric.ball_subset_ball hr.le hy'
    set A : ℕ → F := fun n => (p n fun _ => y.1 - x) - p n fun _ => y.2 - x
    have hA : HasSum (fun n => A (n+2)) (f y.1 - f y.2 - p 1 fun _ => y.1 - y.2) := by
      convert (has_sum_nat_add_iff' 2).2 ((hf.has_sum_sub hy.1).sub (hf.has_sum_sub hy.2)) using 1
      rw [Finset.sum_range_succ, Finset.sum_range_one, hf.coeff_zero, hf.coeff_zero, sub_self, zero_addₓ, ←
        Subsingleton.pi_single_eq (0 : Finₓ 1) (y.1 - x), Pi.single, ← Subsingleton.pi_single_eq (0 : Finₓ 1) (y.2 - x),
        Pi.single, ← (p 1).map_sub, ← Pi.single, Subsingleton.pi_single_eq, sub_sub_sub_cancel_right]
    rw [Emetric.mem_ball, edist_eq_coe_nnnorm_sub, Ennreal.coe_lt_coe] at hy'
    set B : ℕ → ℝ := fun n => ((C*(a / r') ^ 2)*∥y - (x, x)∥*∥y.1 - y.2∥)*(n+2)*a ^ n
    have hAB : ∀ n, ∥A (n+2)∥ ≤ B n := fun n =>
      calc ∥A (n+2)∥ ≤ ((∥p (n+2)∥*↑n+2)*∥y - (x, x)∥ ^ n+1)*∥y.1 - y.2∥ := by
        simpa only [Fintype.card_fin, pi_norm_const, Prod.norm_def, Pi.sub_def, Prod.fst_sub, Prod.snd_sub,
          sub_sub_sub_cancel_right] using (p $ n+2).norm_image_sub_le (fun _ => y.1 - x) fun _ => y.2 - x
        _ = (∥p (n+2)∥*∥y - (x, x)∥ ^ n)*((↑n+2)*∥y - (x, x)∥)*∥y.1 - y.2∥ := by
        rw [pow_succₓ ∥y - (x, x)∥]
        ac_rfl
        _ ≤ (((C*a ^ n+2) / r' ^ n+2)*r' ^ n)*((↑n+2)*∥y - (x, x)∥)*∥y.1 - y.2∥ := by
        apply_rules [mul_le_mul_of_nonneg_right, mul_le_mul, hp, pow_le_pow_of_le_left, hy'.le, norm_nonneg, pow_nonneg,
          div_nonneg, mul_nonneg, Nat.cast_nonneg, hC.le, r'.coe_nonneg, ha.1.le]
        _ = B n := by
        field_simp [B, pow_succₓ, hr'0.ne']
        simp only [mul_assocₓ, mul_commₓ, mul_left_commₓ]
        
    have hBL : HasSum B (L y) := by
      apply HasSum.mul_left
      simp only [add_mulₓ]
      have : ∥a∥ < 1 := by
        simp only [Real.norm_eq_abs, abs_of_pos ha.1, ha.2]
      convert (has_sum_coe_mul_geometric_of_norm_lt_1 this).add ((has_sum_geometric_of_norm_lt_1 this).mul_left 2)
    exact hA.norm_le_of_bounded hBL hAB
  suffices is_O L (fun y => ∥y - (x, x)∥*∥y.1 - y.2∥) (𝓟 (Emetric.Ball (x, x) r'))by
    refine' (is_O.of_bound 1 (eventually_principal.2 $ fun y hy => _)).trans this
    rw [one_mulₓ]
    exact (hL y hy).trans (le_abs_self _)
  simp_rw [L, mul_right_commₓ _ (_*_)]
  exact (is_O_refl _ _).const_mul_left _

-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (y z «expr ∈ » emetric.ball x r')
/--  If `f` has formal power series `∑ n, pₙ` on a ball of radius `r`, then for `y, z` in any smaller
ball, the norm of the difference `f y - f z - p 1 (λ _, y - z)` is bounded above by
`C * (max ∥y - x∥ ∥z - x∥) * ∥y - z∥`. -/
theorem HasFpowerSeriesOnBall.image_sub_sub_deriv_le (hf : HasFpowerSeriesOnBall f p x r) (hr : r' < r) :
    ∃ C,
      ∀ y z _ : y ∈ Emetric.Ball x r' _ : z ∈ Emetric.Ball x r',
        ∥f y - f z - p 1 fun _ => y - z∥ ≤ (C*max ∥y - x∥ ∥z - x∥)*∥y - z∥ :=
  by
  simpa only [is_O_principal, mul_assocₓ, NormedField.norm_mul, norm_norm, Prod.forall, Emetric.mem_ball, Prod.edist_eq,
    max_lt_iff, and_imp] using hf.is_O_image_sub_image_sub_deriv_principal hr

/--  If `f` has formal power series `∑ n, pₙ` at `x`, then
`f y - f z - p 1 (λ _, y - z) = O(∥(y, z) - (x, x)∥ * ∥y - z∥)` as `(y, z) → (x, x)`.
In particular, `f` is strictly differentiable at `x`. -/
theorem HasFpowerSeriesAt.is_O_image_sub_norm_mul_norm_sub (hf : HasFpowerSeriesAt f p x) :
    is_O (fun y : E × E => f y.1 - f y.2 - p 1 fun _ => y.1 - y.2) (fun y => ∥y - (x, x)∥*∥y.1 - y.2∥) (𝓝 (x, x)) := by
  rcases hf with ⟨r, hf⟩
  rcases Ennreal.lt_iff_exists_nnreal_btwn.1 hf.r_pos with ⟨r', r'0, h⟩
  refine' (hf.is_O_image_sub_image_sub_deriv_principal h).mono _
  exact le_principal_iff.2 (Emetric.ball_mem_nhds _ r'0)

/--  If a function admits a power series expansion at `x`, then it is the uniform limit of the
partial sums of this power series on strict subdisks of the disk of convergence, i.e., `f (x + y)`
is the uniform limit of `p.partial_sum n y` there. -/
theorem HasFpowerSeriesOnBall.tendsto_uniformly_on {r' : ℝ≥0 } (hf : HasFpowerSeriesOnBall f p x r)
    (h : (r' : ℝ≥0∞) < r) :
    TendstoUniformlyOn (fun n y => p.partial_sum n y) (fun y => f (x+y)) at_top (Metric.Ball (0 : E) r') := by
  obtain ⟨a, ha, C, hC, hp⟩ :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C > 0, ∀, ∀ y ∈ Metric.Ball (0 : E) r', ∀, ∀ n, ∥f (x+y) - p.partial_sum n y∥ ≤ C*a ^ n
  exact hf.uniform_geometric_approx h
  refine' Metric.tendsto_uniformly_on_iff.2 fun ε εpos => _
  have L : tendsto (fun n => (C : ℝ)*a ^ n) at_top (𝓝 ((C : ℝ)*0)) :=
    tendsto_const_nhds.mul (tendsto_pow_at_top_nhds_0_of_lt_1 ha.1.le ha.2)
  rw [mul_zero] at L
  refine' (L.eventually (gt_mem_nhds εpos)).mono fun n hn y hy => _
  rw [dist_eq_norm]
  exact (hp y hy n).trans_lt hn

/--  If a function admits a power series expansion at `x`, then it is the locally uniform limit of
the partial sums of this power series on the disk of convergence, i.e., `f (x + y)`
is the locally uniform limit of `p.partial_sum n y` there. -/
theorem HasFpowerSeriesOnBall.tendsto_locally_uniformly_on (hf : HasFpowerSeriesOnBall f p x r) :
    TendstoLocallyUniformlyOn (fun n y => p.partial_sum n y) (fun y => f (x+y)) at_top (Emetric.Ball (0 : E) r) := by
  intro u hu x hx
  rcases Ennreal.lt_iff_exists_nnreal_btwn.1 hx with ⟨r', xr', hr'⟩
  have : Emetric.Ball (0 : E) r' ∈ 𝓝 x := IsOpen.mem_nhds Emetric.is_open_ball xr'
  refine' ⟨Emetric.Ball (0 : E) r', mem_nhds_within_of_mem_nhds this, _⟩
  simpa [Metric.emetric_ball_nnreal] using hf.tendsto_uniformly_on hr' u hu

/--  If a function admits a power series expansion at `x`, then it is the uniform limit of the
partial sums of this power series on strict subdisks of the disk of convergence, i.e., `f y`
is the uniform limit of `p.partial_sum n (y - x)` there. -/
theorem HasFpowerSeriesOnBall.tendsto_uniformly_on' {r' : ℝ≥0 } (hf : HasFpowerSeriesOnBall f p x r)
    (h : (r' : ℝ≥0∞) < r) : TendstoUniformlyOn (fun n y => p.partial_sum n (y - x)) f at_top (Metric.Ball (x : E) r') :=
  by
  convert (hf.tendsto_uniformly_on h).comp fun y => y - x
  ·
    simp [· ∘ ·]
  ·
    ext z
    simp [dist_eq_norm]

/--  If a function admits a power series expansion at `x`, then it is the locally uniform limit of
the  partial sums of this power series on the disk of convergence, i.e., `f y`
is the locally uniform limit of `p.partial_sum n (y - x)` there. -/
theorem HasFpowerSeriesOnBall.tendsto_locally_uniformly_on' (hf : HasFpowerSeriesOnBall f p x r) :
    TendstoLocallyUniformlyOn (fun n y => p.partial_sum n (y - x)) f at_top (Emetric.Ball (x : E) r) := by
  have A : ContinuousOn (fun y : E => y - x) (Emetric.Ball (x : E) r) :=
    (continuous_id.sub continuous_const).ContinuousOn
  convert hf.tendsto_locally_uniformly_on.comp (fun y : E => y - x) _ A
  ·
    ext z
    simp
  ·
    intro z
    simp [edist_eq_coe_nnnorm, edist_eq_coe_nnnorm_sub]

/--  If a function admits a power series expansion on a disk, then it is continuous there. -/
protected theorem HasFpowerSeriesOnBall.continuous_on (hf : HasFpowerSeriesOnBall f p x r) :
    ContinuousOn f (Emetric.Ball x r) :=
  hf.tendsto_locally_uniformly_on'.continuous_on $
    eventually_of_forall $ fun n =>
      ((p.partial_sum_continuous n).comp (continuous_id.sub continuous_const)).ContinuousOn

protected theorem HasFpowerSeriesAt.continuous_at (hf : HasFpowerSeriesAt f p x) : ContinuousAt f x :=
  let ⟨r, hr⟩ := hf
  hr.continuous_on.continuous_at (Emetric.ball_mem_nhds x hr.r_pos)

protected theorem AnalyticAt.continuous_at (hf : AnalyticAt 𝕜 f x) : ContinuousAt f x :=
  let ⟨p, hp⟩ := hf
  hp.continuous_at

/--  In a complete space, the sum of a converging power series `p` admits `p` as a power series.
This is not totally obvious as we need to check the convergence of the series. -/
protected theorem FormalMultilinearSeries.has_fpower_series_on_ball [CompleteSpace F]
    (p : FormalMultilinearSeries 𝕜 E F) (h : 0 < p.radius) : HasFpowerSeriesOnBall p.sum p 0 p.radius :=
  { r_le := le_reflₓ _, r_pos := h,
    HasSum := fun y hy => by
      rw [zero_addₓ]
      exact p.has_sum hy }

theorem HasFpowerSeriesOnBall.sum [CompleteSpace F] (h : HasFpowerSeriesOnBall f p x r) {y : E}
    (hy : y ∈ Emetric.Ball (0 : E) r) : f (x+y) = p.sum y :=
  (h.has_sum hy).unique (p.has_sum (lt_of_lt_of_leₓ hy h.r_le))

/--  The sum of a converging power series is continuous in its disk of convergence. -/
protected theorem FormalMultilinearSeries.continuous_on [CompleteSpace F] :
    ContinuousOn p.sum (Emetric.Ball 0 p.radius) := by
  cases' (zero_le p.radius).eq_or_lt with h h
  ·
    simp [← h, continuous_on_empty]
  ·
    exact (p.has_fpower_series_on_ball h).ContinuousOn

end

/-!
### Changing origin in a power series

If a function is analytic in a disk `D(x, R)`, then it is analytic in any disk contained in that
one. Indeed, one can write
$$
f (x + y + z) = \sum_{n} p_n (y + z)^n = \sum_{n, k} \binom{n}{k} p_n y^{n-k} z^k
= \sum_{k} \Bigl(\sum_{n} \binom{n}{k} p_n y^{n-k}\Bigr) z^k.
$$
The corresponding power series has thus a `k`-th coefficient equal to
$\sum_{n} \binom{n}{k} p_n y^{n-k}$. In the general case where `pₙ` is a multilinear map, this has
to be interpreted suitably: instead of having a binomial coefficient, one should sum over all
possible subsets `s` of `fin n` of cardinal `k`, and attribute `z` to the indices in `s` and
`y` to the indices outside of `s`.

In this paragraph, we implement this. The new power series is called `p.change_origin y`. Then, we
check its convergence and the fact that its sum coincides with the original sum. The outcome of this
discussion is that the set of points where a function is analytic is open.
-/


namespace FormalMultilinearSeries

section

variable (p : FormalMultilinearSeries 𝕜 E F) {x y : E} {r R : ℝ≥0 }

/--  A term of `formal_multilinear_series.change_origin_series`.

Given a formal multilinear series `p` and a point `x` in its ball of convergence,
`p.change_origin x` is a formal multilinear series such that
`p.sum (x+y) = (p.change_origin x).sum y` when this makes sense. Each term of `p.change_origin x`
is itself an analytic function of `x` given by the series `p.change_origin_series`. Each term in
`change_origin_series` is the sum of `change_origin_series_term`'s over all `s` of cardinality `l`.
-/
def change_origin_series_term (k l : ℕ) (s : Finset (Finₓ (k+l))) (hs : s.card = l) : E[×l]→L[𝕜] E[×k]→L[𝕜] F :=
  ContinuousMultilinearMap.curryFinFinset 𝕜 E F hs
    (by
      erw [Finset.card_compl, Fintype.card_fin, hs, add_tsub_cancel_right])
    (p $ k+l)

theorem change_origin_series_term_apply (k l : ℕ) (s : Finset (Finₓ (k+l))) (hs : s.card = l) (x y : E) :
    (p.change_origin_series_term k l s hs (fun _ => x) fun _ => y) = p (k+l) (s.piecewise (fun _ => x) fun _ => y) :=
  ContinuousMultilinearMap.curry_fin_finset_apply_const _ _ _ _ _

@[simp]
theorem norm_change_origin_series_term (k l : ℕ) (s : Finset (Finₓ (k+l))) (hs : s.card = l) :
    ∥p.change_origin_series_term k l s hs∥ = ∥p (k+l)∥ := by
  simp only [change_origin_series_term, LinearIsometryEquiv.norm_map]

@[simp]
theorem nnnorm_change_origin_series_term (k l : ℕ) (s : Finset (Finₓ (k+l))) (hs : s.card = l) :
    ∥p.change_origin_series_term k l s hs∥₊ = ∥p (k+l)∥₊ := by
  simp only [change_origin_series_term, LinearIsometryEquiv.nnnorm_map]

theorem nnnorm_change_origin_series_term_apply_le (k l : ℕ) (s : Finset (Finₓ (k+l))) (hs : s.card = l) (x y : E) :
    ∥p.change_origin_series_term k l s hs (fun _ => x) fun _ => y∥₊ ≤ (∥p (k+l)∥₊*∥x∥₊ ^ l)*∥y∥₊ ^ k := by
  rw [← p.nnnorm_change_origin_series_term k l s hs, ← Finₓ.prod_const, ← Finₓ.prod_const]
  apply ContinuousMultilinearMap.le_of_op_nnnorm_le
  apply ContinuousMultilinearMap.le_op_nnnorm

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " The power series for `f.change_origin k`.\n\nGiven a formal multilinear series `p` and a point `x` in its ball of convergence,\n`p.change_origin x` is a formal multilinear series such that\n`p.sum (x+y) = (p.change_origin x).sum y` when this makes sense. -/")]
  []
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `change_origin_series [])
  (Command.optDeclSig
   [(Term.explicitBinder "(" [`k] [":" (termℕ "ℕ")] [] ")")]
   [(Term.typeSpec
     ":"
     (Term.app
      `FormalMultilinearSeries
      [`𝕜 `E (Topology.Algebra.Multilinear.«term_[×_]→L[_]_» `E "[×" `k "]→L[" `𝕜 "] " `F)]))])
  (Command.declValSimple
   ":="
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`l] [])]
     "=>"
     (Algebra.BigOperators.Basic.«term∑_,_»
      "∑"
      (Lean.explicitBinders
       (Lean.unbracketedExplicitBinders
        [(Lean.binderIdent `s)]
        [":"
         («term{__:_//_}»
          "{"
          `s
          [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
          "//"
          («term_=_» (Term.app `Finset.card [`s]) "=" `l)
          "}")]))
      ", "
      (Term.app `p.change_origin_series_term [`k `l `s (Term.proj `s "." (fieldIdx "2"))]))))
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
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`l] [])]
    "=>"
    (Algebra.BigOperators.Basic.«term∑_,_»
     "∑"
     (Lean.explicitBinders
      (Lean.unbracketedExplicitBinders
       [(Lean.binderIdent `s)]
       [":"
        («term{__:_//_}»
         "{"
         `s
         [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
         "//"
         («term_=_» (Term.app `Finset.card [`s]) "=" `l)
         "}")]))
     ", "
     (Term.app `p.change_origin_series_term [`k `l `s (Term.proj `s "." (fieldIdx "2"))]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_,_»
   "∑"
   (Lean.explicitBinders
    (Lean.unbracketedExplicitBinders
     [(Lean.binderIdent `s)]
     [":"
      («term{__:_//_}»
       "{"
       `s
       [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
       "//"
       («term_=_» (Term.app `Finset.card [`s]) "=" `l)
       "}")]))
   ", "
   (Term.app `p.change_origin_series_term [`k `l `s (Term.proj `s "." (fieldIdx "2"))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `p.change_origin_series_term [`k `l `s (Term.proj `s "." (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `s "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `l
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p.change_origin_series_term
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
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
    The power series for `f.change_origin k`.
    
    Given a formal multilinear series `p` and a point `x` in its ball of convergence,
    `p.change_origin x` is a formal multilinear series such that
    `p.sum (x+y) = (p.change_origin x).sum y` when this makes sense. -/
  def
    change_origin_series
    ( k : ℕ ) : FormalMultilinearSeries 𝕜 E E [× k ]→L[ 𝕜 ] F
    := fun l => ∑ s : { s : Finset Finₓ k + l // Finset.card s = l } , p.change_origin_series_term k l s s . 2

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `nnnorm_change_origin_series_le_tsum [])
  (Command.declSig
   [(Term.explicitBinder "(" [`k `l] [":" (termℕ "ℕ")] [] ")")]
   (Term.typeSpec
    ":"
    («term_≤_»
     (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" (Term.app `p.change_origin_series [`k `l]) "∥₊")
     "≤"
     (Topology.Algebra.InfiniteSum.«term∑'_,_»
      "∑'"
      (Lean.explicitBinders
       (Lean.unbracketedExplicitBinders
        [(Lean.binderIdent `x)]
        [":"
         («term{__:_//_}»
          "{"
          `s
          [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
          "//"
          («term_=_» `s.card "=" `l)
          "}")]))
      ", "
      (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" (Term.app `p [(Init.Logic.«term_+_» `k "+" `l)]) "∥₊")))))
  (Command.declValSimple
   ":="
   («term_$__»
    (Term.proj (Term.app `nnnorm_sum_le [(Term.hole "_") (Term.hole "_")]) "." `trans_eq)
    "$"
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
           [(Tactic.simpLemma [] [] `tsum_fintype) "," (Tactic.simpLemma [] [] `nnnorm_change_origin_series_term)]
           "]"]
          [])
         [])]))))
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
  («term_$__»
   (Term.proj (Term.app `nnnorm_sum_le [(Term.hole "_") (Term.hole "_")]) "." `trans_eq)
   "$"
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
          [(Tactic.simpLemma [] [] `tsum_fintype) "," (Tactic.simpLemma [] [] `nnnorm_change_origin_series_term)]
          "]"]
         [])
        [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
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
         [(Tactic.simpLemma [] [] `tsum_fintype) "," (Tactic.simpLemma [] [] `nnnorm_change_origin_series_term)]
         "]"]
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["[" [(Tactic.simpLemma [] [] `tsum_fintype) "," (Tactic.simpLemma [] [] `nnnorm_change_origin_series_term)] "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `nnnorm_change_origin_series_term
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `tsum_fintype
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  (Term.proj (Term.app `nnnorm_sum_le [(Term.hole "_") (Term.hole "_")]) "." `trans_eq)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `nnnorm_sum_le [(Term.hole "_") (Term.hole "_")])
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
  `nnnorm_sum_le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `nnnorm_sum_le [(Term.hole "_") (Term.hole "_")]) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_≤_»
   (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" (Term.app `p.change_origin_series [`k `l]) "∥₊")
   "≤"
   (Topology.Algebra.InfiniteSum.«term∑'_,_»
    "∑'"
    (Lean.explicitBinders
     (Lean.unbracketedExplicitBinders
      [(Lean.binderIdent `x)]
      [":"
       («term{__:_//_}»
        "{"
        `s
        [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
        "//"
        («term_=_» `s.card "=" `l)
        "}")]))
    ", "
    (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" (Term.app `p [(Init.Logic.«term_+_» `k "+" `l)]) "∥₊")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Topology.Algebra.InfiniteSum.«term∑'_,_»
   "∑'"
   (Lean.explicitBinders
    (Lean.unbracketedExplicitBinders
     [(Lean.binderIdent `x)]
     [":"
      («term{__:_//_}»
       "{"
       `s
       [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
       "//"
       («term_=_» `s.card "=" `l)
       "}")]))
   ", "
   (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" (Term.app `p [(Init.Logic.«term_+_» `k "+" `l)]) "∥₊"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Algebra.InfiniteSum.«term∑'_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" (Term.app `p [(Init.Logic.«term_+_» `k "+" `l)]) "∥₊")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥₊»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `p [(Init.Logic.«term_+_» `k "+" `l)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `k "+" `l)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `l
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `k "+" `l) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
  nnnorm_change_origin_series_le_tsum
  ( k l : ℕ ) : ∥ p.change_origin_series k l ∥₊ ≤ ∑' x : { s : Finset Finₓ k + l // s.card = l } , ∥ p k + l ∥₊
  := nnnorm_sum_le _ _ . trans_eq $ by simp only [ tsum_fintype , nnnorm_change_origin_series_term ]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `nnnorm_change_origin_series_apply_le_tsum [])
  (Command.declSig
   [(Term.explicitBinder "(" [`k `l] [":" (termℕ "ℕ")] [] ")") (Term.explicitBinder "(" [`x] [":" `E] [] ")")]
   (Term.typeSpec
    ":"
    («term_≤_»
     (Analysis.Normed.Group.Basic.«term∥_∥₊»
      "∥"
      (Term.app
       `p.change_origin_series
       [`k `l (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `x))])
      "∥₊")
     "≤"
     (Topology.Algebra.InfiniteSum.«term∑'_,_»
      "∑'"
      (Lean.explicitBinders
       (Lean.unbracketedExplicitBinders
        [(Lean.binderIdent `s)]
        [":"
         («term{__:_//_}»
          "{"
          `s
          [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
          "//"
          («term_=_» `s.card "=" `l)
          "}")]))
      ", "
      (Finset.Data.Finset.Fold.«term_*_»
       (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" (Term.app `p [(Init.Logic.«term_+_» `k "+" `l)]) "∥₊")
       "*"
       («term_^_» (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" `x "∥₊") "^" `l))))))
  (Command.declValSimple
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
          [(Tactic.rwRule [] `Nnreal.tsum_mul_right) "," (Tactic.rwRule ["←"] `Finₓ.prod_const)]
          "]")
         [])
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.app
          (Term.proj (Term.app `p.change_origin_series [`k `l]) "." `le_of_op_nnnorm_le)
          [(Term.hole "_") (Term.app `p.nnnorm_change_origin_series_le_tsum [(Term.hole "_") (Term.hole "_")])]))
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
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `Nnreal.tsum_mul_right) "," (Tactic.rwRule ["←"] `Finₓ.prod_const)]
         "]")
        [])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.app
         (Term.proj (Term.app `p.change_origin_series [`k `l]) "." `le_of_op_nnnorm_le)
         [(Term.hole "_") (Term.app `p.nnnorm_change_origin_series_le_tsum [(Term.hole "_") (Term.hole "_")])]))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.app
    (Term.proj (Term.app `p.change_origin_series [`k `l]) "." `le_of_op_nnnorm_le)
    [(Term.hole "_") (Term.app `p.nnnorm_change_origin_series_le_tsum [(Term.hole "_") (Term.hole "_")])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj (Term.app `p.change_origin_series [`k `l]) "." `le_of_op_nnnorm_le)
   [(Term.hole "_") (Term.app `p.nnnorm_change_origin_series_le_tsum [(Term.hole "_") (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `p.nnnorm_change_origin_series_le_tsum [(Term.hole "_") (Term.hole "_")])
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
  `p.nnnorm_change_origin_series_le_tsum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `p.nnnorm_change_origin_series_le_tsum [(Term.hole "_") (Term.hole "_")]) []]
 ")")
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
  (Term.proj (Term.app `p.change_origin_series [`k `l]) "." `le_of_op_nnnorm_le)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `p.change_origin_series [`k `l])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `l
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p.change_origin_series
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `p.change_origin_series [`k `l]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Nnreal.tsum_mul_right) "," (Tactic.rwRule ["←"] `Finₓ.prod_const)] "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finₓ.prod_const
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Nnreal.tsum_mul_right
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_≤_»
   (Analysis.Normed.Group.Basic.«term∥_∥₊»
    "∥"
    (Term.app
     `p.change_origin_series
     [`k `l (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `x))])
    "∥₊")
   "≤"
   (Topology.Algebra.InfiniteSum.«term∑'_,_»
    "∑'"
    (Lean.explicitBinders
     (Lean.unbracketedExplicitBinders
      [(Lean.binderIdent `s)]
      [":"
       («term{__:_//_}»
        "{"
        `s
        [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
        "//"
        («term_=_» `s.card "=" `l)
        "}")]))
    ", "
    (Finset.Data.Finset.Fold.«term_*_»
     (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" (Term.app `p [(Init.Logic.«term_+_» `k "+" `l)]) "∥₊")
     "*"
     («term_^_» (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" `x "∥₊") "^" `l))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Topology.Algebra.InfiniteSum.«term∑'_,_»
   "∑'"
   (Lean.explicitBinders
    (Lean.unbracketedExplicitBinders
     [(Lean.binderIdent `s)]
     [":"
      («term{__:_//_}»
       "{"
       `s
       [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
       "//"
       («term_=_» `s.card "=" `l)
       "}")]))
   ", "
   (Finset.Data.Finset.Fold.«term_*_»
    (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" (Term.app `p [(Init.Logic.«term_+_» `k "+" `l)]) "∥₊")
    "*"
    («term_^_» (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" `x "∥₊") "^" `l)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Algebra.InfiniteSum.«term∑'_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" (Term.app `p [(Init.Logic.«term_+_» `k "+" `l)]) "∥₊")
   "*"
   («term_^_» (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" `x "∥₊") "^" `l))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_^_» (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" `x "∥₊") "^" `l)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `l
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" `x "∥₊")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥₊»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" (Term.app `p [(Init.Logic.«term_+_» `k "+" `l)]) "∥₊")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥₊»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `p [(Init.Logic.«term_+_» `k "+" `l)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `k "+" `l)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `l
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `k "+" `l) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
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
theorem
  nnnorm_change_origin_series_apply_le_tsum
  ( k l : ℕ ) ( x : E )
    :
      ∥ p.change_origin_series k l fun _ => x ∥₊
        ≤
        ∑' s : { s : Finset Finₓ k + l // s.card = l } , ∥ p k + l ∥₊ * ∥ x ∥₊ ^ l
  :=
    by
      rw [ Nnreal.tsum_mul_right , ← Finₓ.prod_const ]
        exact p.change_origin_series k l . le_of_op_nnnorm_le _ p.nnnorm_change_origin_series_le_tsum _ _

/-- 
Changing the origin of a formal multilinear series `p`, so that
`p.sum (x+y) = (p.change_origin x).sum y` when this makes sense.
-/
def change_origin (x : E) : FormalMultilinearSeries 𝕜 E F := fun k => (p.change_origin_series k).Sum x

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " An auxiliary equivalence useful in the proofs about\n`formal_multilinear_series.change_origin_series`: the set of triples `(k, l, s)`, where `s` is a\n`finset (fin (k + l))` of cardinality `l` is equivalent to the set of pairs `(n, s)`, where `s` is a\n`finset (fin n)`.\n\nThe forward map sends `(k, l, s)` to `(k + l, s)` and the inverse map sends `(n, s)` to\n`(n - finset.card s, finset.card s, s)`. The actual definition is less readable because of problems\nwith non-definitional equalities. -/")]
  [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simps "simps" [] []))] "]")]
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `change_origin_index_equiv [])
  (Command.optDeclSig
   []
   [(Term.typeSpec
     ":"
     (Data.Equiv.Basic.«term_≃_»
      (Init.Data.Sigma.Basic.«termΣ_,_»
       "Σ"
       (Lean.explicitBinders
        (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k) (Lean.binderIdent `l)] [":" (termℕ "ℕ")]))
       ", "
       («term{__:_//_}»
        "{"
        `s
        [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
        "//"
        («term_=_» `s.card "=" `l)
        "}"))
      " ≃ "
      (Init.Data.Sigma.Basic.«termΣ_,_»
       "Σ"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] [":" (termℕ "ℕ")]))
       ", "
       (Term.app `Finset [(Term.app `Finₓ [`n])]))))])
  (Command.declValSimple
   ":="
   (Term.structInst
    "{"
    []
    [(group
      (Term.structInstField
       (Term.structInstLVal `toFun [])
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`s] [])]
         "=>"
         (Term.anonymousCtor
          "⟨"
          [(Init.Logic.«term_+_»
            (Term.proj `s "." (fieldIdx "1"))
            "+"
            (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "1")))
           ","
           (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "2"))]
          "⟩"))))
      [","])
     (group
      (Term.structInstField
       (Term.structInstLVal `invFun [])
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`s] [])]
         "=>"
         (Term.anonymousCtor
          "⟨"
          [(«term_-_» (Term.proj `s "." (fieldIdx "1")) "-" (Term.proj (Term.proj `s "." (fieldIdx "2")) "." `card))
           ","
           (Term.proj (Term.proj `s "." (fieldIdx "2")) "." `card)
           ","
           (Term.anonymousCtor
            "⟨"
            [(Term.app
              (Term.proj (Term.proj `s "." (fieldIdx "2")) "." `map)
              [(Term.proj
                (Term.proj
                 («term_$__»
                  `Finₓ.cast
                  "$"
                  (Term.proj
                   («term_$__»
                    `tsub_add_cancel_of_le
                    "$"
                    (Term.app `card_finset_fin_le [(Term.proj `s "." (fieldIdx "2"))]))
                   "."
                   `symm))
                 "."
                 `toEquiv)
                "."
                `toEmbedding)])
             ","
             (Term.app `Finset.card_map [(Term.hole "_")])]
            "⟩")]
          "⟩"))))
      [","])
     (group
      (Term.structInstField
       (Term.structInstLVal `left_inv [])
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.rintro
             "rintro"
             [(Tactic.rintroPat.one
               (Tactic.rcasesPat.tuple
                "⟨"
                [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `k)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `l)]) [])
                 ","
                 (Tactic.rcasesPatLo
                  (Tactic.rcasesPatMed
                   [(Tactic.rcasesPat.tuple
                     "⟨"
                     [(Tactic.rcasesPatLo
                       (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `s)])
                       [":" (Term.app `Finset [(«term_$__» `Finₓ "$" (Init.Logic.«term_+_» `k "+" `l))])])
                      ","
                      (Tactic.rcasesPatLo
                       (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hs)])
                       [":" («term_=_» `s.card "=" `l)])]
                     "⟩")])
                  [])]
                "⟩"))]
             [])
            [])
           (group (Tactic.dsimp "dsimp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `Subtype.coe_mk)] "]"] [] []) [])
           (group
            (Tactic.tacticSuffices_
             "suffices"
             (Term.sufficesDecl
              []
              (Term.forall
               "∀"
               [(Term.simpleBinder [`k' `l'] [])]
               ","
               (Term.arrow
                («term_=_» `k' "=" `k)
                "→"
                (Term.arrow
                 («term_=_» `l' "=" `l)
                 "→"
                 (Term.forall
                  "∀"
                  [(Term.simpleBinder
                    [`hkl]
                    [(Term.typeSpec
                      ":"
                      («term_=_» (Init.Logic.«term_+_» `k "+" `l) "=" (Init.Logic.«term_+_» `k' "+" `l')))])
                   (Term.simpleBinder [`hs'] [])]
                  ","
                  («term_=_»
                   (Term.paren
                    "("
                    [(Term.anonymousCtor
                      "⟨"
                      [`k'
                       ","
                       `l'
                       ","
                       (Term.anonymousCtor
                        "⟨"
                        [(Term.app
                          `Finset.map
                          [(Term.proj (Term.proj (Term.app `Finₓ.cast [`hkl]) "." `toEquiv) "." `toEmbedding) `s])
                         ","
                         `hs']
                        "⟩")]
                      "⟩")
                     [(Term.typeAscription
                       ":"
                       (Init.Data.Sigma.Basic.«termΣ_,_»
                        "Σ"
                        (Lean.explicitBinders
                         (Lean.unbracketedExplicitBinders
                          [(Lean.binderIdent `k) (Lean.binderIdent `l)]
                          [":" (termℕ "ℕ")]))
                        ", "
                        («term{__:_//_}»
                         "{"
                         `s
                         [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
                         "//"
                         («term_=_» `s.card "=" `l)
                         "}")))]]
                    ")")
                   "="
                   (Term.anonymousCtor "⟨" [`k "," `l "," (Term.anonymousCtor "⟨" [`s "," `hs] "⟩")] "⟩"))))))
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group
                   (Tactic.«tactic_<;>_»
                    (Tactic.apply "apply" `this)
                    "<;>"
                    (Tactic.simp
                     "simp"
                     []
                     ["only"]
                     ["[" [(Tactic.simpLemma [] [] `hs) "," (Tactic.simpLemma [] [] `add_tsub_cancel_right)] "]"]
                     []))
                   [])])))))
            [])
           (group
            (Tactic.rintro
             "rintro"
             [(Tactic.rintroPat.one (Tactic.rcasesPat.ignore "_"))
              (Tactic.rintroPat.one (Tactic.rcasesPat.ignore "_"))
              (Tactic.rintroPat.one (Tactic.rcasesPat.one `rfl))
              (Tactic.rintroPat.one (Tactic.rcasesPat.one `rfl))
              (Tactic.rintroPat.one (Tactic.rcasesPat.one `hkl))
              (Tactic.rintroPat.one (Tactic.rcasesPat.one `hs'))]
             [])
            [])
           (group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `Equivₓ.refl_to_embedding)
               ","
               (Tactic.simpLemma [] [] `Finₓ.cast_refl)
               ","
               (Tactic.simpLemma [] [] `Finset.map_refl)
               ","
               (Tactic.simpLemma [] [] `eq_self_iff_true)
               ","
               (Tactic.simpLemma [] [] `OrderIso.refl_to_equiv)
               ","
               (Tactic.simpLemma [] [] `and_selfₓ)
               ","
               (Tactic.simpLemma [] [] `heq_iff_eq)]
              "]"]
             [])
            [])]))))
      [","])
     (group
      (Term.structInstField
       (Term.structInstLVal `right_inv [])
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.rintro
             "rintro"
             [(Tactic.rintroPat.one
               (Tactic.rcasesPat.tuple
                "⟨"
                [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `n)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `s)]) [])]
                "⟩"))]
             [])
            [])
           (group
            (Tactic.simp
             "simp"
             []
             []
             ["["
              [(Tactic.simpLemma [] [] (Term.app `tsub_add_cancel_of_le [(Term.app `card_finset_fin_le [`s])]))
               ","
               (Tactic.simpLemma [] [] `Finₓ.cast_to_equiv)]
              "]"]
             [])
            [])]))))
      [])]
    (Term.optEllipsis [])
    []
    "}")
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
  (Term.structInst
   "{"
   []
   [(group
     (Term.structInstField
      (Term.structInstLVal `toFun [])
      ":="
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`s] [])]
        "=>"
        (Term.anonymousCtor
         "⟨"
         [(Init.Logic.«term_+_»
           (Term.proj `s "." (fieldIdx "1"))
           "+"
           (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "1")))
          ","
          (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "2"))]
         "⟩"))))
     [","])
    (group
     (Term.structInstField
      (Term.structInstLVal `invFun [])
      ":="
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`s] [])]
        "=>"
        (Term.anonymousCtor
         "⟨"
         [(«term_-_» (Term.proj `s "." (fieldIdx "1")) "-" (Term.proj (Term.proj `s "." (fieldIdx "2")) "." `card))
          ","
          (Term.proj (Term.proj `s "." (fieldIdx "2")) "." `card)
          ","
          (Term.anonymousCtor
           "⟨"
           [(Term.app
             (Term.proj (Term.proj `s "." (fieldIdx "2")) "." `map)
             [(Term.proj
               (Term.proj
                («term_$__»
                 `Finₓ.cast
                 "$"
                 (Term.proj
                  («term_$__»
                   `tsub_add_cancel_of_le
                   "$"
                   (Term.app `card_finset_fin_le [(Term.proj `s "." (fieldIdx "2"))]))
                  "."
                  `symm))
                "."
                `toEquiv)
               "."
               `toEmbedding)])
            ","
            (Term.app `Finset.card_map [(Term.hole "_")])]
           "⟩")]
         "⟩"))))
     [","])
    (group
     (Term.structInstField
      (Term.structInstLVal `left_inv [])
      ":="
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group
           (Tactic.rintro
            "rintro"
            [(Tactic.rintroPat.one
              (Tactic.rcasesPat.tuple
               "⟨"
               [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `k)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `l)]) [])
                ","
                (Tactic.rcasesPatLo
                 (Tactic.rcasesPatMed
                  [(Tactic.rcasesPat.tuple
                    "⟨"
                    [(Tactic.rcasesPatLo
                      (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `s)])
                      [":" (Term.app `Finset [(«term_$__» `Finₓ "$" (Init.Logic.«term_+_» `k "+" `l))])])
                     ","
                     (Tactic.rcasesPatLo
                      (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hs)])
                      [":" («term_=_» `s.card "=" `l)])]
                    "⟩")])
                 [])]
               "⟩"))]
            [])
           [])
          (group (Tactic.dsimp "dsimp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `Subtype.coe_mk)] "]"] [] []) [])
          (group
           (Tactic.tacticSuffices_
            "suffices"
            (Term.sufficesDecl
             []
             (Term.forall
              "∀"
              [(Term.simpleBinder [`k' `l'] [])]
              ","
              (Term.arrow
               («term_=_» `k' "=" `k)
               "→"
               (Term.arrow
                («term_=_» `l' "=" `l)
                "→"
                (Term.forall
                 "∀"
                 [(Term.simpleBinder
                   [`hkl]
                   [(Term.typeSpec
                     ":"
                     («term_=_» (Init.Logic.«term_+_» `k "+" `l) "=" (Init.Logic.«term_+_» `k' "+" `l')))])
                  (Term.simpleBinder [`hs'] [])]
                 ","
                 («term_=_»
                  (Term.paren
                   "("
                   [(Term.anonymousCtor
                     "⟨"
                     [`k'
                      ","
                      `l'
                      ","
                      (Term.anonymousCtor
                       "⟨"
                       [(Term.app
                         `Finset.map
                         [(Term.proj (Term.proj (Term.app `Finₓ.cast [`hkl]) "." `toEquiv) "." `toEmbedding) `s])
                        ","
                        `hs']
                       "⟩")]
                     "⟩")
                    [(Term.typeAscription
                      ":"
                      (Init.Data.Sigma.Basic.«termΣ_,_»
                       "Σ"
                       (Lean.explicitBinders
                        (Lean.unbracketedExplicitBinders
                         [(Lean.binderIdent `k) (Lean.binderIdent `l)]
                         [":" (termℕ "ℕ")]))
                       ", "
                       («term{__:_//_}»
                        "{"
                        `s
                        [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
                        "//"
                        («term_=_» `s.card "=" `l)
                        "}")))]]
                   ")")
                  "="
                  (Term.anonymousCtor "⟨" [`k "," `l "," (Term.anonymousCtor "⟨" [`s "," `hs] "⟩")] "⟩"))))))
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.«tactic_<;>_»
                   (Tactic.apply "apply" `this)
                   "<;>"
                   (Tactic.simp
                    "simp"
                    []
                    ["only"]
                    ["[" [(Tactic.simpLemma [] [] `hs) "," (Tactic.simpLemma [] [] `add_tsub_cancel_right)] "]"]
                    []))
                  [])])))))
           [])
          (group
           (Tactic.rintro
            "rintro"
            [(Tactic.rintroPat.one (Tactic.rcasesPat.ignore "_"))
             (Tactic.rintroPat.one (Tactic.rcasesPat.ignore "_"))
             (Tactic.rintroPat.one (Tactic.rcasesPat.one `rfl))
             (Tactic.rintroPat.one (Tactic.rcasesPat.one `rfl))
             (Tactic.rintroPat.one (Tactic.rcasesPat.one `hkl))
             (Tactic.rintroPat.one (Tactic.rcasesPat.one `hs'))]
            [])
           [])
          (group
           (Tactic.simp
            "simp"
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `Equivₓ.refl_to_embedding)
              ","
              (Tactic.simpLemma [] [] `Finₓ.cast_refl)
              ","
              (Tactic.simpLemma [] [] `Finset.map_refl)
              ","
              (Tactic.simpLemma [] [] `eq_self_iff_true)
              ","
              (Tactic.simpLemma [] [] `OrderIso.refl_to_equiv)
              ","
              (Tactic.simpLemma [] [] `and_selfₓ)
              ","
              (Tactic.simpLemma [] [] `heq_iff_eq)]
             "]"]
            [])
           [])]))))
     [","])
    (group
     (Term.structInstField
      (Term.structInstLVal `right_inv [])
      ":="
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group
           (Tactic.rintro
            "rintro"
            [(Tactic.rintroPat.one
              (Tactic.rcasesPat.tuple
               "⟨"
               [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `n)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `s)]) [])]
               "⟩"))]
            [])
           [])
          (group
           (Tactic.simp
            "simp"
            []
            []
            ["["
             [(Tactic.simpLemma [] [] (Term.app `tsub_add_cancel_of_le [(Term.app `card_finset_fin_le [`s])]))
              ","
              (Tactic.simpLemma [] [] `Finₓ.cast_to_equiv)]
             "]"]
            [])
           [])]))))
     [])]
   (Term.optEllipsis [])
   []
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.structInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.optEllipsis', expected 'Lean.Parser.Term.optEllipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstField.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rintro
        "rintro"
        [(Tactic.rintroPat.one
          (Tactic.rcasesPat.tuple
           "⟨"
           [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `n)]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `s)]) [])]
           "⟩"))]
        [])
       [])
      (group
       (Tactic.simp
        "simp"
        []
        []
        ["["
         [(Tactic.simpLemma [] [] (Term.app `tsub_add_cancel_of_le [(Term.app `card_finset_fin_le [`s])]))
          ","
          (Tactic.simpLemma [] [] `Finₓ.cast_to_equiv)]
         "]"]
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp
   "simp"
   []
   []
   ["["
    [(Tactic.simpLemma [] [] (Term.app `tsub_add_cancel_of_le [(Term.app `card_finset_fin_le [`s])]))
     ","
     (Tactic.simpLemma [] [] `Finₓ.cast_to_equiv)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finₓ.cast_to_equiv
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `tsub_add_cancel_of_le [(Term.app `card_finset_fin_le [`s])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `card_finset_fin_le [`s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `card_finset_fin_le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `card_finset_fin_le [`s]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `tsub_add_cancel_of_le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rintro
   "rintro"
   [(Tactic.rintroPat.one
     (Tactic.rcasesPat.tuple
      "⟨"
      [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `n)]) [])
       ","
       (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `s)]) [])]
      "⟩"))]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstLVal', expected 'Lean.Parser.Term.structInstLVal.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«,»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstField.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rintro
        "rintro"
        [(Tactic.rintroPat.one
          (Tactic.rcasesPat.tuple
           "⟨"
           [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `k)]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `l)]) [])
            ","
            (Tactic.rcasesPatLo
             (Tactic.rcasesPatMed
              [(Tactic.rcasesPat.tuple
                "⟨"
                [(Tactic.rcasesPatLo
                  (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `s)])
                  [":" (Term.app `Finset [(«term_$__» `Finₓ "$" (Init.Logic.«term_+_» `k "+" `l))])])
                 ","
                 (Tactic.rcasesPatLo
                  (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hs)])
                  [":" («term_=_» `s.card "=" `l)])]
                "⟩")])
             [])]
           "⟩"))]
        [])
       [])
      (group (Tactic.dsimp "dsimp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `Subtype.coe_mk)] "]"] [] []) [])
      (group
       (Tactic.tacticSuffices_
        "suffices"
        (Term.sufficesDecl
         []
         (Term.forall
          "∀"
          [(Term.simpleBinder [`k' `l'] [])]
          ","
          (Term.arrow
           («term_=_» `k' "=" `k)
           "→"
           (Term.arrow
            («term_=_» `l' "=" `l)
            "→"
            (Term.forall
             "∀"
             [(Term.simpleBinder
               [`hkl]
               [(Term.typeSpec
                 ":"
                 («term_=_» (Init.Logic.«term_+_» `k "+" `l) "=" (Init.Logic.«term_+_» `k' "+" `l')))])
              (Term.simpleBinder [`hs'] [])]
             ","
             («term_=_»
              (Term.paren
               "("
               [(Term.anonymousCtor
                 "⟨"
                 [`k'
                  ","
                  `l'
                  ","
                  (Term.anonymousCtor
                   "⟨"
                   [(Term.app
                     `Finset.map
                     [(Term.proj (Term.proj (Term.app `Finₓ.cast [`hkl]) "." `toEquiv) "." `toEmbedding) `s])
                    ","
                    `hs']
                   "⟩")]
                 "⟩")
                [(Term.typeAscription
                  ":"
                  (Init.Data.Sigma.Basic.«termΣ_,_»
                   "Σ"
                   (Lean.explicitBinders
                    (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k) (Lean.binderIdent `l)] [":" (termℕ "ℕ")]))
                   ", "
                   («term{__:_//_}»
                    "{"
                    `s
                    [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
                    "//"
                    («term_=_» `s.card "=" `l)
                    "}")))]]
               ")")
              "="
              (Term.anonymousCtor "⟨" [`k "," `l "," (Term.anonymousCtor "⟨" [`s "," `hs] "⟩")] "⟩"))))))
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group
              (Tactic.«tactic_<;>_»
               (Tactic.apply "apply" `this)
               "<;>"
               (Tactic.simp
                "simp"
                []
                ["only"]
                ["[" [(Tactic.simpLemma [] [] `hs) "," (Tactic.simpLemma [] [] `add_tsub_cancel_right)] "]"]
                []))
              [])])))))
       [])
      (group
       (Tactic.rintro
        "rintro"
        [(Tactic.rintroPat.one (Tactic.rcasesPat.ignore "_"))
         (Tactic.rintroPat.one (Tactic.rcasesPat.ignore "_"))
         (Tactic.rintroPat.one (Tactic.rcasesPat.one `rfl))
         (Tactic.rintroPat.one (Tactic.rcasesPat.one `rfl))
         (Tactic.rintroPat.one (Tactic.rcasesPat.one `hkl))
         (Tactic.rintroPat.one (Tactic.rcasesPat.one `hs'))]
        [])
       [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `Equivₓ.refl_to_embedding)
          ","
          (Tactic.simpLemma [] [] `Finₓ.cast_refl)
          ","
          (Tactic.simpLemma [] [] `Finset.map_refl)
          ","
          (Tactic.simpLemma [] [] `eq_self_iff_true)
          ","
          (Tactic.simpLemma [] [] `OrderIso.refl_to_equiv)
          ","
          (Tactic.simpLemma [] [] `and_selfₓ)
          ","
          (Tactic.simpLemma [] [] `heq_iff_eq)]
         "]"]
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["["
    [(Tactic.simpLemma [] [] `Equivₓ.refl_to_embedding)
     ","
     (Tactic.simpLemma [] [] `Finₓ.cast_refl)
     ","
     (Tactic.simpLemma [] [] `Finset.map_refl)
     ","
     (Tactic.simpLemma [] [] `eq_self_iff_true)
     ","
     (Tactic.simpLemma [] [] `OrderIso.refl_to_equiv)
     ","
     (Tactic.simpLemma [] [] `and_selfₓ)
     ","
     (Tactic.simpLemma [] [] `heq_iff_eq)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `heq_iff_eq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `and_selfₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `OrderIso.refl_to_equiv
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `eq_self_iff_true
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.map_refl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finₓ.cast_refl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Equivₓ.refl_to_embedding
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rintro
   "rintro"
   [(Tactic.rintroPat.one (Tactic.rcasesPat.ignore "_"))
    (Tactic.rintroPat.one (Tactic.rcasesPat.ignore "_"))
    (Tactic.rintroPat.one (Tactic.rcasesPat.one `rfl))
    (Tactic.rintroPat.one (Tactic.rcasesPat.one `rfl))
    (Tactic.rintroPat.one (Tactic.rcasesPat.one `hkl))
    (Tactic.rintroPat.one (Tactic.rcasesPat.one `hs'))]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.ignore', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.ignore', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticSuffices_
   "suffices"
   (Term.sufficesDecl
    []
    (Term.forall
     "∀"
     [(Term.simpleBinder [`k' `l'] [])]
     ","
     (Term.arrow
      («term_=_» `k' "=" `k)
      "→"
      (Term.arrow
       («term_=_» `l' "=" `l)
       "→"
       (Term.forall
        "∀"
        [(Term.simpleBinder
          [`hkl]
          [(Term.typeSpec ":" («term_=_» (Init.Logic.«term_+_» `k "+" `l) "=" (Init.Logic.«term_+_» `k' "+" `l')))])
         (Term.simpleBinder [`hs'] [])]
        ","
        («term_=_»
         (Term.paren
          "("
          [(Term.anonymousCtor
            "⟨"
            [`k'
             ","
             `l'
             ","
             (Term.anonymousCtor
              "⟨"
              [(Term.app
                `Finset.map
                [(Term.proj (Term.proj (Term.app `Finₓ.cast [`hkl]) "." `toEquiv) "." `toEmbedding) `s])
               ","
               `hs']
              "⟩")]
            "⟩")
           [(Term.typeAscription
             ":"
             (Init.Data.Sigma.Basic.«termΣ_,_»
              "Σ"
              (Lean.explicitBinders
               (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k) (Lean.binderIdent `l)] [":" (termℕ "ℕ")]))
              ", "
              («term{__:_//_}»
               "{"
               `s
               [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
               "//"
               («term_=_» `s.card "=" `l)
               "}")))]]
          ")")
         "="
         (Term.anonymousCtor "⟨" [`k "," `l "," (Term.anonymousCtor "⟨" [`s "," `hs] "⟩")] "⟩"))))))
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group
         (Tactic.«tactic_<;>_»
          (Tactic.apply "apply" `this)
          "<;>"
          (Tactic.simp
           "simp"
           []
           ["only"]
           ["[" [(Tactic.simpLemma [] [] `hs) "," (Tactic.simpLemma [] [] `add_tsub_cancel_right)] "]"]
           []))
         [])])))))
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
  (Tactic.«tactic_<;>_»
   (Tactic.apply "apply" `this)
   "<;>"
   (Tactic.simp
    "simp"
    []
    ["only"]
    ["[" [(Tactic.simpLemma [] [] `hs) "," (Tactic.simpLemma [] [] `add_tsub_cancel_right)] "]"]
    []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic_<;>_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["[" [(Tactic.simpLemma [] [] `hs) "," (Tactic.simpLemma [] [] `add_tsub_cancel_right)] "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `add_tsub_cancel_right
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hs
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
  (Tactic.apply "apply" `this)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder [`k' `l'] [])]
   ","
   (Term.arrow
    («term_=_» `k' "=" `k)
    "→"
    (Term.arrow
     («term_=_» `l' "=" `l)
     "→"
     (Term.forall
      "∀"
      [(Term.simpleBinder
        [`hkl]
        [(Term.typeSpec ":" («term_=_» (Init.Logic.«term_+_» `k "+" `l) "=" (Init.Logic.«term_+_» `k' "+" `l')))])
       (Term.simpleBinder [`hs'] [])]
      ","
      («term_=_»
       (Term.paren
        "("
        [(Term.anonymousCtor
          "⟨"
          [`k'
           ","
           `l'
           ","
           (Term.anonymousCtor
            "⟨"
            [(Term.app
              `Finset.map
              [(Term.proj (Term.proj (Term.app `Finₓ.cast [`hkl]) "." `toEquiv) "." `toEmbedding) `s])
             ","
             `hs']
            "⟩")]
          "⟩")
         [(Term.typeAscription
           ":"
           (Init.Data.Sigma.Basic.«termΣ_,_»
            "Σ"
            (Lean.explicitBinders
             (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k) (Lean.binderIdent `l)] [":" (termℕ "ℕ")]))
            ", "
            («term{__:_//_}»
             "{"
             `s
             [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
             "//"
             («term_=_» `s.card "=" `l)
             "}")))]]
        ")")
       "="
       (Term.anonymousCtor "⟨" [`k "," `l "," (Term.anonymousCtor "⟨" [`s "," `hs] "⟩")] "⟩"))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.arrow
   («term_=_» `k' "=" `k)
   "→"
   (Term.arrow
    («term_=_» `l' "=" `l)
    "→"
    (Term.forall
     "∀"
     [(Term.simpleBinder
       [`hkl]
       [(Term.typeSpec ":" («term_=_» (Init.Logic.«term_+_» `k "+" `l) "=" (Init.Logic.«term_+_» `k' "+" `l')))])
      (Term.simpleBinder [`hs'] [])]
     ","
     («term_=_»
      (Term.paren
       "("
       [(Term.anonymousCtor
         "⟨"
         [`k'
          ","
          `l'
          ","
          (Term.anonymousCtor
           "⟨"
           [(Term.app
             `Finset.map
             [(Term.proj (Term.proj (Term.app `Finₓ.cast [`hkl]) "." `toEquiv) "." `toEmbedding) `s])
            ","
            `hs']
           "⟩")]
         "⟩")
        [(Term.typeAscription
          ":"
          (Init.Data.Sigma.Basic.«termΣ_,_»
           "Σ"
           (Lean.explicitBinders
            (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k) (Lean.binderIdent `l)] [":" (termℕ "ℕ")]))
           ", "
           («term{__:_//_}»
            "{"
            `s
            [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
            "//"
            («term_=_» `s.card "=" `l)
            "}")))]]
       ")")
      "="
      (Term.anonymousCtor "⟨" [`k "," `l "," (Term.anonymousCtor "⟨" [`s "," `hs] "⟩")] "⟩")))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.arrow', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.arrow
   («term_=_» `l' "=" `l)
   "→"
   (Term.forall
    "∀"
    [(Term.simpleBinder
      [`hkl]
      [(Term.typeSpec ":" («term_=_» (Init.Logic.«term_+_» `k "+" `l) "=" (Init.Logic.«term_+_» `k' "+" `l')))])
     (Term.simpleBinder [`hs'] [])]
    ","
    («term_=_»
     (Term.paren
      "("
      [(Term.anonymousCtor
        "⟨"
        [`k'
         ","
         `l'
         ","
         (Term.anonymousCtor
          "⟨"
          [(Term.app
            `Finset.map
            [(Term.proj (Term.proj (Term.app `Finₓ.cast [`hkl]) "." `toEquiv) "." `toEmbedding) `s])
           ","
           `hs']
          "⟩")]
        "⟩")
       [(Term.typeAscription
         ":"
         (Init.Data.Sigma.Basic.«termΣ_,_»
          "Σ"
          (Lean.explicitBinders
           (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k) (Lean.binderIdent `l)] [":" (termℕ "ℕ")]))
          ", "
          («term{__:_//_}»
           "{"
           `s
           [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
           "//"
           («term_=_» `s.card "=" `l)
           "}")))]]
      ")")
     "="
     (Term.anonymousCtor "⟨" [`k "," `l "," (Term.anonymousCtor "⟨" [`s "," `hs] "⟩")] "⟩"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.arrow', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder
     [`hkl]
     [(Term.typeSpec ":" («term_=_» (Init.Logic.«term_+_» `k "+" `l) "=" (Init.Logic.«term_+_» `k' "+" `l')))])
    (Term.simpleBinder [`hs'] [])]
   ","
   («term_=_»
    (Term.paren
     "("
     [(Term.anonymousCtor
       "⟨"
       [`k'
        ","
        `l'
        ","
        (Term.anonymousCtor
         "⟨"
         [(Term.app `Finset.map [(Term.proj (Term.proj (Term.app `Finₓ.cast [`hkl]) "." `toEquiv) "." `toEmbedding) `s])
          ","
          `hs']
         "⟩")]
       "⟩")
      [(Term.typeAscription
        ":"
        (Init.Data.Sigma.Basic.«termΣ_,_»
         "Σ"
         (Lean.explicitBinders
          (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k) (Lean.binderIdent `l)] [":" (termℕ "ℕ")]))
         ", "
         («term{__:_//_}»
          "{"
          `s
          [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
          "//"
          («term_=_» `s.card "=" `l)
          "}")))]]
     ")")
    "="
    (Term.anonymousCtor "⟨" [`k "," `l "," (Term.anonymousCtor "⟨" [`s "," `hs] "⟩")] "⟩")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.paren
    "("
    [(Term.anonymousCtor
      "⟨"
      [`k'
       ","
       `l'
       ","
       (Term.anonymousCtor
        "⟨"
        [(Term.app `Finset.map [(Term.proj (Term.proj (Term.app `Finₓ.cast [`hkl]) "." `toEquiv) "." `toEmbedding) `s])
         ","
         `hs']
        "⟩")]
      "⟩")
     [(Term.typeAscription
       ":"
       (Init.Data.Sigma.Basic.«termΣ_,_»
        "Σ"
        (Lean.explicitBinders
         (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k) (Lean.binderIdent `l)] [":" (termℕ "ℕ")]))
        ", "
        («term{__:_//_}»
         "{"
         `s
         [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
         "//"
         («term_=_» `s.card "=" `l)
         "}")))]]
    ")")
   "="
   (Term.anonymousCtor "⟨" [`k "," `l "," (Term.anonymousCtor "⟨" [`s "," `hs] "⟩")] "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`k "," `l "," (Term.anonymousCtor "⟨" [`s "," `hs] "⟩")] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`s "," `hs] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hs
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `l
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.paren
   "("
   [(Term.anonymousCtor
     "⟨"
     [`k'
      ","
      `l'
      ","
      (Term.anonymousCtor
       "⟨"
       [(Term.app `Finset.map [(Term.proj (Term.proj (Term.app `Finₓ.cast [`hkl]) "." `toEquiv) "." `toEmbedding) `s])
        ","
        `hs']
       "⟩")]
     "⟩")
    [(Term.typeAscription
      ":"
      (Init.Data.Sigma.Basic.«termΣ_,_»
       "Σ"
       (Lean.explicitBinders
        (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k) (Lean.binderIdent `l)] [":" (termℕ "ℕ")]))
       ", "
       («term{__:_//_}»
        "{"
        `s
        [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
        "//"
        («term_=_» `s.card "=" `l)
        "}")))]]
   ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Data.Sigma.Basic.«termΣ_,_»
   "Σ"
   (Lean.explicitBinders
    (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k) (Lean.binderIdent `l)] [":" (termℕ "ℕ")]))
   ", "
   («term{__:_//_}»
    "{"
    `s
    [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
    "//"
    («term_=_» `s.card "=" `l)
    "}"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Data.Sigma.Basic.«termΣ_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term{__:_//_}»
   "{"
   `s
   [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
   "//"
   («term_=_» `s.card "=" `l)
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term{__:_//_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» `s.card "=" `l)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `l
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `s.card
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `k "+" `l)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `l
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `k "+" `l) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `Finₓ [(Term.paren "(" [(Init.Logic.«term_+_» `k "+" `l) []] ")")]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finset
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
      An auxiliary equivalence useful in the proofs about
      `formal_multilinear_series.change_origin_series`: the set of triples `(k, l, s)`, where `s` is a
      `finset (fin (k + l))` of cardinality `l` is equivalent to the set of pairs `(n, s)`, where `s` is a
      `finset (fin n)`.
      
      The forward map sends `(k, l, s)` to `(k + l, s)` and the inverse map sends `(n, s)` to
      `(n - finset.card s, finset.card s, s)`. The actual definition is less readable because of problems
      with non-definitional equalities. -/
    @[ simps ]
  def
    change_origin_index_equiv
    : Σ k l : ℕ , { s : Finset Finₓ k + l // s.card = l } ≃ Σ n : ℕ , Finset Finₓ n
    :=
      {
        toFun := fun s => ⟨ s . 1 + s . 2 . 1 , s . 2 . 2 ⟩ ,
          invFun
              :=
              fun
                s
                  =>
                  ⟨
                    s . 1 - s . 2 . card
                      ,
                      s . 2 . card
                      ,
                      ⟨
                        s . 2 . map
                            Finₓ.cast $ tsub_add_cancel_of_le $ card_finset_fin_le s . 2 . symm . toEquiv . toEmbedding
                          ,
                          Finset.card_map _
                        ⟩
                    ⟩
            ,
          left_inv
              :=
              by
                rintro ⟨ k , l , ⟨ s : Finset Finₓ $ k + l , hs : s.card = l ⟩ ⟩
                  dsimp only [ Subtype.coe_mk ]
                  suffices
                    ∀
                        k' l'
                        ,
                        k' = k
                          →
                          l' = l
                            →
                            ∀
                              hkl : k + l = k' + l' hs'
                              ,
                              (
                                  ⟨ k' , l' , ⟨ Finset.map Finₓ.cast hkl . toEquiv . toEmbedding s , hs' ⟩ ⟩
                                    : Σ k l : ℕ , { s : Finset Finₓ k + l // s.card = l }
                                  )
                                =
                                ⟨ k , l , ⟨ s , hs ⟩ ⟩
                      by apply this <;> simp only [ hs , add_tsub_cancel_right ]
                  rintro _ _ rfl rfl hkl hs'
                  simp
                    only
                    [
                      Equivₓ.refl_to_embedding
                        ,
                        Finₓ.cast_refl
                        ,
                        Finset.map_refl
                        ,
                        eq_self_iff_true
                        ,
                        OrderIso.refl_to_equiv
                        ,
                        and_selfₓ
                        ,
                        heq_iff_eq
                      ]
            ,
          right_inv := by rintro ⟨ n , s ⟩ simp [ tsub_add_cancel_of_le card_finset_fin_le s , Finₓ.cast_to_equiv ]
        }

theorem change_origin_series_summable_aux₁ {r r' : ℝ≥0 } (hr : (r+r' : ℝ≥0∞) < p.radius) :
    Summable fun s => (∥p (s.1+s.2.1)∥₊*r ^ s.2.1)*r' ^ s.1 := by
  rw [← change_origin_index_equiv.symm.summable_iff]
  dsimp only [· ∘ ·, change_origin_index_equiv_symm_apply_fst, change_origin_index_equiv_symm_apply_snd_fst]
  have :
    ∀ n : ℕ,
      HasSum (fun s : Finset (Finₓ n) => (∥p ((n - s.card)+s.card)∥₊*r ^ s.card)*r' ^ (n - s.card))
        (∥p n∥₊*(r+r') ^ n) :=
    by
    intro n
    convert_to HasSum (fun s : Finset (Finₓ n) => ∥p n∥₊*(r ^ s.card)*r' ^ (n - s.card)) _
    ·
      ext1 s
      rw [tsub_add_cancel_of_le (card_finset_fin_le _), mul_assocₓ]
    rw [← Finₓ.sum_pow_mul_eq_add_pow]
    exact (has_sum_fintype _).mul_left _
  refine' Nnreal.summable_sigma.2 ⟨fun n => (this n).Summable, _⟩
  simp only [(this _).tsum_eq]
  exact p.summable_nnnorm_mul_pow hr

theorem change_origin_series_summable_aux₂ (hr : (r : ℝ≥0∞) < p.radius) (k : ℕ) :
    Summable fun s => ∥p (k+s.1)∥₊*r ^ s.1 := by
  rcases Ennreal.lt_iff_exists_add_pos_lt.1 hr with ⟨r', h0, hr'⟩
  simpa only [mul_inv_cancel_right₀ (pow_pos h0 _).ne'] using
    ((Nnreal.summable_sigma.1 (p.change_origin_series_summable_aux₁ hr')).1 k).mul_right ((r' ^ k)⁻¹)

theorem change_origin_series_summable_aux₃ {r : ℝ≥0 } (hr : ↑r < p.radius) (k : ℕ) :
    Summable fun l : ℕ => ∥p.change_origin_series k l∥₊*r ^ l := by
  refine' Nnreal.summable_of_le (fun n => _) (Nnreal.summable_sigma.1 $ p.change_origin_series_summable_aux₂ hr k).2
  simp only [Nnreal.tsum_mul_right]
  exact mul_le_mul' (p.nnnorm_change_origin_series_le_tsum _ _) le_rfl

theorem le_change_origin_series_radius (k : ℕ) : p.radius ≤ (p.change_origin_series k).radius :=
  Ennreal.le_of_forall_nnreal_lt $ fun r hr =>
    le_radius_of_summable_nnnorm _ (p.change_origin_series_summable_aux₃ hr k)

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `nnnorm_change_origin_le [])
  (Command.declSig
   [(Term.explicitBinder "(" [`k] [":" (termℕ "ℕ")] [] ")")
    (Term.explicitBinder
     "("
     [`h]
     [":"
      («term_<_»
       (Term.paren
        "("
        [(Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" `x "∥₊")
         [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]]
        ")")
       "<"
       `p.radius)]
     []
     ")")]
   (Term.typeSpec
    ":"
    («term_≤_»
     (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" (Term.app `p.change_origin [`x `k]) "∥₊")
     "≤"
     (Topology.Algebra.InfiniteSum.«term∑'_,_»
      "∑'"
      (Lean.explicitBinders
       (Lean.unbracketedExplicitBinders
        [(Lean.binderIdent `s)]
        [":"
         (Init.Data.Sigma.Basic.«termΣ_,_»
          "Σ"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `l)] [":" (termℕ "ℕ")]))
          ", "
          («term{__:_//_}»
           "{"
           `s
           [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
           "//"
           («term_=_» `s.card "=" `l)
           "}"))]))
      ", "
      (Finset.Data.Finset.Fold.«term_*_»
       (Analysis.Normed.Group.Basic.«term∥_∥₊»
        "∥"
        (Term.app `p [(Init.Logic.«term_+_» `k "+" (Term.proj `s "." (fieldIdx "1")))])
        "∥₊")
       "*"
       («term_^_» (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" `x "∥₊") "^" (Term.proj `s "." (fieldIdx "1"))))))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.refine'
         "refine'"
         (Term.app
          `tsum_of_nnnorm_bounded
          [(Term.hole "_")
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`l] [])]
             "=>"
             (Term.app `p.nnnorm_change_origin_series_apply_le_tsum [`k `l `x])))]))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `p.change_origin_series_summable_aux₂ [`h `k]))))
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.app
          `HasSum.sigma
          [`this.has_sum (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`l] [])] "=>" (Term.hole "_")))]))
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.proj
          (Term.app
           (Term.proj (Term.app (Term.proj `Nnreal.summable_sigma "." (fieldIdx "1")) [`this]) "." (fieldIdx "1"))
           [`l])
          "."
          `HasSum))
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
       (Tactic.refine'
        "refine'"
        (Term.app
         `tsum_of_nnnorm_bounded
         [(Term.hole "_")
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`l] [])]
            "=>"
            (Term.app `p.nnnorm_change_origin_series_apply_le_tsum [`k `l `x])))]))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `p.change_origin_series_summable_aux₂ [`h `k]))))
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         `HasSum.sigma
         [`this.has_sum (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`l] [])] "=>" (Term.hole "_")))]))
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.proj
         (Term.app
          (Term.proj (Term.app (Term.proj `Nnreal.summable_sigma "." (fieldIdx "1")) [`this]) "." (fieldIdx "1"))
          [`l])
         "."
         `HasSum))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.proj
    (Term.app
     (Term.proj (Term.app (Term.proj `Nnreal.summable_sigma "." (fieldIdx "1")) [`this]) "." (fieldIdx "1"))
     [`l])
    "."
    `HasSum))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj
   (Term.app
    (Term.proj (Term.app (Term.proj `Nnreal.summable_sigma "." (fieldIdx "1")) [`this]) "." (fieldIdx "1"))
    [`l])
   "."
   `HasSum)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app
   (Term.proj (Term.app (Term.proj `Nnreal.summable_sigma "." (fieldIdx "1")) [`this]) "." (fieldIdx "1"))
   [`l])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `l
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.app (Term.proj `Nnreal.summable_sigma "." (fieldIdx "1")) [`this]) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app (Term.proj `Nnreal.summable_sigma "." (fieldIdx "1")) [`this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `Nnreal.summable_sigma "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `Nnreal.summable_sigma
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app (Term.proj `Nnreal.summable_sigma "." (fieldIdx "1")) [`this]) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   (Term.proj
    (Term.paren "(" [(Term.app (Term.proj `Nnreal.summable_sigma "." (fieldIdx "1")) [`this]) []] ")")
    "."
    (fieldIdx "1"))
   [`l])
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    `HasSum.sigma
    [`this.has_sum (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`l] [])] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `HasSum.sigma
   [`this.has_sum (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`l] [])] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`l] [])] "=>" (Term.hole "_")))
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `this.has_sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `HasSum.sigma
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `p.change_origin_series_summable_aux₂ [`h `k]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `p.change_origin_series_summable_aux₂ [`h `k])
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
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p.change_origin_series_summable_aux₂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    `tsum_of_nnnorm_bounded
    [(Term.hole "_")
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`l] [])]
       "=>"
       (Term.app `p.nnnorm_change_origin_series_apply_le_tsum [`k `l `x])))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `tsum_of_nnnorm_bounded
   [(Term.hole "_")
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`l] [])]
      "=>"
      (Term.app `p.nnnorm_change_origin_series_apply_le_tsum [`k `l `x])))])
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
    [(Term.simpleBinder [`l] [])]
    "=>"
    (Term.app `p.nnnorm_change_origin_series_apply_le_tsum [`k `l `x])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `p.nnnorm_change_origin_series_apply_le_tsum [`k `l `x])
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
  `l
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p.nnnorm_change_origin_series_apply_le_tsum
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
  `tsum_of_nnnorm_bounded
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_≤_»
   (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" (Term.app `p.change_origin [`x `k]) "∥₊")
   "≤"
   (Topology.Algebra.InfiniteSum.«term∑'_,_»
    "∑'"
    (Lean.explicitBinders
     (Lean.unbracketedExplicitBinders
      [(Lean.binderIdent `s)]
      [":"
       (Init.Data.Sigma.Basic.«termΣ_,_»
        "Σ"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `l)] [":" (termℕ "ℕ")]))
        ", "
        («term{__:_//_}»
         "{"
         `s
         [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
         "//"
         («term_=_» `s.card "=" `l)
         "}"))]))
    ", "
    (Finset.Data.Finset.Fold.«term_*_»
     (Analysis.Normed.Group.Basic.«term∥_∥₊»
      "∥"
      (Term.app `p [(Init.Logic.«term_+_» `k "+" (Term.proj `s "." (fieldIdx "1")))])
      "∥₊")
     "*"
     («term_^_» (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" `x "∥₊") "^" (Term.proj `s "." (fieldIdx "1"))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Topology.Algebra.InfiniteSum.«term∑'_,_»
   "∑'"
   (Lean.explicitBinders
    (Lean.unbracketedExplicitBinders
     [(Lean.binderIdent `s)]
     [":"
      (Init.Data.Sigma.Basic.«termΣ_,_»
       "Σ"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `l)] [":" (termℕ "ℕ")]))
       ", "
       («term{__:_//_}»
        "{"
        `s
        [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
        "//"
        («term_=_» `s.card "=" `l)
        "}"))]))
   ", "
   (Finset.Data.Finset.Fold.«term_*_»
    (Analysis.Normed.Group.Basic.«term∥_∥₊»
     "∥"
     (Term.app `p [(Init.Logic.«term_+_» `k "+" (Term.proj `s "." (fieldIdx "1")))])
     "∥₊")
    "*"
    («term_^_» (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" `x "∥₊") "^" (Term.proj `s "." (fieldIdx "1")))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Algebra.InfiniteSum.«term∑'_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   (Analysis.Normed.Group.Basic.«term∥_∥₊»
    "∥"
    (Term.app `p [(Init.Logic.«term_+_» `k "+" (Term.proj `s "." (fieldIdx "1")))])
    "∥₊")
   "*"
   («term_^_» (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" `x "∥₊") "^" (Term.proj `s "." (fieldIdx "1"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_^_» (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" `x "∥₊") "^" (Term.proj `s "." (fieldIdx "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `s "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" `x "∥₊")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥₊»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Analysis.Normed.Group.Basic.«term∥_∥₊»
   "∥"
   (Term.app `p [(Init.Logic.«term_+_» `k "+" (Term.proj `s "." (fieldIdx "1")))])
   "∥₊")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥₊»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `p [(Init.Logic.«term_+_» `k "+" (Term.proj `s "." (fieldIdx "1")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `k "+" (Term.proj `s "." (fieldIdx "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `s "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Init.Logic.«term_+_» `k "+" (Term.proj `s "." (fieldIdx "1"))) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
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
theorem
  nnnorm_change_origin_le
  ( k : ℕ ) ( h : ( ∥ x ∥₊ : ℝ≥0∞ ) < p.radius )
    :
      ∥ p.change_origin x k ∥₊
        ≤
        ∑' s : Σ l : ℕ , { s : Finset Finₓ k + l // s.card = l } , ∥ p k + s . 1 ∥₊ * ∥ x ∥₊ ^ s . 1
  :=
    by
      refine' tsum_of_nnnorm_bounded _ fun l => p.nnnorm_change_origin_series_apply_le_tsum k l x
        have := p.change_origin_series_summable_aux₂ h k
        refine' HasSum.sigma this.has_sum fun l => _
        exact Nnreal.summable_sigma . 1 this . 1 l . HasSum

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " The radius of convergence of `p.change_origin x` is at least `p.radius - ∥x∥`. In other words,\n`p.change_origin x` is well defined on the largest ball contained in the original ball of\nconvergence.-/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `change_origin_radius [])
  (Command.declSig
   []
   (Term.typeSpec
    ":"
    («term_≤_»
     («term_-_» `p.radius "-" (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" `x "∥₊"))
     "≤"
     (Term.proj (Term.app `p.change_origin [`x]) "." `radius))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.refine'
         "refine'"
         (Term.app
          `Ennreal.le_of_forall_pos_nnreal_lt
          [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`r `h0 `hr] [])] "=>" (Term.hole "_")))]))
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `lt_tsub_iff_right) "," (Tactic.rwRule [] `add_commₓ)] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`hr] []))])
        [])
       (group
        (Tactic.have''
         "have"
         [`hr' []]
         [(Term.typeSpec
           ":"
           («term_<_»
            (Term.paren
             "("
             [(Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" `x "∥₊")
              [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]]
             ")")
            "<"
            `p.radius))])
        [])
       (group (Tactic.exact "exact" (Term.app (Term.proj (Term.app `le_add_right [`le_rfl]) "." `trans_lt) [`hr])) [])
       (group (Tactic.apply "apply" `le_radius_of_summable_nnnorm) [])
       (group
        (Tactic.have''
         "have"
         []
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            [(Term.simpleBinder [`k] [(Term.typeSpec ":" (termℕ "ℕ"))])]
            ","
            («term_≤_»
             (Finset.Data.Finset.Fold.«term_*_»
              (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" (Term.app `p.change_origin [`x `k]) "∥₊")
              "*"
              («term_^_» `r "^" `k))
             "≤"
             (Finset.Data.Finset.Fold.«term_*_»
              (Topology.Algebra.InfiniteSum.«term∑'_,_»
               "∑'"
               (Lean.explicitBinders
                (Lean.unbracketedExplicitBinders
                 [(Lean.binderIdent `s)]
                 [":"
                  (Init.Data.Sigma.Basic.«termΣ_,_»
                   "Σ"
                   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `l)] [":" (termℕ "ℕ")]))
                   ", "
                   («term{__:_//_}»
                    "{"
                    `s
                    [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
                    "//"
                    («term_=_» `s.card "=" `l)
                    "}"))]))
               ", "
               (Finset.Data.Finset.Fold.«term_*_»
                (Analysis.Normed.Group.Basic.«term∥_∥₊»
                 "∥"
                 (Term.app `p [(Init.Logic.«term_+_» `k "+" (Term.proj `s "." (fieldIdx "1")))])
                 "∥₊")
                "*"
                («term_^_» (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" `x "∥₊") "^" (Term.proj `s "." (fieldIdx "1")))))
              "*"
              («term_^_» `r "^" `k)))))])
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`k] [])]
           "=>"
           (Term.app `mul_le_mul_right' [(Term.app `p.nnnorm_change_origin_le [`k `hr']) («term_^_» `r "^" `k)]))))
        [])
       (group (Tactic.refine' "refine'" (Term.app `Nnreal.summable_of_le [`this (Term.hole "_")])) [])
       (group
        (Tactic.simpa
         "simpa"
         []
         ["only"]
         ["[" [(Tactic.simpLemma [] ["←"] `Nnreal.tsum_mul_right)] "]"]
         []
         ["using"
          (Term.proj
           (Term.app
            (Term.proj `Nnreal.summable_sigma "." (fieldIdx "1"))
            [(Term.app `p.change_origin_series_summable_aux₁ [`hr])])
           "."
           (fieldIdx "2"))])
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
       (Tactic.refine'
        "refine'"
        (Term.app
         `Ennreal.le_of_forall_pos_nnreal_lt
         [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`r `h0 `hr] [])] "=>" (Term.hole "_")))]))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `lt_tsub_iff_right) "," (Tactic.rwRule [] `add_commₓ)] "]")
        [(Tactic.location "at" (Tactic.locationHyp [`hr] []))])
       [])
      (group
       (Tactic.have''
        "have"
        [`hr' []]
        [(Term.typeSpec
          ":"
          («term_<_»
           (Term.paren
            "("
            [(Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" `x "∥₊")
             [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]]
            ")")
           "<"
           `p.radius))])
       [])
      (group (Tactic.exact "exact" (Term.app (Term.proj (Term.app `le_add_right [`le_rfl]) "." `trans_lt) [`hr])) [])
      (group (Tactic.apply "apply" `le_radius_of_summable_nnnorm) [])
      (group
       (Tactic.have''
        "have"
        []
        [(Term.typeSpec
          ":"
          (Term.forall
           "∀"
           [(Term.simpleBinder [`k] [(Term.typeSpec ":" (termℕ "ℕ"))])]
           ","
           («term_≤_»
            (Finset.Data.Finset.Fold.«term_*_»
             (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" (Term.app `p.change_origin [`x `k]) "∥₊")
             "*"
             («term_^_» `r "^" `k))
            "≤"
            (Finset.Data.Finset.Fold.«term_*_»
             (Topology.Algebra.InfiniteSum.«term∑'_,_»
              "∑'"
              (Lean.explicitBinders
               (Lean.unbracketedExplicitBinders
                [(Lean.binderIdent `s)]
                [":"
                 (Init.Data.Sigma.Basic.«termΣ_,_»
                  "Σ"
                  (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `l)] [":" (termℕ "ℕ")]))
                  ", "
                  («term{__:_//_}»
                   "{"
                   `s
                   [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
                   "//"
                   («term_=_» `s.card "=" `l)
                   "}"))]))
              ", "
              (Finset.Data.Finset.Fold.«term_*_»
               (Analysis.Normed.Group.Basic.«term∥_∥₊»
                "∥"
                (Term.app `p [(Init.Logic.«term_+_» `k "+" (Term.proj `s "." (fieldIdx "1")))])
                "∥₊")
               "*"
               («term_^_» (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" `x "∥₊") "^" (Term.proj `s "." (fieldIdx "1")))))
             "*"
             («term_^_» `r "^" `k)))))])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`k] [])]
          "=>"
          (Term.app `mul_le_mul_right' [(Term.app `p.nnnorm_change_origin_le [`k `hr']) («term_^_» `r "^" `k)]))))
       [])
      (group (Tactic.refine' "refine'" (Term.app `Nnreal.summable_of_le [`this (Term.hole "_")])) [])
      (group
       (Tactic.simpa
        "simpa"
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] ["←"] `Nnreal.tsum_mul_right)] "]"]
        []
        ["using"
         (Term.proj
          (Term.app
           (Term.proj `Nnreal.summable_sigma "." (fieldIdx "1"))
           [(Term.app `p.change_origin_series_summable_aux₁ [`hr])])
          "."
          (fieldIdx "2"))])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simpa
   "simpa"
   []
   ["only"]
   ["[" [(Tactic.simpLemma [] ["←"] `Nnreal.tsum_mul_right)] "]"]
   []
   ["using"
    (Term.proj
     (Term.app
      (Term.proj `Nnreal.summable_sigma "." (fieldIdx "1"))
      [(Term.app `p.change_origin_series_summable_aux₁ [`hr])])
     "."
     (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpa', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj
   (Term.app
    (Term.proj `Nnreal.summable_sigma "." (fieldIdx "1"))
    [(Term.app `p.change_origin_series_summable_aux₁ [`hr])])
   "."
   (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app
   (Term.proj `Nnreal.summable_sigma "." (fieldIdx "1"))
   [(Term.app `p.change_origin_series_summable_aux₁ [`hr])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `p.change_origin_series_summable_aux₁ [`hr])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p.change_origin_series_summable_aux₁
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `p.change_origin_series_summable_aux₁ [`hr]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `Nnreal.summable_sigma "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `Nnreal.summable_sigma
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   (Term.proj `Nnreal.summable_sigma "." (fieldIdx "1"))
   [(Term.paren "(" [(Term.app `p.change_origin_series_summable_aux₁ [`hr]) []] ")")])
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Nnreal.tsum_mul_right
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine' "refine'" (Term.app `Nnreal.summable_of_le [`this (Term.hole "_")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Nnreal.summable_of_le [`this (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Nnreal.summable_of_le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.exact
   "exact"
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`k] [])]
     "=>"
     (Term.app `mul_le_mul_right' [(Term.app `p.nnnorm_change_origin_le [`k `hr']) («term_^_» `r "^" `k)]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`k] [])]
    "=>"
    (Term.app `mul_le_mul_right' [(Term.app `p.nnnorm_change_origin_le [`k `hr']) («term_^_» `r "^" `k)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `mul_le_mul_right' [(Term.app `p.nnnorm_change_origin_le [`k `hr']) («term_^_» `r "^" `k)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_^_» `r "^" `k)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `r
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(«term_^_» `r "^" `k) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `p.nnnorm_change_origin_le [`k `hr'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hr'
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p.nnnorm_change_origin_le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `p.nnnorm_change_origin_le [`k `hr']) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mul_le_mul_right'
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
  (Tactic.have''
   "have"
   []
   [(Term.typeSpec
     ":"
     (Term.forall
      "∀"
      [(Term.simpleBinder [`k] [(Term.typeSpec ":" (termℕ "ℕ"))])]
      ","
      («term_≤_»
       (Finset.Data.Finset.Fold.«term_*_»
        (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" (Term.app `p.change_origin [`x `k]) "∥₊")
        "*"
        («term_^_» `r "^" `k))
       "≤"
       (Finset.Data.Finset.Fold.«term_*_»
        (Topology.Algebra.InfiniteSum.«term∑'_,_»
         "∑'"
         (Lean.explicitBinders
          (Lean.unbracketedExplicitBinders
           [(Lean.binderIdent `s)]
           [":"
            (Init.Data.Sigma.Basic.«termΣ_,_»
             "Σ"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `l)] [":" (termℕ "ℕ")]))
             ", "
             («term{__:_//_}»
              "{"
              `s
              [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
              "//"
              («term_=_» `s.card "=" `l)
              "}"))]))
         ", "
         (Finset.Data.Finset.Fold.«term_*_»
          (Analysis.Normed.Group.Basic.«term∥_∥₊»
           "∥"
           (Term.app `p [(Init.Logic.«term_+_» `k "+" (Term.proj `s "." (fieldIdx "1")))])
           "∥₊")
          "*"
          («term_^_» (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" `x "∥₊") "^" (Term.proj `s "." (fieldIdx "1")))))
        "*"
        («term_^_» `r "^" `k)))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.have''', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder [`k] [(Term.typeSpec ":" (termℕ "ℕ"))])]
   ","
   («term_≤_»
    (Finset.Data.Finset.Fold.«term_*_»
     (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" (Term.app `p.change_origin [`x `k]) "∥₊")
     "*"
     («term_^_» `r "^" `k))
    "≤"
    (Finset.Data.Finset.Fold.«term_*_»
     (Topology.Algebra.InfiniteSum.«term∑'_,_»
      "∑'"
      (Lean.explicitBinders
       (Lean.unbracketedExplicitBinders
        [(Lean.binderIdent `s)]
        [":"
         (Init.Data.Sigma.Basic.«termΣ_,_»
          "Σ"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `l)] [":" (termℕ "ℕ")]))
          ", "
          («term{__:_//_}»
           "{"
           `s
           [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
           "//"
           («term_=_» `s.card "=" `l)
           "}"))]))
      ", "
      (Finset.Data.Finset.Fold.«term_*_»
       (Analysis.Normed.Group.Basic.«term∥_∥₊»
        "∥"
        (Term.app `p [(Init.Logic.«term_+_» `k "+" (Term.proj `s "." (fieldIdx "1")))])
        "∥₊")
       "*"
       («term_^_» (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" `x "∥₊") "^" (Term.proj `s "." (fieldIdx "1")))))
     "*"
     («term_^_» `r "^" `k))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (Finset.Data.Finset.Fold.«term_*_»
    (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" (Term.app `p.change_origin [`x `k]) "∥₊")
    "*"
    («term_^_» `r "^" `k))
   "≤"
   (Finset.Data.Finset.Fold.«term_*_»
    (Topology.Algebra.InfiniteSum.«term∑'_,_»
     "∑'"
     (Lean.explicitBinders
      (Lean.unbracketedExplicitBinders
       [(Lean.binderIdent `s)]
       [":"
        (Init.Data.Sigma.Basic.«termΣ_,_»
         "Σ"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `l)] [":" (termℕ "ℕ")]))
         ", "
         («term{__:_//_}»
          "{"
          `s
          [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
          "//"
          («term_=_» `s.card "=" `l)
          "}"))]))
     ", "
     (Finset.Data.Finset.Fold.«term_*_»
      (Analysis.Normed.Group.Basic.«term∥_∥₊»
       "∥"
       (Term.app `p [(Init.Logic.«term_+_» `k "+" (Term.proj `s "." (fieldIdx "1")))])
       "∥₊")
      "*"
      («term_^_» (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" `x "∥₊") "^" (Term.proj `s "." (fieldIdx "1")))))
    "*"
    («term_^_» `r "^" `k)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   (Topology.Algebra.InfiniteSum.«term∑'_,_»
    "∑'"
    (Lean.explicitBinders
     (Lean.unbracketedExplicitBinders
      [(Lean.binderIdent `s)]
      [":"
       (Init.Data.Sigma.Basic.«termΣ_,_»
        "Σ"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `l)] [":" (termℕ "ℕ")]))
        ", "
        («term{__:_//_}»
         "{"
         `s
         [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
         "//"
         («term_=_» `s.card "=" `l)
         "}"))]))
    ", "
    (Finset.Data.Finset.Fold.«term_*_»
     (Analysis.Normed.Group.Basic.«term∥_∥₊»
      "∥"
      (Term.app `p [(Init.Logic.«term_+_» `k "+" (Term.proj `s "." (fieldIdx "1")))])
      "∥₊")
     "*"
     («term_^_» (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" `x "∥₊") "^" (Term.proj `s "." (fieldIdx "1")))))
   "*"
   («term_^_» `r "^" `k))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_^_» `r "^" `k)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `r
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Topology.Algebra.InfiniteSum.«term∑'_,_»
   "∑'"
   (Lean.explicitBinders
    (Lean.unbracketedExplicitBinders
     [(Lean.binderIdent `s)]
     [":"
      (Init.Data.Sigma.Basic.«termΣ_,_»
       "Σ"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `l)] [":" (termℕ "ℕ")]))
       ", "
       («term{__:_//_}»
        "{"
        `s
        [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
        "//"
        («term_=_» `s.card "=" `l)
        "}"))]))
   ", "
   (Finset.Data.Finset.Fold.«term_*_»
    (Analysis.Normed.Group.Basic.«term∥_∥₊»
     "∥"
     (Term.app `p [(Init.Logic.«term_+_» `k "+" (Term.proj `s "." (fieldIdx "1")))])
     "∥₊")
    "*"
    («term_^_» (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" `x "∥₊") "^" (Term.proj `s "." (fieldIdx "1")))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Algebra.InfiniteSum.«term∑'_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   (Analysis.Normed.Group.Basic.«term∥_∥₊»
    "∥"
    (Term.app `p [(Init.Logic.«term_+_» `k "+" (Term.proj `s "." (fieldIdx "1")))])
    "∥₊")
   "*"
   («term_^_» (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" `x "∥₊") "^" (Term.proj `s "." (fieldIdx "1"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_^_» (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" `x "∥₊") "^" (Term.proj `s "." (fieldIdx "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `s "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" `x "∥₊")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥₊»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Analysis.Normed.Group.Basic.«term∥_∥₊»
   "∥"
   (Term.app `p [(Init.Logic.«term_+_» `k "+" (Term.proj `s "." (fieldIdx "1")))])
   "∥₊")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥₊»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `p [(Init.Logic.«term_+_» `k "+" (Term.proj `s "." (fieldIdx "1")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `k "+" (Term.proj `s "." (fieldIdx "1")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `s "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Init.Logic.«term_+_» `k "+" (Term.proj `s "." (fieldIdx "1"))) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
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
/--
    The radius of convergence of `p.change_origin x` is at least `p.radius - ∥x∥`. In other words,
    `p.change_origin x` is well defined on the largest ball contained in the original ball of
    convergence.-/
  theorem
    change_origin_radius
    : p.radius - ∥ x ∥₊ ≤ p.change_origin x . radius
    :=
      by
        refine' Ennreal.le_of_forall_pos_nnreal_lt fun r h0 hr => _
          rw [ lt_tsub_iff_right , add_commₓ ] at hr
          have hr' : ( ∥ x ∥₊ : ℝ≥0∞ ) < p.radius
          exact le_add_right le_rfl . trans_lt hr
          apply le_radius_of_summable_nnnorm
          have
            :
              ∀
                k : ℕ
                ,
                ∥ p.change_origin x k ∥₊ * r ^ k
                  ≤
                  ∑' s : Σ l : ℕ , { s : Finset Finₓ k + l // s.card = l } , ∥ p k + s . 1 ∥₊ * ∥ x ∥₊ ^ s . 1 * r ^ k
          exact fun k => mul_le_mul_right' p.nnnorm_change_origin_le k hr' r ^ k
          refine' Nnreal.summable_of_le this _
          simpa
            only
            [ ← Nnreal.tsum_mul_right ]
            using Nnreal.summable_sigma . 1 p.change_origin_series_summable_aux₁ hr . 2

end

variable [CompleteSpace F] (p : FormalMultilinearSeries 𝕜 E F) {x y : E} {r R : ℝ≥0 }

theorem has_fpower_series_on_ball_change_origin (k : ℕ) (hr : 0 < p.radius) :
    HasFpowerSeriesOnBall (fun x => p.change_origin x k) (p.change_origin_series k) 0 p.radius :=
  have := p.le_change_origin_series_radius k
  ((p.change_origin_series k).HasFpowerSeriesOnBall (hr.trans_le this)).mono hr this

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment "/--" " Summing the series `p.change_origin x` at a point `y` gives back `p (x + y)`-/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `change_origin_eval [])
  (Command.declSig
   [(Term.explicitBinder
     "("
     [`h]
     [":"
      («term_<_»
       (Term.paren
        "("
        [(Init.Logic.«term_+_»
          (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" `x "∥₊")
          "+"
          (Analysis.Normed.Group.Basic.«term∥_∥₊» "∥" `y "∥₊"))
         [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]]
        ")")
       "<"
       `p.radius)]
     []
     ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app (Term.proj (Term.app `p.change_origin [`x]) "." `Sum) [`y])
     "="
     (Term.app `p.sum [(Init.Logic.«term_+_» `x "+" `y)]))))
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
           [`radius_pos []]
           [(Term.typeSpec ":" («term_<_» (numLit "0") "<" `p.radius))]
           ":="
           (Term.app `lt_of_le_of_ltₓ [(Term.app `zero_le [(Term.hole "_")]) `h]))))
        [])
       (group
        (Tactic.have''
         "have"
         [`x_mem_ball []]
         [(Term.typeSpec
           ":"
           (Init.Core.«term_∈_»
            `x
            " ∈ "
            (Term.app `Emetric.Ball [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `E)]] ")") `p.radius])))])
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.app
          (Term.proj `mem_emetric_ball_zero_iff "." (fieldIdx "2"))
          [(Term.app (Term.proj (Term.app `le_add_right [`le_rfl]) "." `trans_lt) [`h])]))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`y_mem_ball []]
           [(Term.typeSpec
             ":"
             (Init.Core.«term_∈_»
              `y
              " ∈ "
              (Term.app
               `Emetric.Ball
               [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `E)]] ")")
                (Term.proj (Term.app `p.change_origin [`x]) "." `radius)])))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.refine'
                 "refine'"
                 (Term.app
                  (Term.proj `mem_emetric_ball_zero_iff "." (fieldIdx "2"))
                  [(Term.app `lt_of_lt_of_leₓ [(Term.hole "_") `p.change_origin_radius])]))
                [])
               (group
                (tacticRwa__
                 "rwa"
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `lt_tsub_iff_right) "," (Tactic.rwRule [] `add_commₓ)] "]")
                 [])
                [])]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`x_add_y_mem_ball []]
           [(Term.typeSpec
             ":"
             (Init.Core.«term_∈_»
              (Init.Logic.«term_+_» `x "+" `y)
              " ∈ "
              (Term.app `Emetric.Ball [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `E)]] ")") `p.radius])))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.refine'
                 "refine'"
                 (Term.app
                  (Term.proj `mem_emetric_ball_zero_iff "." (fieldIdx "2"))
                  [(Term.app `lt_of_le_of_ltₓ [(Term.hole "_") `h])]))
                [])
               (group (Tactic.exactModCast "exact_mod_cast" (Term.app `nnnorm_add_le [`x `y])) [])]))))))
        [])
       (group
        (Tactic.set
         "set"
         `f
         [":"
          (Term.arrow
           (Init.Data.Sigma.Basic.«termΣ_,_»
            "Σ"
            (Lean.explicitBinders
             (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k) (Lean.binderIdent `l)] [":" (termℕ "ℕ")]))
            ", "
            («term{__:_//_}»
             "{"
             `s
             [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
             "//"
             («term_=_» `s.card "=" `l)
             "}"))
           "→"
           `F)]
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`s] [])]
           "=>"
           (Term.app
            `p.change_origin_series_term
            [(Term.proj `s "." (fieldIdx "1"))
             (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "1"))
             (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "2"))
             (Term.proj (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "2")) "." (fieldIdx "2"))
             (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `x))
             (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `y))])))
         [])
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hsf []]
           [(Term.typeSpec ":" (Term.app `Summable [`f]))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.refine'
                 "refine'"
                 (Term.app
                  `summable_of_nnnorm_bounded
                  [(Term.hole "_") (Term.app `p.change_origin_series_summable_aux₁ [`h]) (Term.hole "_")]))
                [])
               (group
                (Tactic.rintro
                 "rintro"
                 [(Tactic.rintroPat.one
                   (Tactic.rcasesPat.tuple
                    "⟨"
                    [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `k)]) [])
                     ","
                     (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `l)]) [])
                     ","
                     (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `s)]) [])
                     ","
                     (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hs)]) [])]
                    "⟩"))]
                 [])
                [])
               (group (Tactic.dsimp "dsimp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `Subtype.coe_mk)] "]"] [] []) [])
               (group
                (Tactic.exact
                 "exact"
                 (Term.app
                  `p.nnnorm_change_origin_series_term_apply_le
                  [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                [])]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hf []]
           [(Term.typeSpec
             ":"
             (Term.app `HasSum [`f (Term.app (Term.proj (Term.app `p.change_origin [`x]) "." `Sum) [`y])]))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.refine'
                 "refine'"
                 (Term.app
                  `HasSum.sigma_of_has_sum
                  [(Term.proj
                    (Term.app (Term.proj (Term.app `p.change_origin [`x]) "." `Summable) [`y_mem_ball])
                    "."
                    `HasSum)
                   (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k] [])] "=>" (Term.hole "_")))
                   `hsf]))
                [])
               (group
                (Tactic.«tactic·._»
                 "·"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group (Tactic.dsimp "dsimp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `f)] "]"] [] []) [])
                    (group
                     (Tactic.refine'
                      "refine'"
                      (Term.app `ContinuousMultilinearMap.has_sum_eval [(Term.hole "_") (Term.hole "_")]))
                     [])
                    (group
                     (Tactic.tacticHave_
                      "have"
                      (Term.haveDecl
                       (Term.haveIdDecl
                        []
                        []
                        ":="
                        (Term.app
                         (Term.proj (Term.app `p.has_fpower_series_on_ball_change_origin [`k `radius_pos]) "." `HasSum)
                         [`x_mem_ball]))))
                     [])
                    (group
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `zero_addₓ)] "]")
                      [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
                     [])
                    (group
                     (Tactic.refine'
                      "refine'"
                      (Term.app
                       `HasSum.sigma_of_has_sum
                       [`this
                        (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`l] [])] "=>" (Term.hole "_")))
                        (Term.hole "_")]))
                     [])
                    (group
                     (Tactic.«tactic·._»
                      "·"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(group
                          (Tactic.simp
                           "simp"
                           []
                           ["only"]
                           ["["
                            [(Tactic.simpLemma [] [] `change_origin_series)
                             ","
                             (Tactic.simpLemma [] [] `ContinuousMultilinearMap.sum_apply)]
                            "]"]
                           [])
                          [])
                         (group (Tactic.apply "apply" `has_sum_fintype) [])])))
                     [])
                    (group
                     (Tactic.«tactic·._»
                      "·"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(group
                          (Tactic.refine'
                           "refine'"
                           (Term.app
                            `summable_of_nnnorm_bounded
                            [(Term.hole "_")
                             (Term.app
                              `p.change_origin_series_summable_aux₂
                              [(Term.app (Term.proj `mem_emetric_ball_zero_iff "." (fieldIdx "1")) [`x_mem_ball]) `k])
                             (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`s] [])] "=>" (Term.hole "_")))]))
                          [])
                         (group
                          (Tactic.refine'
                           "refine'"
                           (Term.app
                            (Term.proj
                             (Term.app `ContinuousMultilinearMap.le_op_nnnorm [(Term.hole "_") (Term.hole "_")])
                             "."
                             `trans_eq)
                            [(Term.hole "_")]))
                          [])
                         (group (Tactic.simp "simp" [] [] [] []) [])])))
                     [])])))
                [])]))))))
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.app
          `hf.unique
          [(Term.app (Term.proj `change_origin_index_equiv.symm.has_sum_iff "." (fieldIdx "1")) [(Term.hole "_")])]))
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.app
          `HasSum.sigma_of_has_sum
          [(Term.app `p.has_sum [`x_add_y_mem_ball])
           (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.hole "_")))
           (Term.app (Term.proj `change_origin_index_equiv.symm.summable_iff "." (fieldIdx "2")) [`hsf])]))
        [])
       (group
        (Tactic.tacticErw__
         "erw"
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            []
            (Term.app
             (Term.proj (Term.app `p [`n]) "." `map_add_univ)
             [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `x))
              (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `y))]))]
          "]")
         [])
        [])
       (group (Tactic.convert "convert" [] (Term.app `has_sum_fintype [(Term.hole "_")]) []) [])
       (group (Tactic.ext1 "ext1" [(Tactic.rcasesPat.one `s)]) [])
       (group
        (Tactic.dsimp
         "dsimp"
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `f)
           ","
           (Tactic.simpLemma [] [] `change_origin_series_term)
           ","
           (Tactic.simpLemma [] [] (Rel.Data.Rel.«term_∘_» (Term.cdot "·") " ∘ " (Term.cdot "·")))
           ","
           (Tactic.simpLemma [] [] `change_origin_index_equiv_symm_apply_fst)
           ","
           (Tactic.simpLemma [] [] `change_origin_index_equiv_symm_apply_snd_fst)
           ","
           (Tactic.simpLemma [] [] `change_origin_index_equiv_symm_apply_snd_snd_coe)]
          "]"]
         []
         [])
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ContinuousMultilinearMap.curry_fin_finset_apply_const)] "]")
         [])
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`m] []) (Term.simpleBinder [`hm] [(Term.typeSpec ":" («term_=_» `n "=" `m))])]
              ","
              («term_=_»
               (Term.app
                `p
                [`n
                 (Term.app
                  `s.piecewise
                  [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `x))
                   (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `y))])])
               "="
               (Term.app
                `p
                [`m
                 (Term.app
                  (Term.proj
                   (Term.app `s.map [(Term.proj (Term.proj (Term.app `Finₓ.cast [`hm]) "." `toEquiv) "." `toEmbedding)])
                   "."
                   `piecewise)
                  [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `x))
                   (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `y))])]))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.rintro
                 "rintro"
                 [(Tactic.rintroPat.one (Tactic.rcasesPat.one `m)) (Tactic.rintroPat.one (Tactic.rcasesPat.one `rfl))]
                 [])
                [])
               (group (Tactic.simp "simp" [] [] [] []) [])
               (group (Tactic.congr "congr" [] []) [])]))))))
        [])
       (group (Tactic.apply "apply" `this) [])])))
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
          [`radius_pos []]
          [(Term.typeSpec ":" («term_<_» (numLit "0") "<" `p.radius))]
          ":="
          (Term.app `lt_of_le_of_ltₓ [(Term.app `zero_le [(Term.hole "_")]) `h]))))
       [])
      (group
       (Tactic.have''
        "have"
        [`x_mem_ball []]
        [(Term.typeSpec
          ":"
          (Init.Core.«term_∈_»
           `x
           " ∈ "
           (Term.app `Emetric.Ball [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `E)]] ")") `p.radius])))])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.app
         (Term.proj `mem_emetric_ball_zero_iff "." (fieldIdx "2"))
         [(Term.app (Term.proj (Term.app `le_add_right [`le_rfl]) "." `trans_lt) [`h])]))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`y_mem_ball []]
          [(Term.typeSpec
            ":"
            (Init.Core.«term_∈_»
             `y
             " ∈ "
             (Term.app
              `Emetric.Ball
              [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `E)]] ")")
               (Term.proj (Term.app `p.change_origin [`x]) "." `radius)])))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.refine'
                "refine'"
                (Term.app
                 (Term.proj `mem_emetric_ball_zero_iff "." (fieldIdx "2"))
                 [(Term.app `lt_of_lt_of_leₓ [(Term.hole "_") `p.change_origin_radius])]))
               [])
              (group
               (tacticRwa__
                "rwa"
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `lt_tsub_iff_right) "," (Tactic.rwRule [] `add_commₓ)] "]")
                [])
               [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`x_add_y_mem_ball []]
          [(Term.typeSpec
            ":"
            (Init.Core.«term_∈_»
             (Init.Logic.«term_+_» `x "+" `y)
             " ∈ "
             (Term.app `Emetric.Ball [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" `E)]] ")") `p.radius])))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.refine'
                "refine'"
                (Term.app
                 (Term.proj `mem_emetric_ball_zero_iff "." (fieldIdx "2"))
                 [(Term.app `lt_of_le_of_ltₓ [(Term.hole "_") `h])]))
               [])
              (group (Tactic.exactModCast "exact_mod_cast" (Term.app `nnnorm_add_le [`x `y])) [])]))))))
       [])
      (group
       (Tactic.set
        "set"
        `f
        [":"
         (Term.arrow
          (Init.Data.Sigma.Basic.«termΣ_,_»
           "Σ"
           (Lean.explicitBinders
            (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k) (Lean.binderIdent `l)] [":" (termℕ "ℕ")]))
           ", "
           («term{__:_//_}»
            "{"
            `s
            [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
            "//"
            («term_=_» `s.card "=" `l)
            "}"))
          "→"
          `F)]
        ":="
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`s] [])]
          "=>"
          (Term.app
           `p.change_origin_series_term
           [(Term.proj `s "." (fieldIdx "1"))
            (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "1"))
            (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "2"))
            (Term.proj (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "2")) "." (fieldIdx "2"))
            (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `x))
            (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `y))])))
        [])
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hsf []]
          [(Term.typeSpec ":" (Term.app `Summable [`f]))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.refine'
                "refine'"
                (Term.app
                 `summable_of_nnnorm_bounded
                 [(Term.hole "_") (Term.app `p.change_origin_series_summable_aux₁ [`h]) (Term.hole "_")]))
               [])
              (group
               (Tactic.rintro
                "rintro"
                [(Tactic.rintroPat.one
                  (Tactic.rcasesPat.tuple
                   "⟨"
                   [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `k)]) [])
                    ","
                    (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `l)]) [])
                    ","
                    (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `s)]) [])
                    ","
                    (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hs)]) [])]
                   "⟩"))]
                [])
               [])
              (group (Tactic.dsimp "dsimp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `Subtype.coe_mk)] "]"] [] []) [])
              (group
               (Tactic.exact
                "exact"
                (Term.app
                 `p.nnnorm_change_origin_series_term_apply_le
                 [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")]))
               [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hf []]
          [(Term.typeSpec
            ":"
            (Term.app `HasSum [`f (Term.app (Term.proj (Term.app `p.change_origin [`x]) "." `Sum) [`y])]))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.refine'
                "refine'"
                (Term.app
                 `HasSum.sigma_of_has_sum
                 [(Term.proj
                   (Term.app (Term.proj (Term.app `p.change_origin [`x]) "." `Summable) [`y_mem_ball])
                   "."
                   `HasSum)
                  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k] [])] "=>" (Term.hole "_")))
                  `hsf]))
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.dsimp "dsimp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `f)] "]"] [] []) [])
                   (group
                    (Tactic.refine'
                     "refine'"
                     (Term.app `ContinuousMultilinearMap.has_sum_eval [(Term.hole "_") (Term.hole "_")]))
                    [])
                   (group
                    (Tactic.tacticHave_
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       []
                       []
                       ":="
                       (Term.app
                        (Term.proj (Term.app `p.has_fpower_series_on_ball_change_origin [`k `radius_pos]) "." `HasSum)
                        [`x_mem_ball]))))
                    [])
                   (group
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `zero_addₓ)] "]")
                     [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
                    [])
                   (group
                    (Tactic.refine'
                     "refine'"
                     (Term.app
                      `HasSum.sigma_of_has_sum
                      [`this
                       (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`l] [])] "=>" (Term.hole "_")))
                       (Term.hole "_")]))
                    [])
                   (group
                    (Tactic.«tactic·._»
                     "·"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group
                         (Tactic.simp
                          "simp"
                          []
                          ["only"]
                          ["["
                           [(Tactic.simpLemma [] [] `change_origin_series)
                            ","
                            (Tactic.simpLemma [] [] `ContinuousMultilinearMap.sum_apply)]
                           "]"]
                          [])
                         [])
                        (group (Tactic.apply "apply" `has_sum_fintype) [])])))
                    [])
                   (group
                    (Tactic.«tactic·._»
                     "·"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group
                         (Tactic.refine'
                          "refine'"
                          (Term.app
                           `summable_of_nnnorm_bounded
                           [(Term.hole "_")
                            (Term.app
                             `p.change_origin_series_summable_aux₂
                             [(Term.app (Term.proj `mem_emetric_ball_zero_iff "." (fieldIdx "1")) [`x_mem_ball]) `k])
                            (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`s] [])] "=>" (Term.hole "_")))]))
                         [])
                        (group
                         (Tactic.refine'
                          "refine'"
                          (Term.app
                           (Term.proj
                            (Term.app `ContinuousMultilinearMap.le_op_nnnorm [(Term.hole "_") (Term.hole "_")])
                            "."
                            `trans_eq)
                           [(Term.hole "_")]))
                         [])
                        (group (Tactic.simp "simp" [] [] [] []) [])])))
                    [])])))
               [])]))))))
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         `hf.unique
         [(Term.app (Term.proj `change_origin_index_equiv.symm.has_sum_iff "." (fieldIdx "1")) [(Term.hole "_")])]))
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         `HasSum.sigma_of_has_sum
         [(Term.app `p.has_sum [`x_add_y_mem_ball])
          (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.hole "_")))
          (Term.app (Term.proj `change_origin_index_equiv.symm.summable_iff "." (fieldIdx "2")) [`hsf])]))
       [])
      (group
       (Tactic.tacticErw__
        "erw"
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule
           []
           (Term.app
            (Term.proj (Term.app `p [`n]) "." `map_add_univ)
            [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `x))
             (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `y))]))]
         "]")
        [])
       [])
      (group (Tactic.convert "convert" [] (Term.app `has_sum_fintype [(Term.hole "_")]) []) [])
      (group (Tactic.ext1 "ext1" [(Tactic.rcasesPat.one `s)]) [])
      (group
       (Tactic.dsimp
        "dsimp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `f)
          ","
          (Tactic.simpLemma [] [] `change_origin_series_term)
          ","
          (Tactic.simpLemma [] [] (Rel.Data.Rel.«term_∘_» (Term.cdot "·") " ∘ " (Term.cdot "·")))
          ","
          (Tactic.simpLemma [] [] `change_origin_index_equiv_symm_apply_fst)
          ","
          (Tactic.simpLemma [] [] `change_origin_index_equiv_symm_apply_snd_fst)
          ","
          (Tactic.simpLemma [] [] `change_origin_index_equiv_symm_apply_snd_snd_coe)]
         "]"]
        []
        [])
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ContinuousMultilinearMap.curry_fin_finset_apply_const)] "]")
        [])
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`m] []) (Term.simpleBinder [`hm] [(Term.typeSpec ":" («term_=_» `n "=" `m))])]
             ","
             («term_=_»
              (Term.app
               `p
               [`n
                (Term.app
                 `s.piecewise
                 [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `x))
                  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `y))])])
              "="
              (Term.app
               `p
               [`m
                (Term.app
                 (Term.proj
                  (Term.app `s.map [(Term.proj (Term.proj (Term.app `Finₓ.cast [`hm]) "." `toEquiv) "." `toEmbedding)])
                  "."
                  `piecewise)
                 [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `x))
                  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `y))])]))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rintro
                "rintro"
                [(Tactic.rintroPat.one (Tactic.rcasesPat.one `m)) (Tactic.rintroPat.one (Tactic.rcasesPat.one `rfl))]
                [])
               [])
              (group (Tactic.simp "simp" [] [] [] []) [])
              (group (Tactic.congr "congr" [] []) [])]))))))
       [])
      (group (Tactic.apply "apply" `this) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.apply "apply" `this)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     []
     [(Term.typeSpec
       ":"
       (Term.forall
        "∀"
        [(Term.simpleBinder [`m] []) (Term.simpleBinder [`hm] [(Term.typeSpec ":" («term_=_» `n "=" `m))])]
        ","
        («term_=_»
         (Term.app
          `p
          [`n
           (Term.app
            `s.piecewise
            [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `x))
             (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `y))])])
         "="
         (Term.app
          `p
          [`m
           (Term.app
            (Term.proj
             (Term.app `s.map [(Term.proj (Term.proj (Term.app `Finₓ.cast [`hm]) "." `toEquiv) "." `toEmbedding)])
             "."
             `piecewise)
            [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `x))
             (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `y))])]))))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.rintro
           "rintro"
           [(Tactic.rintroPat.one (Tactic.rcasesPat.one `m)) (Tactic.rintroPat.one (Tactic.rcasesPat.one `rfl))]
           [])
          [])
         (group (Tactic.simp "simp" [] [] [] []) [])
         (group (Tactic.congr "congr" [] []) [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rintro
        "rintro"
        [(Tactic.rintroPat.one (Tactic.rcasesPat.one `m)) (Tactic.rintroPat.one (Tactic.rcasesPat.one `rfl))]
        [])
       [])
      (group (Tactic.simp "simp" [] [] [] []) [])
      (group (Tactic.congr "congr" [] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.congr "congr" [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.congr', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp "simp" [] [] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rintro
   "rintro"
   [(Tactic.rintroPat.one (Tactic.rcasesPat.one `m)) (Tactic.rintroPat.one (Tactic.rcasesPat.one `rfl))]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder [`m] []) (Term.simpleBinder [`hm] [(Term.typeSpec ":" («term_=_» `n "=" `m))])]
   ","
   («term_=_»
    (Term.app
     `p
     [`n
      (Term.app
       `s.piecewise
       [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `x))
        (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `y))])])
    "="
    (Term.app
     `p
     [`m
      (Term.app
       (Term.proj
        (Term.app `s.map [(Term.proj (Term.proj (Term.app `Finₓ.cast [`hm]) "." `toEquiv) "." `toEmbedding)])
        "."
        `piecewise)
       [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `x))
        (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `y))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.app
    `p
    [`n
     (Term.app
      `s.piecewise
      [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `x))
       (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `y))])])
   "="
   (Term.app
    `p
    [`m
     (Term.app
      (Term.proj
       (Term.app `s.map [(Term.proj (Term.proj (Term.app `Finₓ.cast [`hm]) "." `toEquiv) "." `toEmbedding)])
       "."
       `piecewise)
      [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `x))
       (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `y))])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `p
   [`m
    (Term.app
     (Term.proj
      (Term.app `s.map [(Term.proj (Term.proj (Term.app `Finₓ.cast [`hm]) "." `toEquiv) "." `toEmbedding)])
      "."
      `piecewise)
     [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `x))
      (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `y))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj
    (Term.app `s.map [(Term.proj (Term.proj (Term.app `Finₓ.cast [`hm]) "." `toEquiv) "." `toEmbedding)])
    "."
    `piecewise)
   [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `x))
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `y))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `y))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `x))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `x)) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj
   (Term.app `s.map [(Term.proj (Term.proj (Term.app `Finₓ.cast [`hm]) "." `toEquiv) "." `toEmbedding)])
   "."
   `piecewise)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `s.map [(Term.proj (Term.proj (Term.app `Finₓ.cast [`hm]) "." `toEquiv) "." `toEmbedding)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.proj (Term.app `Finₓ.cast [`hm]) "." `toEquiv) "." `toEmbedding)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj (Term.app `Finₓ.cast [`hm]) "." `toEquiv)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `Finₓ.cast [`hm])
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
  `Finₓ.cast
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Finₓ.cast [`hm]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `s.map
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `s.map
   [(Term.proj (Term.proj (Term.paren "(" [(Term.app `Finₓ.cast [`hm]) []] ")") "." `toEquiv) "." `toEmbedding)])
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   (Term.proj
    (Term.paren
     "("
     [(Term.app
       `s.map
       [(Term.proj (Term.proj (Term.paren "(" [(Term.app `Finₓ.cast [`hm]) []] ")") "." `toEquiv) "." `toEmbedding)])
      []]
     ")")
    "."
    `piecewise)
   [(Term.paren "(" [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `x)) []] ")")
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `y))])
  []]
 ")")
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
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app
   `p
   [`n
    (Term.app
     `s.piecewise
     [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `x))
      (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `y))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `s.piecewise
   [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `x))
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `y))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `y))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `x))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `x)) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `s.piecewise
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `s.piecewise
   [(Term.paren "(" [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `x)) []] ")")
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `y))])
  []]
 ")")
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
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» `n "=" `m)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ContinuousMultilinearMap.curry_fin_finset_apply_const)] "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ContinuousMultilinearMap.curry_fin_finset_apply_const
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.dsimp
   "dsimp"
   []
   ["only"]
   ["["
    [(Tactic.simpLemma [] [] `f)
     ","
     (Tactic.simpLemma [] [] `change_origin_series_term)
     ","
     (Tactic.simpLemma [] [] (Rel.Data.Rel.«term_∘_» (Term.cdot "·") " ∘ " (Term.cdot "·")))
     ","
     (Tactic.simpLemma [] [] `change_origin_index_equiv_symm_apply_fst)
     ","
     (Tactic.simpLemma [] [] `change_origin_index_equiv_symm_apply_snd_fst)
     ","
     (Tactic.simpLemma [] [] `change_origin_index_equiv_symm_apply_snd_snd_coe)]
    "]"]
   []
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.dsimp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `change_origin_index_equiv_symm_apply_snd_snd_coe
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `change_origin_index_equiv_symm_apply_snd_fst
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `change_origin_index_equiv_symm_apply_fst
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Rel.Data.Rel.«term_∘_» (Term.cdot "·") " ∘ " (Term.cdot "·"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Rel.Data.Rel.«term_∘_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.cdot "·")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.cdot', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.cdot', expected 'Lean.Parser.Term.cdot.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  (Term.cdot "·")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.cdot', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.cdot', expected 'Lean.Parser.Term.cdot.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1024, (none, [anonymous]) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `change_origin_series_term
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.ext1 "ext1" [(Tactic.rcasesPat.one `s)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.ext1', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.convert "convert" [] (Term.app `has_sum_fintype [(Term.hole "_")]) [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.convert', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `has_sum_fintype [(Term.hole "_")])
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
  `has_sum_fintype
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticErw__
   "erw"
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule
      []
      (Term.app
       (Term.proj (Term.app `p [`n]) "." `map_add_univ)
       [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `x))
        (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `y))]))]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticErw__', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj (Term.app `p [`n]) "." `map_add_univ)
   [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `x))
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `y))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `y))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `x))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `x)) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.app `p [`n]) "." `map_add_univ)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `p [`n])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `p [`n]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    `HasSum.sigma_of_has_sum
    [(Term.app `p.has_sum [`x_add_y_mem_ball])
     (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.hole "_")))
     (Term.app (Term.proj `change_origin_index_equiv.symm.summable_iff "." (fieldIdx "2")) [`hsf])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `HasSum.sigma_of_has_sum
   [(Term.app `p.has_sum [`x_add_y_mem_ball])
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.hole "_")))
    (Term.app (Term.proj `change_origin_index_equiv.symm.summable_iff "." (fieldIdx "2")) [`hsf])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj `change_origin_index_equiv.symm.summable_iff "." (fieldIdx "2")) [`hsf])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hsf
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `change_origin_index_equiv.symm.summable_iff "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `change_origin_index_equiv.symm.summable_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app (Term.proj `change_origin_index_equiv.symm.summable_iff "." (fieldIdx "2")) [`hsf]) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.hole "_"))) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `p.has_sum [`x_add_y_mem_ball])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x_add_y_mem_ball
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p.has_sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `p.has_sum [`x_add_y_mem_ball]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `HasSum.sigma_of_has_sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    `hf.unique
    [(Term.app (Term.proj `change_origin_index_equiv.symm.has_sum_iff "." (fieldIdx "1")) [(Term.hole "_")])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `hf.unique
   [(Term.app (Term.proj `change_origin_index_equiv.symm.has_sum_iff "." (fieldIdx "1")) [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj `change_origin_index_equiv.symm.has_sum_iff "." (fieldIdx "1")) [(Term.hole "_")])
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
  (Term.proj `change_origin_index_equiv.symm.has_sum_iff "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `change_origin_index_equiv.symm.has_sum_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app (Term.proj `change_origin_index_equiv.symm.has_sum_iff "." (fieldIdx "1")) [(Term.hole "_")]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hf.unique
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`hf []]
     [(Term.typeSpec ":" (Term.app `HasSum [`f (Term.app (Term.proj (Term.app `p.change_origin [`x]) "." `Sum) [`y])]))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.refine'
           "refine'"
           (Term.app
            `HasSum.sigma_of_has_sum
            [(Term.proj (Term.app (Term.proj (Term.app `p.change_origin [`x]) "." `Summable) [`y_mem_ball]) "." `HasSum)
             (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k] [])] "=>" (Term.hole "_")))
             `hsf]))
          [])
         (group
          (Tactic.«tactic·._»
           "·"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.dsimp "dsimp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `f)] "]"] [] []) [])
              (group
               (Tactic.refine'
                "refine'"
                (Term.app `ContinuousMultilinearMap.has_sum_eval [(Term.hole "_") (Term.hole "_")]))
               [])
              (group
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  []
                  []
                  ":="
                  (Term.app
                   (Term.proj (Term.app `p.has_fpower_series_on_ball_change_origin [`k `radius_pos]) "." `HasSum)
                   [`x_mem_ball]))))
               [])
              (group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `zero_addₓ)] "]")
                [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
               [])
              (group
               (Tactic.refine'
                "refine'"
                (Term.app
                 `HasSum.sigma_of_has_sum
                 [`this
                  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`l] [])] "=>" (Term.hole "_")))
                  (Term.hole "_")]))
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.simp
                     "simp"
                     []
                     ["only"]
                     ["["
                      [(Tactic.simpLemma [] [] `change_origin_series)
                       ","
                       (Tactic.simpLemma [] [] `ContinuousMultilinearMap.sum_apply)]
                      "]"]
                     [])
                    [])
                   (group (Tactic.apply "apply" `has_sum_fintype) [])])))
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.refine'
                     "refine'"
                     (Term.app
                      `summable_of_nnnorm_bounded
                      [(Term.hole "_")
                       (Term.app
                        `p.change_origin_series_summable_aux₂
                        [(Term.app (Term.proj `mem_emetric_ball_zero_iff "." (fieldIdx "1")) [`x_mem_ball]) `k])
                       (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`s] [])] "=>" (Term.hole "_")))]))
                    [])
                   (group
                    (Tactic.refine'
                     "refine'"
                     (Term.app
                      (Term.proj
                       (Term.app `ContinuousMultilinearMap.le_op_nnnorm [(Term.hole "_") (Term.hole "_")])
                       "."
                       `trans_eq)
                      [(Term.hole "_")]))
                    [])
                   (group (Tactic.simp "simp" [] [] [] []) [])])))
               [])])))
          [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.refine'
        "refine'"
        (Term.app
         `HasSum.sigma_of_has_sum
         [(Term.proj (Term.app (Term.proj (Term.app `p.change_origin [`x]) "." `Summable) [`y_mem_ball]) "." `HasSum)
          (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k] [])] "=>" (Term.hole "_")))
          `hsf]))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.dsimp "dsimp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `f)] "]"] [] []) [])
           (group
            (Tactic.refine'
             "refine'"
             (Term.app `ContinuousMultilinearMap.has_sum_eval [(Term.hole "_") (Term.hole "_")]))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               []
               ":="
               (Term.app
                (Term.proj (Term.app `p.has_fpower_series_on_ball_change_origin [`k `radius_pos]) "." `HasSum)
                [`x_mem_ball]))))
            [])
           (group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `zero_addₓ)] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
            [])
           (group
            (Tactic.refine'
             "refine'"
             (Term.app
              `HasSum.sigma_of_has_sum
              [`this
               (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`l] [])] "=>" (Term.hole "_")))
               (Term.hole "_")]))
            [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.simp
                  "simp"
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `change_origin_series)
                    ","
                    (Tactic.simpLemma [] [] `ContinuousMultilinearMap.sum_apply)]
                   "]"]
                  [])
                 [])
                (group (Tactic.apply "apply" `has_sum_fintype) [])])))
            [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.refine'
                  "refine'"
                  (Term.app
                   `summable_of_nnnorm_bounded
                   [(Term.hole "_")
                    (Term.app
                     `p.change_origin_series_summable_aux₂
                     [(Term.app (Term.proj `mem_emetric_ball_zero_iff "." (fieldIdx "1")) [`x_mem_ball]) `k])
                    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`s] [])] "=>" (Term.hole "_")))]))
                 [])
                (group
                 (Tactic.refine'
                  "refine'"
                  (Term.app
                   (Term.proj
                    (Term.app `ContinuousMultilinearMap.le_op_nnnorm [(Term.hole "_") (Term.hole "_")])
                    "."
                    `trans_eq)
                   [(Term.hole "_")]))
                 [])
                (group (Tactic.simp "simp" [] [] [] []) [])])))
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
     [(group (Tactic.dsimp "dsimp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `f)] "]"] [] []) [])
      (group
       (Tactic.refine' "refine'" (Term.app `ContinuousMultilinearMap.has_sum_eval [(Term.hole "_") (Term.hole "_")]))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          []
          ":="
          (Term.app
           (Term.proj (Term.app `p.has_fpower_series_on_ball_change_origin [`k `radius_pos]) "." `HasSum)
           [`x_mem_ball]))))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `zero_addₓ)] "]")
        [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         `HasSum.sigma_of_has_sum
         [`this (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`l] [])] "=>" (Term.hole "_"))) (Term.hole "_")]))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `change_origin_series)
               ","
               (Tactic.simpLemma [] [] `ContinuousMultilinearMap.sum_apply)]
              "]"]
             [])
            [])
           (group (Tactic.apply "apply" `has_sum_fintype) [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.refine'
             "refine'"
             (Term.app
              `summable_of_nnnorm_bounded
              [(Term.hole "_")
               (Term.app
                `p.change_origin_series_summable_aux₂
                [(Term.app (Term.proj `mem_emetric_ball_zero_iff "." (fieldIdx "1")) [`x_mem_ball]) `k])
               (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`s] [])] "=>" (Term.hole "_")))]))
            [])
           (group
            (Tactic.refine'
             "refine'"
             (Term.app
              (Term.proj
               (Term.app `ContinuousMultilinearMap.le_op_nnnorm [(Term.hole "_") (Term.hole "_")])
               "."
               `trans_eq)
              [(Term.hole "_")]))
            [])
           (group (Tactic.simp "simp" [] [] [] []) [])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
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
       (Tactic.refine'
        "refine'"
        (Term.app
         `summable_of_nnnorm_bounded
         [(Term.hole "_")
          (Term.app
           `p.change_origin_series_summable_aux₂
           [(Term.app (Term.proj `mem_emetric_ball_zero_iff "." (fieldIdx "1")) [`x_mem_ball]) `k])
          (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`s] [])] "=>" (Term.hole "_")))]))
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         (Term.proj (Term.app `ContinuousMultilinearMap.le_op_nnnorm [(Term.hole "_") (Term.hole "_")]) "." `trans_eq)
         [(Term.hole "_")]))
       [])
      (group (Tactic.simp "simp" [] [] [] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
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
  (Tactic.refine'
   "refine'"
   (Term.app
    (Term.proj (Term.app `ContinuousMultilinearMap.le_op_nnnorm [(Term.hole "_") (Term.hole "_")]) "." `trans_eq)
    [(Term.hole "_")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj (Term.app `ContinuousMultilinearMap.le_op_nnnorm [(Term.hole "_") (Term.hole "_")]) "." `trans_eq)
   [(Term.hole "_")])
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
  (Term.proj (Term.app `ContinuousMultilinearMap.le_op_nnnorm [(Term.hole "_") (Term.hole "_")]) "." `trans_eq)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `ContinuousMultilinearMap.le_op_nnnorm [(Term.hole "_") (Term.hole "_")])
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
  `ContinuousMultilinearMap.le_op_nnnorm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `ContinuousMultilinearMap.le_op_nnnorm [(Term.hole "_") (Term.hole "_")]) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    `summable_of_nnnorm_bounded
    [(Term.hole "_")
     (Term.app
      `p.change_origin_series_summable_aux₂
      [(Term.app (Term.proj `mem_emetric_ball_zero_iff "." (fieldIdx "1")) [`x_mem_ball]) `k])
     (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`s] [])] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `summable_of_nnnorm_bounded
   [(Term.hole "_")
    (Term.app
     `p.change_origin_series_summable_aux₂
     [(Term.app (Term.proj `mem_emetric_ball_zero_iff "." (fieldIdx "1")) [`x_mem_ball]) `k])
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`s] [])] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`s] [])] "=>" (Term.hole "_")))
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.app
   `p.change_origin_series_summable_aux₂
   [(Term.app (Term.proj `mem_emetric_ball_zero_iff "." (fieldIdx "1")) [`x_mem_ball]) `k])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app (Term.proj `mem_emetric_ball_zero_iff "." (fieldIdx "1")) [`x_mem_ball])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x_mem_ball
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `mem_emetric_ball_zero_iff "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `mem_emetric_ball_zero_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app (Term.proj `mem_emetric_ball_zero_iff "." (fieldIdx "1")) [`x_mem_ball]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p.change_origin_series_summable_aux₂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `p.change_origin_series_summable_aux₂
   [(Term.paren "(" [(Term.app (Term.proj `mem_emetric_ball_zero_iff "." (fieldIdx "1")) [`x_mem_ball]) []] ")") `k])
  []]
 ")")
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
  `summable_of_nnnorm_bounded
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `change_origin_series)
          ","
          (Tactic.simpLemma [] [] `ContinuousMultilinearMap.sum_apply)]
         "]"]
        [])
       [])
      (group (Tactic.apply "apply" `has_sum_fintype) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.apply "apply" `has_sum_fintype)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `has_sum_fintype
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["["
    [(Tactic.simpLemma [] [] `change_origin_series) "," (Tactic.simpLemma [] [] `ContinuousMultilinearMap.sum_apply)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ContinuousMultilinearMap.sum_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `change_origin_series
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    `HasSum.sigma_of_has_sum
    [`this (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`l] [])] "=>" (Term.hole "_"))) (Term.hole "_")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `HasSum.sigma_of_has_sum
   [`this (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`l] [])] "=>" (Term.hole "_"))) (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`l] [])] "=>" (Term.hole "_")))
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`l] [])] "=>" (Term.hole "_"))) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `HasSum.sigma_of_has_sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `zero_addₓ)] "]")
   [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.location', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `zero_addₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     []
     []
     ":="
     (Term.app
      (Term.proj (Term.app `p.has_fpower_series_on_ball_change_origin [`k `radius_pos]) "." `HasSum)
      [`x_mem_ball]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj (Term.app `p.has_fpower_series_on_ball_change_origin [`k `radius_pos]) "." `HasSum)
   [`x_mem_ball])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x_mem_ball
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.app `p.has_fpower_series_on_ball_change_origin [`k `radius_pos]) "." `HasSum)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `p.has_fpower_series_on_ball_change_origin [`k `radius_pos])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `radius_pos
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p.has_fpower_series_on_ball_change_origin
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `p.has_fpower_series_on_ball_change_origin [`k `radius_pos]) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine' "refine'" (Term.app `ContinuousMultilinearMap.has_sum_eval [(Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `ContinuousMultilinearMap.has_sum_eval [(Term.hole "_") (Term.hole "_")])
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
  `ContinuousMultilinearMap.has_sum_eval
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.dsimp "dsimp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `f)] "]"] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.dsimp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    `HasSum.sigma_of_has_sum
    [(Term.proj (Term.app (Term.proj (Term.app `p.change_origin [`x]) "." `Summable) [`y_mem_ball]) "." `HasSum)
     (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k] [])] "=>" (Term.hole "_")))
     `hsf]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `HasSum.sigma_of_has_sum
   [(Term.proj (Term.app (Term.proj (Term.app `p.change_origin [`x]) "." `Summable) [`y_mem_ball]) "." `HasSum)
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k] [])] "=>" (Term.hole "_")))
    `hsf])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hsf
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k] [])] "=>" (Term.hole "_")))
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k] [])] "=>" (Term.hole "_"))) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj (Term.app (Term.proj (Term.app `p.change_origin [`x]) "." `Summable) [`y_mem_ball]) "." `HasSum)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app (Term.proj (Term.app `p.change_origin [`x]) "." `Summable) [`y_mem_ball])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `y_mem_ball
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.app `p.change_origin [`x]) "." `Summable)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `p.change_origin [`x])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p.change_origin
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `p.change_origin [`x]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app (Term.proj (Term.paren "(" [(Term.app `p.change_origin [`x]) []] ")") "." `Summable) [`y_mem_ball]) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `HasSum.sigma_of_has_sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `HasSum [`f (Term.app (Term.proj (Term.app `p.change_origin [`x]) "." `Sum) [`y])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj (Term.app `p.change_origin [`x]) "." `Sum) [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.app `p.change_origin [`x]) "." `Sum)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `p.change_origin [`x])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p.change_origin
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `p.change_origin [`x]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app (Term.proj (Term.paren "(" [(Term.app `p.change_origin [`x]) []] ")") "." `Sum) [`y]) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `HasSum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`hsf []]
     [(Term.typeSpec ":" (Term.app `Summable [`f]))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.refine'
           "refine'"
           (Term.app
            `summable_of_nnnorm_bounded
            [(Term.hole "_") (Term.app `p.change_origin_series_summable_aux₁ [`h]) (Term.hole "_")]))
          [])
         (group
          (Tactic.rintro
           "rintro"
           [(Tactic.rintroPat.one
             (Tactic.rcasesPat.tuple
              "⟨"
              [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `k)]) [])
               ","
               (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `l)]) [])
               ","
               (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `s)]) [])
               ","
               (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hs)]) [])]
              "⟩"))]
           [])
          [])
         (group (Tactic.dsimp "dsimp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `Subtype.coe_mk)] "]"] [] []) [])
         (group
          (Tactic.exact
           "exact"
           (Term.app
            `p.nnnorm_change_origin_series_term_apply_le
            [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")]))
          [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.refine'
        "refine'"
        (Term.app
         `summable_of_nnnorm_bounded
         [(Term.hole "_") (Term.app `p.change_origin_series_summable_aux₁ [`h]) (Term.hole "_")]))
       [])
      (group
       (Tactic.rintro
        "rintro"
        [(Tactic.rintroPat.one
          (Tactic.rcasesPat.tuple
           "⟨"
           [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `k)]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `l)]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `s)]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hs)]) [])]
           "⟩"))]
        [])
       [])
      (group (Tactic.dsimp "dsimp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `Subtype.coe_mk)] "]"] [] []) [])
      (group
       (Tactic.exact
        "exact"
        (Term.app
         `p.nnnorm_change_origin_series_term_apply_le
         [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")]))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.app
    `p.nnnorm_change_origin_series_term_apply_le
    [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `p.nnnorm_change_origin_series_term_apply_le
   [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
  `p.nnnorm_change_origin_series_term_apply_le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.dsimp "dsimp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `Subtype.coe_mk)] "]"] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.dsimp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Subtype.coe_mk
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rintro
   "rintro"
   [(Tactic.rintroPat.one
     (Tactic.rcasesPat.tuple
      "⟨"
      [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `k)]) [])
       ","
       (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `l)]) [])
       ","
       (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `s)]) [])
       ","
       (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hs)]) [])]
      "⟩"))]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    `summable_of_nnnorm_bounded
    [(Term.hole "_") (Term.app `p.change_origin_series_summable_aux₁ [`h]) (Term.hole "_")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `summable_of_nnnorm_bounded
   [(Term.hole "_") (Term.app `p.change_origin_series_summable_aux₁ [`h]) (Term.hole "_")])
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
  (Term.app `p.change_origin_series_summable_aux₁ [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p.change_origin_series_summable_aux₁
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `p.change_origin_series_summable_aux₁ [`h]) []]
 ")")
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
  `summable_of_nnnorm_bounded
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Summable [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Summable
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.set
   "set"
   `f
   [":"
    (Term.arrow
     (Init.Data.Sigma.Basic.«termΣ_,_»
      "Σ"
      (Lean.explicitBinders
       (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k) (Lean.binderIdent `l)] [":" (termℕ "ℕ")]))
      ", "
      («term{__:_//_}»
       "{"
       `s
       [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
       "//"
       («term_=_» `s.card "=" `l)
       "}"))
     "→"
     `F)]
   ":="
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`s] [])]
     "=>"
     (Term.app
      `p.change_origin_series_term
      [(Term.proj `s "." (fieldIdx "1"))
       (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "1"))
       (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "2"))
       (Term.proj (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "2")) "." (fieldIdx "2"))
       (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `x))
       (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `y))])))
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.set', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`s] [])]
    "=>"
    (Term.app
     `p.change_origin_series_term
     [(Term.proj `s "." (fieldIdx "1"))
      (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "1"))
      (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "2"))
      (Term.proj (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "2")) "." (fieldIdx "2"))
      (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `x))
      (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `y))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `p.change_origin_series_term
   [(Term.proj `s "." (fieldIdx "1"))
    (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "1"))
    (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "2"))
    (Term.proj (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "2")) "." (fieldIdx "2"))
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `x))
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `y))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `y))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `x))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `x)) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "2")) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `s "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `s "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj (Term.proj `s "." (fieldIdx "2")) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `s "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `s "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p.change_origin_series_term
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.arrow', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.arrow
   (Init.Data.Sigma.Basic.«termΣ_,_»
    "Σ"
    (Lean.explicitBinders
     (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k) (Lean.binderIdent `l)] [":" (termℕ "ℕ")]))
    ", "
    («term{__:_//_}»
     "{"
     `s
     [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
     "//"
     («term_=_» `s.card "=" `l)
     "}"))
   "→"
   `F)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.arrow', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `F
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
  (Init.Data.Sigma.Basic.«termΣ_,_»
   "Σ"
   (Lean.explicitBinders
    (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k) (Lean.binderIdent `l)] [":" (termℕ "ℕ")]))
   ", "
   («term{__:_//_}»
    "{"
    `s
    [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
    "//"
    («term_=_» `s.card "=" `l)
    "}"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Data.Sigma.Basic.«termΣ_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term{__:_//_}»
   "{"
   `s
   [":" (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])]
   "//"
   («term_=_» `s.card "=" `l)
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term{__:_//_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» `s.card "=" `l)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `l
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `s.card
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Finset [(Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Finₓ [(Init.Logic.«term_+_» `k "+" `l)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `k "+" `l)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `l
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `k "+" `l) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `Finₓ [(Term.paren "(" [(Init.Logic.«term_+_» `k "+" `l) []] ")")]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finset
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
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
/-- Summing the series `p.change_origin x` at a point `y` gives back `p (x + y)`-/
  theorem
    change_origin_eval
    ( h : ( ∥ x ∥₊ + ∥ y ∥₊ : ℝ≥0∞ ) < p.radius ) : p.change_origin x . Sum y = p.sum x + y
    :=
      by
        have radius_pos : 0 < p.radius := lt_of_le_of_ltₓ zero_le _ h
          have x_mem_ball : x ∈ Emetric.Ball ( 0 : E ) p.radius
          exact mem_emetric_ball_zero_iff . 2 le_add_right le_rfl . trans_lt h
          have
            y_mem_ball
              : y ∈ Emetric.Ball ( 0 : E ) p.change_origin x . radius
              :=
              by
                refine' mem_emetric_ball_zero_iff . 2 lt_of_lt_of_leₓ _ p.change_origin_radius
                  rwa [ lt_tsub_iff_right , add_commₓ ]
          have
            x_add_y_mem_ball
              : x + y ∈ Emetric.Ball ( 0 : E ) p.radius
              :=
              by refine' mem_emetric_ball_zero_iff . 2 lt_of_le_of_ltₓ _ h exact_mod_cast nnnorm_add_le x y
          set
            f
            : Σ k l : ℕ , { s : Finset Finₓ k + l // s.card = l } → F
            :=
            fun s => p.change_origin_series_term s . 1 s . 2 . 1 s . 2 . 2 s . 2 . 2 . 2 fun _ => x fun _ => y
          have
            hsf
              : Summable f
              :=
              by
                refine' summable_of_nnnorm_bounded _ p.change_origin_series_summable_aux₁ h _
                  rintro ⟨ k , l , s , hs ⟩
                  dsimp only [ Subtype.coe_mk ]
                  exact p.nnnorm_change_origin_series_term_apply_le _ _ _ _ _ _
          have
            hf
              : HasSum f p.change_origin x . Sum y
              :=
              by
                refine' HasSum.sigma_of_has_sum p.change_origin x . Summable y_mem_ball . HasSum fun k => _ hsf
                  ·
                    dsimp only [ f ]
                      refine' ContinuousMultilinearMap.has_sum_eval _ _
                      have := p.has_fpower_series_on_ball_change_origin k radius_pos . HasSum x_mem_ball
                      rw [ zero_addₓ ] at this
                      refine' HasSum.sigma_of_has_sum this fun l => _ _
                      · simp only [ change_origin_series , ContinuousMultilinearMap.sum_apply ] apply has_sum_fintype
                      ·
                        refine'
                            summable_of_nnnorm_bounded
                              _
                                p.change_origin_series_summable_aux₂ mem_emetric_ball_zero_iff . 1 x_mem_ball k
                                fun s => _
                          refine' ContinuousMultilinearMap.le_op_nnnorm _ _ . trans_eq _
                          simp
          refine' hf.unique change_origin_index_equiv.symm.has_sum_iff . 1 _
          refine'
            HasSum.sigma_of_has_sum
              p.has_sum x_add_y_mem_ball fun n => _ change_origin_index_equiv.symm.summable_iff . 2 hsf
          erw [ p n . map_add_univ fun _ => x fun _ => y ]
          convert has_sum_fintype _
          ext1 s
          dsimp
            only
            [
              f
                ,
                change_origin_series_term
                ,
                · ∘ ·
                ,
                change_origin_index_equiv_symm_apply_fst
                ,
                change_origin_index_equiv_symm_apply_snd_fst
                ,
                change_origin_index_equiv_symm_apply_snd_snd_coe
              ]
          rw [ ContinuousMultilinearMap.curry_fin_finset_apply_const ]
          have
            :
                ∀
                  m hm : n = m
                  ,
                  p n s.piecewise fun _ => x fun _ => y
                    =
                    p m s.map Finₓ.cast hm . toEquiv . toEmbedding . piecewise fun _ => x fun _ => y
              :=
              by rintro m rfl simp congr
          apply this

end FormalMultilinearSeries

section

variable [CompleteSpace F] {f : E → F} {p : FormalMultilinearSeries 𝕜 E F} {x y : E} {r : ℝ≥0∞}

/--  If a function admits a power series expansion `p` on a ball `B (x, r)`, then it also admits a
power series on any subball of this ball (even with a different center), given by `p.change_origin`.
-/
theorem HasFpowerSeriesOnBall.change_origin (hf : HasFpowerSeriesOnBall f p x r) (h : (∥y∥₊ : ℝ≥0∞) < r) :
    HasFpowerSeriesOnBall f (p.change_origin y) (x+y) (r - ∥y∥₊) :=
  { r_le := by
      apply le_transₓ _ p.change_origin_radius
      exact tsub_le_tsub hf.r_le (le_reflₓ _),
    r_pos := by
      simp [h],
    HasSum := fun z hz => by
      convert (p.change_origin y).HasSum _
      ·
        rw [mem_emetric_ball_zero_iff, lt_tsub_iff_right, add_commₓ] at hz
        rw [p.change_origin_eval (hz.trans_le hf.r_le), add_assocₓ, hf.sum]
        refine' mem_emetric_ball_zero_iff.2 (lt_of_le_of_ltₓ _ hz)
        exact_mod_cast nnnorm_add_le y z
      ·
        refine' Emetric.ball_subset_ball (le_transₓ _ p.change_origin_radius) hz
        exact tsub_le_tsub hf.r_le le_rfl }

/--  If a function admits a power series expansion `p` on an open ball `B (x, r)`, then
it is analytic at every point of this ball. -/
theorem HasFpowerSeriesOnBall.analytic_at_of_mem (hf : HasFpowerSeriesOnBall f p x r) (h : y ∈ Emetric.Ball x r) :
    AnalyticAt 𝕜 f y := by
  have : (∥y - x∥₊ : ℝ≥0∞) < r := by
    simpa [edist_eq_coe_nnnorm_sub] using h
  have := hf.change_origin this
  rw [add_sub_cancel'_right] at this
  exact this.analytic_at

variable (𝕜 f)

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " For any function `f` from a normed vector space to a Banach space, the set of points `x` such\nthat `f` is analytic at `x` is open. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `is_open_analytic_at [])
  (Command.declSig
   []
   (Term.typeSpec ":" (Term.app `IsOpen [(Set.«term{_|_}» "{" `x "|" (Term.app `AnalyticAt [`𝕜 `f `x]) "}")])))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `is_open_iff_mem_nhds)] "]") []) [])
       (group
        (Tactic.rintro
         "rintro"
         [(Tactic.rintroPat.one (Tactic.rcasesPat.one `x))
          (Tactic.rintroPat.one
           (Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `p)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `r)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hr)]) [])]
            "⟩"))]
         [])
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.app
          `mem_of_superset
          [(Term.app `Emetric.ball_mem_nhds [(Term.hole "_") `hr.r_pos])
           (Term.fun
            "fun"
            (Term.basicFun [(Term.simpleBinder [`y `hy] [])] "=>" (Term.app `hr.analytic_at_of_mem [`hy])))]))
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
     [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `is_open_iff_mem_nhds)] "]") []) [])
      (group
       (Tactic.rintro
        "rintro"
        [(Tactic.rintroPat.one (Tactic.rcasesPat.one `x))
         (Tactic.rintroPat.one
          (Tactic.rcasesPat.tuple
           "⟨"
           [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `p)]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `r)]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hr)]) [])]
           "⟩"))]
        [])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.app
         `mem_of_superset
         [(Term.app `Emetric.ball_mem_nhds [(Term.hole "_") `hr.r_pos])
          (Term.fun
           "fun"
           (Term.basicFun [(Term.simpleBinder [`y `hy] [])] "=>" (Term.app `hr.analytic_at_of_mem [`hy])))]))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.app
    `mem_of_superset
    [(Term.app `Emetric.ball_mem_nhds [(Term.hole "_") `hr.r_pos])
     (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`y `hy] [])] "=>" (Term.app `hr.analytic_at_of_mem [`hy])))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `mem_of_superset
   [(Term.app `Emetric.ball_mem_nhds [(Term.hole "_") `hr.r_pos])
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`y `hy] [])] "=>" (Term.app `hr.analytic_at_of_mem [`hy])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`y `hy] [])] "=>" (Term.app `hr.analytic_at_of_mem [`hy])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `hr.analytic_at_of_mem [`hy])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hy
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hr.analytic_at_of_mem
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.app `Emetric.ball_mem_nhds [(Term.hole "_") `hr.r_pos])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hr.r_pos
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
  `Emetric.ball_mem_nhds
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `Emetric.ball_mem_nhds [(Term.hole "_") `hr.r_pos]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mem_of_superset
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rintro
   "rintro"
   [(Tactic.rintroPat.one (Tactic.rcasesPat.one `x))
    (Tactic.rintroPat.one
     (Tactic.rcasesPat.tuple
      "⟨"
      [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `p)]) [])
       ","
       (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `r)]) [])
       ","
       (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hr)]) [])]
      "⟩"))]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rintroPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `is_open_iff_mem_nhds)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `is_open_iff_mem_nhds
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.app `IsOpen [(Set.«term{_|_}» "{" `x "|" (Term.app `AnalyticAt [`𝕜 `f `x]) "}")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.«term{_|_}» "{" `x "|" (Term.app `AnalyticAt [`𝕜 `f `x]) "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `AnalyticAt [`𝕜 `f `x])
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
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `𝕜
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `AnalyticAt
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Mathlib.ExtendedBinder.extBinder'
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
    For any function `f` from a normed vector space to a Banach space, the set of points `x` such
    that `f` is analytic at `x` is open. -/
  theorem
    is_open_analytic_at
    : IsOpen { x | AnalyticAt 𝕜 f x }
    :=
      by
        rw [ is_open_iff_mem_nhds ]
          rintro x ⟨ p , r , hr ⟩
          exact mem_of_superset Emetric.ball_mem_nhds _ hr.r_pos fun y hy => hr.analytic_at_of_mem hy

end

