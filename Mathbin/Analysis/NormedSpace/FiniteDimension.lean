import Mathbin.Analysis.NormedSpace.AffineIsometry
import Mathbin.Analysis.NormedSpace.OperatorNorm
import Mathbin.Analysis.Asymptotics.AsymptoticEquivalent
import Mathbin.LinearAlgebra.Matrix.ToLin

/-!
# Finite dimensional normed spaces over complete fields

Over a complete nondiscrete field, in finite dimension, all norms are equivalent and all linear maps
are continuous. Moreover, a finite-dimensional subspace is always complete and closed.

## Main results:

* `linear_map.continuous_of_finite_dimensional` : a linear map on a finite-dimensional space over a
  complete field is continuous.
* `finite_dimensional.complete` : a finite-dimensional space over a complete field is complete. This
  is not registered as an instance, as the field would be an unknown metavariable in typeclass
  resolution.
* `submodule.closed_of_finite_dimensional` : a finite-dimensional subspace over a complete field is
  closed
* `finite_dimensional.proper` : a finite-dimensional space over a proper field is proper. This
  is not registered as an instance, as the field would be an unknown metavariable in typeclass
  resolution. It is however registered as an instance for `𝕜 = ℝ` and `𝕜 = ℂ`. As properness
  implies completeness, there is no need to also register `finite_dimensional.complete` on `ℝ` or
  `ℂ`.
* `finite_dimensional_of_is_compact_closed_ball`: Riesz' theorem: if the closed unit ball is
  compact, then the space is finite-dimensional.

## Implementation notes

The fact that all norms are equivalent is not written explicitly, as it would mean having two norms
on a single space, which is not the way type classes work. However, if one has a
finite-dimensional vector space `E` with a norm, and a copy `E'` of this type with another norm,
then the identities from `E` to `E'` and from `E'`to `E` are continuous thanks to
`linear_map.continuous_of_finite_dimensional`. This gives the desired norm equivalence.
-/


universe u v w x

noncomputable section

open Set FiniteDimensional TopologicalSpace Filter Asymptotics

open_locale Classical BigOperators Filter TopologicalSpace Asymptotics

namespace LinearIsometry

open LinearMap

variable {R : Type _} [Semiringₓ R]

variable {F E₁ : Type _} [SemiNormedGroup F] [NormedGroup E₁] [Module R E₁]

variable {R₁ : Type _} [Field R₁] [Module R₁ E₁] [Module R₁ F] [FiniteDimensional R₁ E₁] [FiniteDimensional R₁ F]

/--  A linear isometry between finite dimensional spaces of equal dimension can be upgraded
    to a linear isometry equivalence. -/
def to_linear_isometry_equiv (li : E₁ →ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁ F) : E₁ ≃ₗᵢ[R₁] F :=
  { toLinearEquiv := li.to_linear_map.linear_equiv_of_injective li.injective h, norm_map' := li.norm_map' }

@[simp]
theorem coe_to_linear_isometry_equiv (li : E₁ →ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁ F) :
    (li.to_linear_isometry_equiv h : E₁ → F) = li :=
  rfl

@[simp]
theorem to_linear_isometry_equiv_apply (li : E₁ →ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁ F) (x : E₁) :
    (li.to_linear_isometry_equiv h) x = li x :=
  rfl

end LinearIsometry

namespace AffineIsometry

open AffineMap

variable {𝕜 : Type _} {V₁ V₂ : Type _} {P₁ P₂ : Type _} [NormedField 𝕜] [NormedGroup V₁] [SemiNormedGroup V₂]
  [NormedSpace 𝕜 V₁] [SemiNormedSpace 𝕜 V₂] [MetricSpace P₁] [PseudoMetricSpace P₂] [NormedAddTorsor V₁ P₁]
  [SemiNormedAddTorsor V₂ P₂]

variable [FiniteDimensional 𝕜 V₁] [FiniteDimensional 𝕜 V₂]

/--  An affine isometry between finite dimensional spaces of equal dimension can be upgraded
    to an affine isometry equivalence. -/
def to_affine_isometry_equiv [Inhabited P₁] (li : P₁ →ᵃⁱ[𝕜] P₂) (h : finrank 𝕜 V₁ = finrank 𝕜 V₂) : P₁ ≃ᵃⁱ[𝕜] P₂ :=
  AffineIsometryEquiv.mk' li (li.linear_isometry.to_linear_isometry_equiv h) (arbitraryₓ P₁) fun p => by
    simp

@[simp]
theorem coe_to_affine_isometry_equiv [Inhabited P₁] (li : P₁ →ᵃⁱ[𝕜] P₂) (h : finrank 𝕜 V₁ = finrank 𝕜 V₂) :
    (li.to_affine_isometry_equiv h : P₁ → P₂) = li :=
  rfl

@[simp]
theorem to_affine_isometry_equiv_apply [Inhabited P₁] (li : P₁ →ᵃⁱ[𝕜] P₂) (h : finrank 𝕜 V₁ = finrank 𝕜 V₂) (x : P₁) :
    (li.to_affine_isometry_equiv h) x = li x :=
  rfl

end AffineIsometry

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment "/--" " A linear map on `ι → 𝕜` (where `ι` is a fintype) is continuous -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `LinearMap.continuous_on_pi [])
  (Command.declSig
   [(Term.implicitBinder "{" [`ι] [":" (Term.type "Type" [`w])] "}")
    (Term.instBinder "[" [] (Term.app `Fintype [`ι]) "]")
    (Term.implicitBinder "{" [`𝕜] [":" (Term.type "Type" [`u])] "}")
    (Term.instBinder "[" [] (Term.app `NormedField [`𝕜]) "]")
    (Term.implicitBinder "{" [`E] [":" (Term.type "Type" [`v])] "}")
    (Term.instBinder "[" [] (Term.app `AddCommGroupₓ [`E]) "]")
    (Term.instBinder "[" [] (Term.app `Module [`𝕜 `E]) "]")
    (Term.instBinder "[" [] (Term.app `TopologicalSpace [`E]) "]")
    (Term.instBinder "[" [] (Term.app `TopologicalAddGroup [`E]) "]")
    (Term.instBinder "[" [] (Term.app `HasContinuousSmul [`𝕜 `E]) "]")
    (Term.explicitBinder
     "("
     [`f]
     [":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» (Term.arrow `ι "→" `𝕜) " →ₗ[" `𝕜 "] " `E)]
     []
     ")")]
   (Term.typeSpec ":" (Term.app `Continuous [`f])))
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
           []
           [(Term.typeSpec
             ":"
             («term_=_»
              (Term.paren "(" [`f [(Term.typeAscription ":" (Term.arrow (Term.arrow `ι "→" `𝕜) "→" `E))]] ")")
              "="
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`x] [])]
                "=>"
                (Algebra.BigOperators.Basic.«term∑_,_»
                 "∑"
                 (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" `ι]))
                 ", "
                 (Algebra.Group.Defs.«term_•_»
                  (Term.app `x [`i])
                  " • "
                  (Term.app
                   `f
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.simpleBinder [`j] [])]
                      "=>"
                      (termIfThenElse "if" («term_=_» `i "=" `j) "then" (numLit "1") "else" (numLit "0"))))])))))))]
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
                   [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x)] []) [])
                    (group (Tactic.exact "exact" (Term.app `f.pi_apply_eq_sum_univ [`x])) [])])))
                [])]))))))
        [])
       (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") []) [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.app
          `continuous_finset_sum
          [(Term.hole "_") (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i `hi] [])] "=>" (Term.hole "_")))]))
        [])
       (group
        (Tactic.exact "exact" (Term.app (Term.proj (Term.app `continuous_apply [`i]) "." `smul) [`continuous_const]))
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
          []
          [(Term.typeSpec
            ":"
            («term_=_»
             (Term.paren "(" [`f [(Term.typeAscription ":" (Term.arrow (Term.arrow `ι "→" `𝕜) "→" `E))]] ")")
             "="
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`x] [])]
               "=>"
               (Algebra.BigOperators.Basic.«term∑_,_»
                "∑"
                (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" `ι]))
                ", "
                (Algebra.Group.Defs.«term_•_»
                 (Term.app `x [`i])
                 " • "
                 (Term.app
                  `f
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [`j] [])]
                     "=>"
                     (termIfThenElse "if" («term_=_» `i "=" `j) "then" (numLit "1") "else" (numLit "0"))))])))))))]
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
                  [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x)] []) [])
                   (group (Tactic.exact "exact" (Term.app `f.pi_apply_eq_sum_univ [`x])) [])])))
               [])]))))))
       [])
      (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") []) [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         `continuous_finset_sum
         [(Term.hole "_") (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i `hi] [])] "=>" (Term.hole "_")))]))
       [])
      (group
       (Tactic.exact "exact" (Term.app (Term.proj (Term.app `continuous_apply [`i]) "." `smul) [`continuous_const]))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app (Term.proj (Term.app `continuous_apply [`i]) "." `smul) [`continuous_const]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj (Term.app `continuous_apply [`i]) "." `smul) [`continuous_const])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `continuous_const
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.app `continuous_apply [`i]) "." `smul)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `continuous_apply [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `continuous_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `continuous_apply [`i]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    `continuous_finset_sum
    [(Term.hole "_") (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i `hi] [])] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `continuous_finset_sum
   [(Term.hole "_") (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i `hi] [])] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i `hi] [])] "=>" (Term.hole "_")))
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
  `continuous_finset_sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
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
       («term_=_»
        (Term.paren "(" [`f [(Term.typeAscription ":" (Term.arrow (Term.arrow `ι "→" `𝕜) "→" `E))]] ")")
        "="
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`x] [])]
          "=>"
          (Algebra.BigOperators.Basic.«term∑_,_»
           "∑"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" `ι]))
           ", "
           (Algebra.Group.Defs.«term_•_»
            (Term.app `x [`i])
            " • "
            (Term.app
             `f
             [(Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`j] [])]
                "=>"
                (termIfThenElse "if" («term_=_» `i "=" `j) "then" (numLit "1") "else" (numLit "0"))))])))))))]
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
             [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x)] []) [])
              (group (Tactic.exact "exact" (Term.app `f.pi_apply_eq_sum_univ [`x])) [])])))
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
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x)] []) [])
           (group (Tactic.exact "exact" (Term.app `f.pi_apply_eq_sum_univ [`x])) [])])))
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
     [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x)] []) [])
      (group (Tactic.exact "exact" (Term.app `f.pi_apply_eq_sum_univ [`x])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `f.pi_apply_eq_sum_univ [`x]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f.pi_apply_eq_sum_univ [`x])
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
  `f.pi_apply_eq_sum_univ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.ext "ext" [(Tactic.rcasesPat.one `x)] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.ext', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.paren "(" [`f [(Term.typeAscription ":" (Term.arrow (Term.arrow `ι "→" `𝕜) "→" `E))]] ")")
   "="
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`x] [])]
     "=>"
     (Algebra.BigOperators.Basic.«term∑_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" `ι]))
      ", "
      (Algebra.Group.Defs.«term_•_»
       (Term.app `x [`i])
       " • "
       (Term.app
        `f
        [(Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`j] [])]
           "=>"
           (termIfThenElse "if" («term_=_» `i "=" `j) "then" (numLit "1") "else" (numLit "0"))))]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`x] [])]
    "=>"
    (Algebra.BigOperators.Basic.«term∑_,_»
     "∑"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" `ι]))
     ", "
     (Algebra.Group.Defs.«term_•_»
      (Term.app `x [`i])
      " • "
      (Term.app
       `f
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`j] [])]
          "=>"
          (termIfThenElse "if" («term_=_» `i "=" `j) "then" (numLit "1") "else" (numLit "0"))))])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" `ι]))
   ", "
   (Algebra.Group.Defs.«term_•_»
    (Term.app `x [`i])
    " • "
    (Term.app
     `f
     [(Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`j] [])]
        "=>"
        (termIfThenElse "if" («term_=_» `i "=" `j) "then" (numLit "1") "else" (numLit "0"))))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.Group.Defs.«term_•_»
   (Term.app `x [`i])
   " • "
   (Term.app
    `f
    [(Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`j] [])]
       "=>"
       (termIfThenElse "if" («term_=_» `i "=" `j) "then" (numLit "1") "else" (numLit "0"))))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `f
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`j] [])]
      "=>"
      (termIfThenElse "if" («term_=_» `i "=" `j) "then" (numLit "1") "else" (numLit "0"))))])
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
    [(Term.simpleBinder [`j] [])]
    "=>"
    (termIfThenElse "if" («term_=_» `i "=" `j) "then" (numLit "1") "else" (numLit "0"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (termIfThenElse "if" («term_=_» `i "=" `j) "then" (numLit "1") "else" (numLit "0"))
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
  («term_=_» `i "=" `j)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
  (Term.app `x [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1022, (some 1023, term) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
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
/-- A linear map on `ι → 𝕜` (where `ι` is a fintype) is continuous -/
  theorem
    LinearMap.continuous_on_pi
    { ι : Type w }
        [ Fintype ι ]
        { 𝕜 : Type u }
        [ NormedField 𝕜 ]
        { E : Type v }
        [ AddCommGroupₓ E ]
        [ Module 𝕜 E ]
        [ TopologicalSpace E ]
        [ TopologicalAddGroup E ]
        [ HasContinuousSmul 𝕜 E ]
        ( f : ι → 𝕜 →ₗ[ 𝕜 ] E )
      : Continuous f
    :=
      by
        have
            : ( f : ι → 𝕜 → E ) = fun x => ∑ i : ι , x i • f fun j => if i = j then 1 else 0
              :=
              by · ext x exact f.pi_apply_eq_sum_univ x
          rw [ this ]
          refine' continuous_finset_sum _ fun i hi => _
          exact continuous_apply i . smul continuous_const

/--  The space of continuous linear maps between finite-dimensional spaces is finite-dimensional. -/
instance {𝕜 E F : Type _} [Field 𝕜] [TopologicalSpace 𝕜] [TopologicalSpace E] [AddCommGroupₓ E] [Module 𝕜 E]
    [FiniteDimensional 𝕜 E] [TopologicalSpace F] [AddCommGroupₓ F] [Module 𝕜 F] [TopologicalAddGroup F]
    [HasContinuousSmul 𝕜 F] [FiniteDimensional 𝕜 F] : FiniteDimensional 𝕜 (E →L[𝕜] F) := by
  have : IsNoetherian 𝕜 (E →ₗ[𝕜] F) :=
    is_noetherian.iff_fg.mpr
      (by
        infer_instance)
  let I : (E →L[𝕜] F) →ₗ[𝕜] E →ₗ[𝕜] F := ContinuousLinearMap.coeLm 𝕜
  exact Module.Finite.of_injective I ContinuousLinearMap.coe_injective

section CompleteField

variable {𝕜 : Type u} [NondiscreteNormedField 𝕜] {E : Type v} [NormedGroup E] [NormedSpace 𝕜 E] {F : Type w}
  [NormedGroup F] [NormedSpace 𝕜 F] {F' : Type x} [AddCommGroupₓ F'] [Module 𝕜 F'] [TopologicalSpace F']
  [TopologicalAddGroup F'] [HasContinuousSmul 𝕜 F'] [CompleteSpace 𝕜]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " In finite dimension over a complete field, the canonical identification (in terms of a basis)\nwith `𝕜^n` together with its sup norm is continuous. This is the nontrivial part in the fact that\nall norms are equivalent in finite dimension.\n\nThis statement is superceded by the fact that every linear map on a finite-dimensional space is\ncontinuous, in `linear_map.continuous_of_finite_dimensional`. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `continuous_equiv_fun_basis [])
  (Command.declSig
   [(Term.implicitBinder "{" [`ι] [":" (Term.type "Type" [`v])] "}")
    (Term.instBinder "[" [] (Term.app `Fintype [`ι]) "]")
    (Term.explicitBinder "(" [`ξ] [":" (Term.app `Basis [`ι `𝕜 `E])] [] ")")]
   (Term.typeSpec ":" (Term.app `Continuous [`ξ.equiv_fun])))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.paren
         "("
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.induction'
              "induction'"
              [(Tactic.casesTarget [`hn ":"] (Term.app `Fintype.card [`ι]))]
              []
              ["with" [(Lean.binderIdent `n) (Lean.binderIdent `IH)]]
              ["generalizing" [`ι `E]])
             [])]))
         ")")
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.apply
              "apply"
              (Term.app
               `ξ.equiv_fun.to_linear_map.continuous_of_bound
               [(numLit "0") (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x] [])] "=>" (Term.hole "_")))]))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec ":" («term_=_» (Term.app `ξ.equiv_fun [`x]) "=" (numLit "0")))]
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
                        [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `i)] []) [])
                         (group
                          (Tactic.exact
                           "exact"
                           (Term.app
                            (Term.proj
                             (Term.app (Term.proj `Fintype.card_eq_zero_iff "." (fieldIdx "1")) [`hn])
                             "."
                             `elim)
                            [`i]))
                          [])])))
                     [])]))))))
             [])
            (group
             (Tactic.change
              "change"
              («term_≤_»
               (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `ξ.equiv_fun [`x]) "∥")
               "≤"
               (Finset.Data.Finset.Fold.«term_*_» (numLit "0") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥")))
              [])
             [])
            (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") []) [])
            (group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `norm_nonneg)] "]"] []) [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec ":" (Term.app `FiniteDimensional [`𝕜 `E]))]
                ":="
                (Term.app `of_fintype_basis [`ξ]))))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`H₁ []]
                [(Term.typeSpec
                  ":"
                  (Term.forall
                   "∀"
                   [(Term.simpleBinder [`s] [(Term.typeSpec ":" (Term.app `Submodule [`𝕜 `E]))])]
                   ","
                   (Term.arrow
                    («term_=_» (Term.app `finrank [`𝕜 `s]) "=" `n)
                    "→"
                    (Term.app
                     `IsClosed
                     [(Term.paren "(" [`s [(Term.typeAscription ":" (Term.app `Set [`E]))]] ")")]))))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group (Tactic.intro "intro" [`s `s_dim]) [])
                    (group
                     (Tactic.tacticLet_
                      "let"
                      (Term.letDecl (Term.letIdDecl `b [] ":=" (Term.app `Basis.ofVectorSpace [`𝕜 `s]))))
                     [])
                    (group
                     (Tactic.tacticHave_
                      "have"
                      (Term.haveDecl
                       (Term.haveIdDecl
                        [`U []]
                        [(Term.typeSpec ":" (Term.app `UniformEmbedding [`b.equiv_fun.symm.to_equiv]))]
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
                                []
                                [(Term.typeSpec
                                  ":"
                                  («term_=_»
                                   (Term.app `Fintype.card [(Term.app `Basis.OfVectorSpaceIndex [`𝕜 `s])])
                                   "="
                                   `n))]
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
                                           (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `s_dim)] "]")
                                           [])
                                          [])
                                         (group
                                          (Tactic.exact
                                           "exact"
                                           (Term.proj (Term.app `finrank_eq_card_basis [`b]) "." `symm))
                                          [])])))
                                     [])]))))))
                             [])
                            (group
                             (Tactic.tacticHave_
                              "have"
                              (Term.haveDecl
                               (Term.haveIdDecl
                                []
                                [(Term.typeSpec ":" (Term.app `Continuous [`b.equiv_fun]))]
                                ":="
                                (Term.app `IH [`b `this]))))
                             [])
                            (group
                             (Tactic.exact
                              "exact"
                              (Term.app
                               `b.equiv_fun.symm.uniform_embedding
                               [`b.equiv_fun.symm.to_linear_map.continuous_on_pi `this]))
                             [])]))))))
                     [])
                    (group
                     (Tactic.have''
                      "have"
                      []
                      [(Term.typeSpec
                        ":"
                        (Term.app
                         `IsComplete
                         [(Term.paren "(" [`s [(Term.typeAscription ":" (Term.app `Set [`E]))]] ")")]))])
                     [])
                    (group
                     (Tactic.exact
                      "exact"
                      (Term.app
                       (Term.proj `complete_space_coe_iff_is_complete "." (fieldIdx "1"))
                       [(Term.app
                         (Term.proj (Term.app `complete_space_congr [`U]) "." (fieldIdx "1"))
                         [(Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(group (Tactic.tacticInfer_instance "infer_instance") [])])))])]))
                     [])
                    (group (Tactic.exact "exact" `this.is_closed) [])]))))))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`H₂ []]
                [(Term.typeSpec
                  ":"
                  (Term.forall
                   "∀"
                   [(Term.simpleBinder
                     [`f]
                     [(Term.typeSpec ":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `E " →ₗ[" `𝕜 "] " `𝕜))])]
                   ","
                   (Term.app `Continuous [`f])))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group (Tactic.intro "intro" [`f]) [])
                    (group
                     (Tactic.tacticHave_
                      "have"
                      (Term.haveDecl
                       (Term.haveIdDecl
                        []
                        [(Term.typeSpec
                          ":"
                          («term_∨_»
                           («term_=_» (Term.app `finrank [`𝕜 `f.ker]) "=" `n)
                           "∨"
                           («term_=_» (Term.app `finrank [`𝕜 `f.ker]) "=" `n.succ)))]
                        ":="
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(group
                             (Tactic.tacticHave_
                              "have"
                              (Term.haveDecl (Term.haveIdDecl [`Z []] [] ":=" `f.finrank_range_add_finrank_ker)))
                             [])
                            (group
                             (Tactic.rwSeq
                              "rw"
                              []
                              (Tactic.rwRuleSeq
                               "["
                               [(Tactic.rwRule [] (Term.app `finrank_eq_card_basis [`ξ])) "," (Tactic.rwRule [] `hn)]
                               "]")
                              [(Tactic.location "at" (Tactic.locationHyp [`Z] []))])
                             [])
                            (group
                             (Tactic.byCases'
                              "by_cases'"
                              [`H ":"]
                              («term_=_» (Term.app `finrank [`𝕜 `f.range]) "=" (numLit "0")))
                             [])
                            (group
                             (Tactic.«tactic·._»
                              "·"
                              (Tactic.tacticSeq
                               (Tactic.tacticSeq1Indented
                                [(group (Tactic.right "right") [])
                                 (group
                                  (Tactic.rwSeq
                                   "rw"
                                   []
                                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `H)] "]")
                                   [(Tactic.location "at" (Tactic.locationHyp [`Z] []))])
                                  [])
                                 (group (Tactic.simpa "simpa" [] [] [] [] ["using" `Z]) [])])))
                             [])
                            (group
                             (Tactic.«tactic·._»
                              "·"
                              (Tactic.tacticSeq
                               (Tactic.tacticSeq1Indented
                                [(group (Tactic.left "left") [])
                                 (group
                                  (Tactic.tacticHave_
                                   "have"
                                   (Term.haveDecl
                                    (Term.haveIdDecl
                                     []
                                     [(Term.typeSpec
                                       ":"
                                       («term_=_» (Term.app `finrank [`𝕜 `f.range]) "=" (numLit "1")))]
                                     ":="
                                     (Term.byTactic
                                      "by"
                                      (Tactic.tacticSeq
                                       (Tactic.tacticSeq1Indented
                                        [(group
                                          (Tactic.refine'
                                           "refine'"
                                           (Term.app `le_antisymmₓ [(Term.hole "_") (Term.app `zero_lt_iff.mpr [`H])]))
                                          [])
                                         (group
                                          (Tactic.simpa
                                           "simpa"
                                           []
                                           []
                                           ["[" [(Tactic.simpLemma [] [] `finrank_self)] "]"]
                                           []
                                           ["using" `f.range.finrank_le])
                                          [])]))))))
                                  [])
                                 (group
                                  (Tactic.rwSeq
                                   "rw"
                                   []
                                   (Tactic.rwRuleSeq
                                    "["
                                    [(Tactic.rwRule [] `this)
                                     ","
                                     (Tactic.rwRule [] `add_commₓ)
                                     ","
                                     (Tactic.rwRule [] `Nat.add_one)]
                                    "]")
                                   [(Tactic.location "at" (Tactic.locationHyp [`Z] []))])
                                  [])
                                 (group (Tactic.exact "exact" (Term.app `Nat.succ.injₓ [`Z])) [])])))
                             [])]))))))
                     [])
                    (group
                     (Tactic.tacticHave_
                      "have"
                      (Term.haveDecl
                       (Term.haveIdDecl
                        []
                        [(Term.typeSpec
                          ":"
                          (Term.app
                           `IsClosed
                           [(Term.paren "(" [`f.ker [(Term.typeAscription ":" (Term.app `Set [`E]))]] ")")]))]
                        ":="
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(group (Tactic.cases "cases" [(Tactic.casesTarget [] `this)] [] []) [])
                            (group
                             (Tactic.«tactic·._»
                              "·"
                              (Tactic.tacticSeq
                               (Tactic.tacticSeq1Indented
                                [(group (Tactic.exact "exact" (Term.app `H₁ [(Term.hole "_") `this])) [])])))
                             [])
                            (group
                             (Tactic.«tactic·._»
                              "·"
                              (Tactic.tacticSeq
                               (Tactic.tacticSeq1Indented
                                [(group
                                  (Tactic.tacticHave_
                                   "have"
                                   (Term.haveDecl
                                    (Term.haveIdDecl
                                     []
                                     [(Term.typeSpec ":" («term_=_» `f.ker "=" (Order.BoundedOrder.«term⊤» "⊤")))]
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
                                             [(group (Tactic.apply "apply" `eq_top_of_finrank_eq) [])
                                              (group
                                               (Tactic.rwSeq
                                                "rw"
                                                []
                                                (Tactic.rwRuleSeq
                                                 "["
                                                 [(Tactic.rwRule [] (Term.app `finrank_eq_card_basis [`ξ]))
                                                  ","
                                                  (Tactic.rwRule [] `hn)
                                                  ","
                                                  (Tactic.rwRule [] `this)]
                                                 "]")
                                                [])
                                               [])])))
                                          [])]))))))
                                  [])
                                 (group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `this)] "]"] []) [])])))
                             [])]))))))
                     [])
                    (group
                     (Tactic.exact
                      "exact"
                      (Term.app (Term.proj `LinearMap.continuous_iff_is_closed_ker "." (fieldIdx "2")) [`this]))
                     [])]))))))
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
                   [(Term.simpleBinder [`i] [(Term.typeSpec ":" `ι)])]
                   ","
                   («term∃_,_»
                    "∃"
                    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `C)] []))
                    ","
                    («term_∧_»
                     («term_≤_» (numLit "0") "≤" `C)
                     "∧"
                     (Term.forall
                      "∀"
                      [(Term.simpleBinder [`x] [(Term.typeSpec ":" `E)])]
                      ","
                      («term_≤_»
                       (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `ξ.equiv_fun [`x `i]) "∥")
                       "≤"
                       (Finset.Data.Finset.Fold.«term_*_»
                        `C
                        "*"
                        (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥"))))))))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group (Tactic.intro "intro" [`i]) [])
                    (group
                     (Tactic.tacticLet_
                      "let"
                      (Term.letDecl
                       (Term.letIdDecl
                        `f
                        [(Term.typeSpec ":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `E " →ₗ[" `𝕜 "] " `𝕜))]
                        ":="
                        (LinearMap.Algebra.Module.LinearMap.«term_∘ₗ_»
                         (Term.app `LinearMap.proj [`i])
                         " ∘ₗ "
                         (Init.Coe.«term↑_» "↑" `ξ.equiv_fun)))))
                     [])
                    (group
                     (Tactic.tacticLet_
                      "let"
                      (Term.letDecl
                       (Term.letIdDecl
                        `f'
                        [(Term.typeSpec ":" (Topology.Algebra.Module.«term_→L[_]_» `E " →L[" `𝕜 "] " `𝕜))]
                        ":="
                        (Term.structInst
                         "{"
                         [[`f] "with"]
                         [(group (Term.structInstField (Term.structInstLVal `cont []) ":=" (Term.app `H₂ [`f])) [])]
                         (Term.optEllipsis [])
                         []
                         "}"))))
                     [])
                    (group
                     (Tactic.exact
                      "exact"
                      (Term.anonymousCtor
                       "⟨"
                       [(Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f' "∥")
                        ","
                        (Term.app `norm_nonneg [(Term.hole "_")])
                        ","
                        (Term.fun
                         "fun"
                         (Term.basicFun
                          [(Term.simpleBinder [`x] [])]
                          "=>"
                          (Term.app `ContinuousLinearMap.le_op_norm [`f' `x])))]
                       "⟩"))
                     [])]))))))
             [])
            (group (Tactic.choose "choose" [`C0 `hC0] ["using" `this]) [])
            (group
             (Tactic.tacticLet_
              "let"
              (Term.letDecl
               (Term.letIdDecl
                `C
                []
                ":="
                (Algebra.BigOperators.Basic.«term∑_,_»
                 "∑"
                 (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                 ", "
                 (Term.app `C0 [`i])))))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`C_nonneg []]
                [(Term.typeSpec ":" («term_≤_» (numLit "0") "≤" `C))]
                ":="
                (Term.app
                 `Finset.sum_nonneg
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`i `hi] [])]
                    "=>"
                    (Term.proj (Term.app `hC0 [`i]) "." (fieldIdx "1"))))]))))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`C0_le []]
                [(Term.typeSpec
                  ":"
                  (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," («term_≤_» (Term.app `C0 [`i]) "≤" `C)))]
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`i] [])]
                  "=>"
                  (Term.app
                   `Finset.single_le_sum
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.simpleBinder [`j `hj] [])]
                      "=>"
                      (Term.proj (Term.app `hC0 [`j]) "." (fieldIdx "1"))))
                    (Term.app `Finset.mem_univ [(Term.hole "_")])]))))))
             [])
            (group
             (Tactic.apply
              "apply"
              (Term.app
               `ξ.equiv_fun.to_linear_map.continuous_of_bound
               [`C (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x] [])] "=>" (Term.hole "_")))]))
             [])
            (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `pi_semi_norm_le_iff)] "]") []) [])
            (group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.exact
                   "exact"
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [`i] [])]
                     "=>"
                     (Term.app
                      `le_transₓ
                      [(Term.app (Term.proj (Term.app `hC0 [`i]) "." (fieldIdx "2")) [`x])
                       (Term.app
                        `mul_le_mul_of_nonneg_right
                        [(Term.app `C0_le [`i]) (Term.app `norm_nonneg [(Term.hole "_")])])]))))
                  [])])))
             [])
            (group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.exact "exact" (Term.app `mul_nonneg [`C_nonneg (Term.app `norm_nonneg [(Term.hole "_")])]))
                  [])])))
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
       (Tactic.paren
        "("
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.induction'
             "induction'"
             [(Tactic.casesTarget [`hn ":"] (Term.app `Fintype.card [`ι]))]
             []
             ["with" [(Lean.binderIdent `n) (Lean.binderIdent `IH)]]
             ["generalizing" [`ι `E]])
            [])]))
        ")")
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.apply
             "apply"
             (Term.app
              `ξ.equiv_fun.to_linear_map.continuous_of_bound
              [(numLit "0") (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x] [])] "=>" (Term.hole "_")))]))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec ":" («term_=_» (Term.app `ξ.equiv_fun [`x]) "=" (numLit "0")))]
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
                       [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `i)] []) [])
                        (group
                         (Tactic.exact
                          "exact"
                          (Term.app
                           (Term.proj
                            (Term.app (Term.proj `Fintype.card_eq_zero_iff "." (fieldIdx "1")) [`hn])
                            "."
                            `elim)
                           [`i]))
                         [])])))
                    [])]))))))
            [])
           (group
            (Tactic.change
             "change"
             («term_≤_»
              (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `ξ.equiv_fun [`x]) "∥")
              "≤"
              (Finset.Data.Finset.Fold.«term_*_» (numLit "0") "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥")))
             [])
            [])
           (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this)] "]") []) [])
           (group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `norm_nonneg)] "]"] []) [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec ":" (Term.app `FiniteDimensional [`𝕜 `E]))]
               ":="
               (Term.app `of_fintype_basis [`ξ]))))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`H₁ []]
               [(Term.typeSpec
                 ":"
                 (Term.forall
                  "∀"
                  [(Term.simpleBinder [`s] [(Term.typeSpec ":" (Term.app `Submodule [`𝕜 `E]))])]
                  ","
                  (Term.arrow
                   («term_=_» (Term.app `finrank [`𝕜 `s]) "=" `n)
                   "→"
                   (Term.app `IsClosed [(Term.paren "(" [`s [(Term.typeAscription ":" (Term.app `Set [`E]))]] ")")]))))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.intro "intro" [`s `s_dim]) [])
                   (group
                    (Tactic.tacticLet_
                     "let"
                     (Term.letDecl (Term.letIdDecl `b [] ":=" (Term.app `Basis.ofVectorSpace [`𝕜 `s]))))
                    [])
                   (group
                    (Tactic.tacticHave_
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       [`U []]
                       [(Term.typeSpec ":" (Term.app `UniformEmbedding [`b.equiv_fun.symm.to_equiv]))]
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
                               []
                               [(Term.typeSpec
                                 ":"
                                 («term_=_»
                                  (Term.app `Fintype.card [(Term.app `Basis.OfVectorSpaceIndex [`𝕜 `s])])
                                  "="
                                  `n))]
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
                                          (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `s_dim)] "]")
                                          [])
                                         [])
                                        (group
                                         (Tactic.exact
                                          "exact"
                                          (Term.proj (Term.app `finrank_eq_card_basis [`b]) "." `symm))
                                         [])])))
                                    [])]))))))
                            [])
                           (group
                            (Tactic.tacticHave_
                             "have"
                             (Term.haveDecl
                              (Term.haveIdDecl
                               []
                               [(Term.typeSpec ":" (Term.app `Continuous [`b.equiv_fun]))]
                               ":="
                               (Term.app `IH [`b `this]))))
                            [])
                           (group
                            (Tactic.exact
                             "exact"
                             (Term.app
                              `b.equiv_fun.symm.uniform_embedding
                              [`b.equiv_fun.symm.to_linear_map.continuous_on_pi `this]))
                            [])]))))))
                    [])
                   (group
                    (Tactic.have''
                     "have"
                     []
                     [(Term.typeSpec
                       ":"
                       (Term.app
                        `IsComplete
                        [(Term.paren "(" [`s [(Term.typeAscription ":" (Term.app `Set [`E]))]] ")")]))])
                    [])
                   (group
                    (Tactic.exact
                     "exact"
                     (Term.app
                      (Term.proj `complete_space_coe_iff_is_complete "." (fieldIdx "1"))
                      [(Term.app
                        (Term.proj (Term.app `complete_space_congr [`U]) "." (fieldIdx "1"))
                        [(Term.byTactic
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented
                            [(group (Tactic.tacticInfer_instance "infer_instance") [])])))])]))
                    [])
                   (group (Tactic.exact "exact" `this.is_closed) [])]))))))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`H₂ []]
               [(Term.typeSpec
                 ":"
                 (Term.forall
                  "∀"
                  [(Term.simpleBinder
                    [`f]
                    [(Term.typeSpec ":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `E " →ₗ[" `𝕜 "] " `𝕜))])]
                  ","
                  (Term.app `Continuous [`f])))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.intro "intro" [`f]) [])
                   (group
                    (Tactic.tacticHave_
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       []
                       [(Term.typeSpec
                         ":"
                         («term_∨_»
                          («term_=_» (Term.app `finrank [`𝕜 `f.ker]) "=" `n)
                          "∨"
                          («term_=_» (Term.app `finrank [`𝕜 `f.ker]) "=" `n.succ)))]
                       ":="
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group
                            (Tactic.tacticHave_
                             "have"
                             (Term.haveDecl (Term.haveIdDecl [`Z []] [] ":=" `f.finrank_range_add_finrank_ker)))
                            [])
                           (group
                            (Tactic.rwSeq
                             "rw"
                             []
                             (Tactic.rwRuleSeq
                              "["
                              [(Tactic.rwRule [] (Term.app `finrank_eq_card_basis [`ξ])) "," (Tactic.rwRule [] `hn)]
                              "]")
                             [(Tactic.location "at" (Tactic.locationHyp [`Z] []))])
                            [])
                           (group
                            (Tactic.byCases'
                             "by_cases'"
                             [`H ":"]
                             («term_=_» (Term.app `finrank [`𝕜 `f.range]) "=" (numLit "0")))
                            [])
                           (group
                            (Tactic.«tactic·._»
                             "·"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(group (Tactic.right "right") [])
                                (group
                                 (Tactic.rwSeq
                                  "rw"
                                  []
                                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `H)] "]")
                                  [(Tactic.location "at" (Tactic.locationHyp [`Z] []))])
                                 [])
                                (group (Tactic.simpa "simpa" [] [] [] [] ["using" `Z]) [])])))
                            [])
                           (group
                            (Tactic.«tactic·._»
                             "·"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(group (Tactic.left "left") [])
                                (group
                                 (Tactic.tacticHave_
                                  "have"
                                  (Term.haveDecl
                                   (Term.haveIdDecl
                                    []
                                    [(Term.typeSpec ":" («term_=_» (Term.app `finrank [`𝕜 `f.range]) "=" (numLit "1")))]
                                    ":="
                                    (Term.byTactic
                                     "by"
                                     (Tactic.tacticSeq
                                      (Tactic.tacticSeq1Indented
                                       [(group
                                         (Tactic.refine'
                                          "refine'"
                                          (Term.app `le_antisymmₓ [(Term.hole "_") (Term.app `zero_lt_iff.mpr [`H])]))
                                         [])
                                        (group
                                         (Tactic.simpa
                                          "simpa"
                                          []
                                          []
                                          ["[" [(Tactic.simpLemma [] [] `finrank_self)] "]"]
                                          []
                                          ["using" `f.range.finrank_le])
                                         [])]))))))
                                 [])
                                (group
                                 (Tactic.rwSeq
                                  "rw"
                                  []
                                  (Tactic.rwRuleSeq
                                   "["
                                   [(Tactic.rwRule [] `this)
                                    ","
                                    (Tactic.rwRule [] `add_commₓ)
                                    ","
                                    (Tactic.rwRule [] `Nat.add_one)]
                                   "]")
                                  [(Tactic.location "at" (Tactic.locationHyp [`Z] []))])
                                 [])
                                (group (Tactic.exact "exact" (Term.app `Nat.succ.injₓ [`Z])) [])])))
                            [])]))))))
                    [])
                   (group
                    (Tactic.tacticHave_
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       []
                       [(Term.typeSpec
                         ":"
                         (Term.app
                          `IsClosed
                          [(Term.paren "(" [`f.ker [(Term.typeAscription ":" (Term.app `Set [`E]))]] ")")]))]
                       ":="
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group (Tactic.cases "cases" [(Tactic.casesTarget [] `this)] [] []) [])
                           (group
                            (Tactic.«tactic·._»
                             "·"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(group (Tactic.exact "exact" (Term.app `H₁ [(Term.hole "_") `this])) [])])))
                            [])
                           (group
                            (Tactic.«tactic·._»
                             "·"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(group
                                 (Tactic.tacticHave_
                                  "have"
                                  (Term.haveDecl
                                   (Term.haveIdDecl
                                    []
                                    [(Term.typeSpec ":" («term_=_» `f.ker "=" (Order.BoundedOrder.«term⊤» "⊤")))]
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
                                            [(group (Tactic.apply "apply" `eq_top_of_finrank_eq) [])
                                             (group
                                              (Tactic.rwSeq
                                               "rw"
                                               []
                                               (Tactic.rwRuleSeq
                                                "["
                                                [(Tactic.rwRule [] (Term.app `finrank_eq_card_basis [`ξ]))
                                                 ","
                                                 (Tactic.rwRule [] `hn)
                                                 ","
                                                 (Tactic.rwRule [] `this)]
                                                "]")
                                               [])
                                              [])])))
                                         [])]))))))
                                 [])
                                (group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `this)] "]"] []) [])])))
                            [])]))))))
                    [])
                   (group
                    (Tactic.exact
                     "exact"
                     (Term.app (Term.proj `LinearMap.continuous_iff_is_closed_ker "." (fieldIdx "2")) [`this]))
                    [])]))))))
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
                  [(Term.simpleBinder [`i] [(Term.typeSpec ":" `ι)])]
                  ","
                  («term∃_,_»
                   "∃"
                   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `C)] []))
                   ","
                   («term_∧_»
                    («term_≤_» (numLit "0") "≤" `C)
                    "∧"
                    (Term.forall
                     "∀"
                     [(Term.simpleBinder [`x] [(Term.typeSpec ":" `E)])]
                     ","
                     («term_≤_»
                      (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `ξ.equiv_fun [`x `i]) "∥")
                      "≤"
                      (Finset.Data.Finset.Fold.«term_*_»
                       `C
                       "*"
                       (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥"))))))))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.intro "intro" [`i]) [])
                   (group
                    (Tactic.tacticLet_
                     "let"
                     (Term.letDecl
                      (Term.letIdDecl
                       `f
                       [(Term.typeSpec ":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `E " →ₗ[" `𝕜 "] " `𝕜))]
                       ":="
                       (LinearMap.Algebra.Module.LinearMap.«term_∘ₗ_»
                        (Term.app `LinearMap.proj [`i])
                        " ∘ₗ "
                        (Init.Coe.«term↑_» "↑" `ξ.equiv_fun)))))
                    [])
                   (group
                    (Tactic.tacticLet_
                     "let"
                     (Term.letDecl
                      (Term.letIdDecl
                       `f'
                       [(Term.typeSpec ":" (Topology.Algebra.Module.«term_→L[_]_» `E " →L[" `𝕜 "] " `𝕜))]
                       ":="
                       (Term.structInst
                        "{"
                        [[`f] "with"]
                        [(group (Term.structInstField (Term.structInstLVal `cont []) ":=" (Term.app `H₂ [`f])) [])]
                        (Term.optEllipsis [])
                        []
                        "}"))))
                    [])
                   (group
                    (Tactic.exact
                     "exact"
                     (Term.anonymousCtor
                      "⟨"
                      [(Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f' "∥")
                       ","
                       (Term.app `norm_nonneg [(Term.hole "_")])
                       ","
                       (Term.fun
                        "fun"
                        (Term.basicFun
                         [(Term.simpleBinder [`x] [])]
                         "=>"
                         (Term.app `ContinuousLinearMap.le_op_norm [`f' `x])))]
                      "⟩"))
                    [])]))))))
            [])
           (group (Tactic.choose "choose" [`C0 `hC0] ["using" `this]) [])
           (group
            (Tactic.tacticLet_
             "let"
             (Term.letDecl
              (Term.letIdDecl
               `C
               []
               ":="
               (Algebra.BigOperators.Basic.«term∑_,_»
                "∑"
                (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                ", "
                (Term.app `C0 [`i])))))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`C_nonneg []]
               [(Term.typeSpec ":" («term_≤_» (numLit "0") "≤" `C))]
               ":="
               (Term.app
                `Finset.sum_nonneg
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`i `hi] [])]
                   "=>"
                   (Term.proj (Term.app `hC0 [`i]) "." (fieldIdx "1"))))]))))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`C0_le []]
               [(Term.typeSpec
                 ":"
                 (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," («term_≤_» (Term.app `C0 [`i]) "≤" `C)))]
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`i] [])]
                 "=>"
                 (Term.app
                  `Finset.single_le_sum
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [`j `hj] [])]
                     "=>"
                     (Term.proj (Term.app `hC0 [`j]) "." (fieldIdx "1"))))
                   (Term.app `Finset.mem_univ [(Term.hole "_")])]))))))
            [])
           (group
            (Tactic.apply
             "apply"
             (Term.app
              `ξ.equiv_fun.to_linear_map.continuous_of_bound
              [`C (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x] [])] "=>" (Term.hole "_")))]))
            [])
           (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `pi_semi_norm_le_iff)] "]") []) [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.exact
                  "exact"
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`i] [])]
                    "=>"
                    (Term.app
                     `le_transₓ
                     [(Term.app (Term.proj (Term.app `hC0 [`i]) "." (fieldIdx "2")) [`x])
                      (Term.app
                       `mul_le_mul_of_nonneg_right
                       [(Term.app `C0_le [`i]) (Term.app `norm_nonneg [(Term.hole "_")])])]))))
                 [])])))
            [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.exact "exact" (Term.app `mul_nonneg [`C_nonneg (Term.app `norm_nonneg [(Term.hole "_")])]))
                 [])])))
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
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec ":" (Term.app `FiniteDimensional [`𝕜 `E]))]
          ":="
          (Term.app `of_fintype_basis [`ξ]))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`H₁ []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`s] [(Term.typeSpec ":" (Term.app `Submodule [`𝕜 `E]))])]
             ","
             (Term.arrow
              («term_=_» (Term.app `finrank [`𝕜 `s]) "=" `n)
              "→"
              (Term.app `IsClosed [(Term.paren "(" [`s [(Term.typeAscription ":" (Term.app `Set [`E]))]] ")")]))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`s `s_dim]) [])
              (group
               (Tactic.tacticLet_
                "let"
                (Term.letDecl (Term.letIdDecl `b [] ":=" (Term.app `Basis.ofVectorSpace [`𝕜 `s]))))
               [])
              (group
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`U []]
                  [(Term.typeSpec ":" (Term.app `UniformEmbedding [`b.equiv_fun.symm.to_equiv]))]
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
                          []
                          [(Term.typeSpec
                            ":"
                            («term_=_» (Term.app `Fintype.card [(Term.app `Basis.OfVectorSpaceIndex [`𝕜 `s])]) "=" `n))]
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
                                    (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `s_dim)] "]") [])
                                    [])
                                   (group
                                    (Tactic.exact "exact" (Term.proj (Term.app `finrank_eq_card_basis [`b]) "." `symm))
                                    [])])))
                               [])]))))))
                       [])
                      (group
                       (Tactic.tacticHave_
                        "have"
                        (Term.haveDecl
                         (Term.haveIdDecl
                          []
                          [(Term.typeSpec ":" (Term.app `Continuous [`b.equiv_fun]))]
                          ":="
                          (Term.app `IH [`b `this]))))
                       [])
                      (group
                       (Tactic.exact
                        "exact"
                        (Term.app
                         `b.equiv_fun.symm.uniform_embedding
                         [`b.equiv_fun.symm.to_linear_map.continuous_on_pi `this]))
                       [])]))))))
               [])
              (group
               (Tactic.have''
                "have"
                []
                [(Term.typeSpec
                  ":"
                  (Term.app `IsComplete [(Term.paren "(" [`s [(Term.typeAscription ":" (Term.app `Set [`E]))]] ")")]))])
               [])
              (group
               (Tactic.exact
                "exact"
                (Term.app
                 (Term.proj `complete_space_coe_iff_is_complete "." (fieldIdx "1"))
                 [(Term.app
                   (Term.proj (Term.app `complete_space_congr [`U]) "." (fieldIdx "1"))
                   [(Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented [(group (Tactic.tacticInfer_instance "infer_instance") [])])))])]))
               [])
              (group (Tactic.exact "exact" `this.is_closed) [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`H₂ []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder
               [`f]
               [(Term.typeSpec ":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `E " →ₗ[" `𝕜 "] " `𝕜))])]
             ","
             (Term.app `Continuous [`f])))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`f]) [])
              (group
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  []
                  [(Term.typeSpec
                    ":"
                    («term_∨_»
                     («term_=_» (Term.app `finrank [`𝕜 `f.ker]) "=" `n)
                     "∨"
                     («term_=_» (Term.app `finrank [`𝕜 `f.ker]) "=" `n.succ)))]
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Tactic.tacticHave_
                        "have"
                        (Term.haveDecl (Term.haveIdDecl [`Z []] [] ":=" `f.finrank_range_add_finrank_ker)))
                       [])
                      (group
                       (Tactic.rwSeq
                        "rw"
                        []
                        (Tactic.rwRuleSeq
                         "["
                         [(Tactic.rwRule [] (Term.app `finrank_eq_card_basis [`ξ])) "," (Tactic.rwRule [] `hn)]
                         "]")
                        [(Tactic.location "at" (Tactic.locationHyp [`Z] []))])
                       [])
                      (group
                       (Tactic.byCases'
                        "by_cases'"
                        [`H ":"]
                        («term_=_» (Term.app `finrank [`𝕜 `f.range]) "=" (numLit "0")))
                       [])
                      (group
                       (Tactic.«tactic·._»
                        "·"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group (Tactic.right "right") [])
                           (group
                            (Tactic.rwSeq
                             "rw"
                             []
                             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `H)] "]")
                             [(Tactic.location "at" (Tactic.locationHyp [`Z] []))])
                            [])
                           (group (Tactic.simpa "simpa" [] [] [] [] ["using" `Z]) [])])))
                       [])
                      (group
                       (Tactic.«tactic·._»
                        "·"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group (Tactic.left "left") [])
                           (group
                            (Tactic.tacticHave_
                             "have"
                             (Term.haveDecl
                              (Term.haveIdDecl
                               []
                               [(Term.typeSpec ":" («term_=_» (Term.app `finrank [`𝕜 `f.range]) "=" (numLit "1")))]
                               ":="
                               (Term.byTactic
                                "by"
                                (Tactic.tacticSeq
                                 (Tactic.tacticSeq1Indented
                                  [(group
                                    (Tactic.refine'
                                     "refine'"
                                     (Term.app `le_antisymmₓ [(Term.hole "_") (Term.app `zero_lt_iff.mpr [`H])]))
                                    [])
                                   (group
                                    (Tactic.simpa
                                     "simpa"
                                     []
                                     []
                                     ["[" [(Tactic.simpLemma [] [] `finrank_self)] "]"]
                                     []
                                     ["using" `f.range.finrank_le])
                                    [])]))))))
                            [])
                           (group
                            (Tactic.rwSeq
                             "rw"
                             []
                             (Tactic.rwRuleSeq
                              "["
                              [(Tactic.rwRule [] `this)
                               ","
                               (Tactic.rwRule [] `add_commₓ)
                               ","
                               (Tactic.rwRule [] `Nat.add_one)]
                              "]")
                             [(Tactic.location "at" (Tactic.locationHyp [`Z] []))])
                            [])
                           (group (Tactic.exact "exact" (Term.app `Nat.succ.injₓ [`Z])) [])])))
                       [])]))))))
               [])
              (group
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  []
                  [(Term.typeSpec
                    ":"
                    (Term.app
                     `IsClosed
                     [(Term.paren "(" [`f.ker [(Term.typeAscription ":" (Term.app `Set [`E]))]] ")")]))]
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group (Tactic.cases "cases" [(Tactic.casesTarget [] `this)] [] []) [])
                      (group
                       (Tactic.«tactic·._»
                        "·"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group (Tactic.exact "exact" (Term.app `H₁ [(Term.hole "_") `this])) [])])))
                       [])
                      (group
                       (Tactic.«tactic·._»
                        "·"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group
                            (Tactic.tacticHave_
                             "have"
                             (Term.haveDecl
                              (Term.haveIdDecl
                               []
                               [(Term.typeSpec ":" («term_=_» `f.ker "=" (Order.BoundedOrder.«term⊤» "⊤")))]
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
                                       [(group (Tactic.apply "apply" `eq_top_of_finrank_eq) [])
                                        (group
                                         (Tactic.rwSeq
                                          "rw"
                                          []
                                          (Tactic.rwRuleSeq
                                           "["
                                           [(Tactic.rwRule [] (Term.app `finrank_eq_card_basis [`ξ]))
                                            ","
                                            (Tactic.rwRule [] `hn)
                                            ","
                                            (Tactic.rwRule [] `this)]
                                           "]")
                                          [])
                                         [])])))
                                    [])]))))))
                            [])
                           (group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `this)] "]"] []) [])])))
                       [])]))))))
               [])
              (group
               (Tactic.exact
                "exact"
                (Term.app (Term.proj `LinearMap.continuous_iff_is_closed_ker "." (fieldIdx "2")) [`this]))
               [])]))))))
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
             [(Term.simpleBinder [`i] [(Term.typeSpec ":" `ι)])]
             ","
             («term∃_,_»
              "∃"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `C)] []))
              ","
              («term_∧_»
               («term_≤_» (numLit "0") "≤" `C)
               "∧"
               (Term.forall
                "∀"
                [(Term.simpleBinder [`x] [(Term.typeSpec ":" `E)])]
                ","
                («term_≤_»
                 (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `ξ.equiv_fun [`x `i]) "∥")
                 "≤"
                 (Finset.Data.Finset.Fold.«term_*_» `C "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `x "∥"))))))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`i]) [])
              (group
               (Tactic.tacticLet_
                "let"
                (Term.letDecl
                 (Term.letIdDecl
                  `f
                  [(Term.typeSpec ":" (Algebra.Module.LinearMap.«term_→ₗ[_]_» `E " →ₗ[" `𝕜 "] " `𝕜))]
                  ":="
                  (LinearMap.Algebra.Module.LinearMap.«term_∘ₗ_»
                   (Term.app `LinearMap.proj [`i])
                   " ∘ₗ "
                   (Init.Coe.«term↑_» "↑" `ξ.equiv_fun)))))
               [])
              (group
               (Tactic.tacticLet_
                "let"
                (Term.letDecl
                 (Term.letIdDecl
                  `f'
                  [(Term.typeSpec ":" (Topology.Algebra.Module.«term_→L[_]_» `E " →L[" `𝕜 "] " `𝕜))]
                  ":="
                  (Term.structInst
                   "{"
                   [[`f] "with"]
                   [(group (Term.structInstField (Term.structInstLVal `cont []) ":=" (Term.app `H₂ [`f])) [])]
                   (Term.optEllipsis [])
                   []
                   "}"))))
               [])
              (group
               (Tactic.exact
                "exact"
                (Term.anonymousCtor
                 "⟨"
                 [(Analysis.Normed.Group.Basic.«term∥_∥» "∥" `f' "∥")
                  ","
                  (Term.app `norm_nonneg [(Term.hole "_")])
                  ","
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`x] [])]
                    "=>"
                    (Term.app `ContinuousLinearMap.le_op_norm [`f' `x])))]
                 "⟩"))
               [])]))))))
       [])
      (group (Tactic.choose "choose" [`C0 `hC0] ["using" `this]) [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `C
          []
          ":="
          (Algebra.BigOperators.Basic.«term∑_,_»
           "∑"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
           ", "
           (Term.app `C0 [`i])))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`C_nonneg []]
          [(Term.typeSpec ":" («term_≤_» (numLit "0") "≤" `C))]
          ":="
          (Term.app
           `Finset.sum_nonneg
           [(Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`i `hi] [])]
              "=>"
              (Term.proj (Term.app `hC0 [`i]) "." (fieldIdx "1"))))]))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`C0_le []]
          [(Term.typeSpec
            ":"
            (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," («term_≤_» (Term.app `C0 [`i]) "≤" `C)))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`i] [])]
            "=>"
            (Term.app
             `Finset.single_le_sum
             [(Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`j `hj] [])]
                "=>"
                (Term.proj (Term.app `hC0 [`j]) "." (fieldIdx "1"))))
              (Term.app `Finset.mem_univ [(Term.hole "_")])]))))))
       [])
      (group
       (Tactic.apply
        "apply"
        (Term.app
         `ξ.equiv_fun.to_linear_map.continuous_of_bound
         [`C (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x] [])] "=>" (Term.hole "_")))]))
       [])
      (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `pi_semi_norm_le_iff)] "]") []) [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.exact
             "exact"
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`i] [])]
               "=>"
               (Term.app
                `le_transₓ
                [(Term.app (Term.proj (Term.app `hC0 [`i]) "." (fieldIdx "2")) [`x])
                 (Term.app
                  `mul_le_mul_of_nonneg_right
                  [(Term.app `C0_le [`i]) (Term.app `norm_nonneg [(Term.hole "_")])])]))))
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.exact "exact" (Term.app `mul_nonneg [`C_nonneg (Term.app `norm_nonneg [(Term.hole "_")])]))
            [])])))
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
     [(group (Tactic.exact "exact" (Term.app `mul_nonneg [`C_nonneg (Term.app `norm_nonneg [(Term.hole "_")])])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `mul_nonneg [`C_nonneg (Term.app `norm_nonneg [(Term.hole "_")])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `mul_nonneg [`C_nonneg (Term.app `norm_nonneg [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `norm_nonneg [(Term.hole "_")]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `C_nonneg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mul_nonneg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.exact
        "exact"
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`i] [])]
          "=>"
          (Term.app
           `le_transₓ
           [(Term.app (Term.proj (Term.app `hC0 [`i]) "." (fieldIdx "2")) [`x])
            (Term.app
             `mul_le_mul_of_nonneg_right
             [(Term.app `C0_le [`i]) (Term.app `norm_nonneg [(Term.hole "_")])])]))))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`i] [])]
     "=>"
     (Term.app
      `le_transₓ
      [(Term.app (Term.proj (Term.app `hC0 [`i]) "." (fieldIdx "2")) [`x])
       (Term.app `mul_le_mul_of_nonneg_right [(Term.app `C0_le [`i]) (Term.app `norm_nonneg [(Term.hole "_")])])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`i] [])]
    "=>"
    (Term.app
     `le_transₓ
     [(Term.app (Term.proj (Term.app `hC0 [`i]) "." (fieldIdx "2")) [`x])
      (Term.app `mul_le_mul_of_nonneg_right [(Term.app `C0_le [`i]) (Term.app `norm_nonneg [(Term.hole "_")])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `le_transₓ
   [(Term.app (Term.proj (Term.app `hC0 [`i]) "." (fieldIdx "2")) [`x])
    (Term.app `mul_le_mul_of_nonneg_right [(Term.app `C0_le [`i]) (Term.app `norm_nonneg [(Term.hole "_")])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `mul_le_mul_of_nonneg_right [(Term.app `C0_le [`i]) (Term.app `norm_nonneg [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `norm_nonneg [(Term.hole "_")]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `C0_le [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `C0_le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `C0_le [`i]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mul_le_mul_of_nonneg_right
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `mul_le_mul_of_nonneg_right
   [(Term.paren "(" [(Term.app `C0_le [`i]) []] ")")
    (Term.paren "(" [(Term.app `norm_nonneg [(Term.hole "_")]) []] ")")])
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app (Term.proj (Term.app `hC0 [`i]) "." (fieldIdx "2")) [`x])
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
  (Term.proj (Term.app `hC0 [`i]) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `hC0 [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hC0
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `hC0 [`i]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app (Term.proj (Term.paren "(" [(Term.app `hC0 [`i]) []] ")") "." (fieldIdx "2")) [`x]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `le_transₓ
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `pi_semi_norm_le_iff)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `pi_semi_norm_le_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply
   "apply"
   (Term.app
    `ξ.equiv_fun.to_linear_map.continuous_of_bound
    [`C (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x] [])] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `ξ.equiv_fun.to_linear_map.continuous_of_bound
   [`C (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x] [])] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x] [])] "=>" (Term.hole "_")))
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
  `C
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `ξ.equiv_fun.to_linear_map.continuous_of_bound
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`C0_le []]
     [(Term.typeSpec ":" (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," («term_≤_» (Term.app `C0 [`i]) "≤" `C)))]
     ":="
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`i] [])]
       "=>"
       (Term.app
        `Finset.single_le_sum
        [(Term.fun
          "fun"
          (Term.basicFun [(Term.simpleBinder [`j `hj] [])] "=>" (Term.proj (Term.app `hC0 [`j]) "." (fieldIdx "1"))))
         (Term.app `Finset.mem_univ [(Term.hole "_")])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`i] [])]
    "=>"
    (Term.app
     `Finset.single_le_sum
     [(Term.fun
       "fun"
       (Term.basicFun [(Term.simpleBinder [`j `hj] [])] "=>" (Term.proj (Term.app `hC0 [`j]) "." (fieldIdx "1"))))
      (Term.app `Finset.mem_univ [(Term.hole "_")])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Finset.single_le_sum
   [(Term.fun
     "fun"
     (Term.basicFun [(Term.simpleBinder [`j `hj] [])] "=>" (Term.proj (Term.app `hC0 [`j]) "." (fieldIdx "1"))))
    (Term.app `Finset.mem_univ [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Finset.mem_univ [(Term.hole "_")])
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
  `Finset.mem_univ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Finset.mem_univ [(Term.hole "_")]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.fun
   "fun"
   (Term.basicFun [(Term.simpleBinder [`j `hj] [])] "=>" (Term.proj (Term.app `hC0 [`j]) "." (fieldIdx "1"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `hC0 [`j]) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `hC0 [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hC0
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `hC0 [`j]) []] ")")
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`j `hj] [])]
    "=>"
    (Term.proj (Term.paren "(" [(Term.app `hC0 [`j]) []] ")") "." (fieldIdx "1"))))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finset.single_le_sum
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," («term_≤_» (Term.app `C0 [`i]) "≤" `C))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_» (Term.app `C0 [`i]) "≤" `C)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `C
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `C0 [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `C0
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`C_nonneg []]
     [(Term.typeSpec ":" («term_≤_» (numLit "0") "≤" `C))]
     ":="
     (Term.app
      `Finset.sum_nonneg
      [(Term.fun
        "fun"
        (Term.basicFun [(Term.simpleBinder [`i `hi] [])] "=>" (Term.proj (Term.app `hC0 [`i]) "." (fieldIdx "1"))))]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Finset.sum_nonneg
   [(Term.fun
     "fun"
     (Term.basicFun [(Term.simpleBinder [`i `hi] [])] "=>" (Term.proj (Term.app `hC0 [`i]) "." (fieldIdx "1"))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun [(Term.simpleBinder [`i `hi] [])] "=>" (Term.proj (Term.app `hC0 [`i]) "." (fieldIdx "1"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `hC0 [`i]) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `hC0 [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hC0
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `hC0 [`i]) []] ")")
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finset.sum_nonneg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_» (numLit "0") "≤" `C)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `C
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticLet_
   "let"
   (Term.letDecl
    (Term.letIdDecl
     `C
     []
     ":="
     (Algebra.BigOperators.Basic.«term∑_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
      ", "
      (Term.app `C0 [`i])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticLet_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letDecl', expected 'Lean.Parser.Term.letDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
   ", "
   (Term.app `C0 [`i]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `C0 [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `C0
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letPatDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letEqnsDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letEqnsDecl'
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
    In finite dimension over a complete field, the canonical identification (in terms of a basis)
    with `𝕜^n` together with its sup norm is continuous. This is the nontrivial part in the fact that
    all norms are equivalent in finite dimension.
    
    This statement is superceded by the fact that every linear map on a finite-dimensional space is
    continuous, in `linear_map.continuous_of_finite_dimensional`. -/
  theorem
    continuous_equiv_fun_basis
    { ι : Type v } [ Fintype ι ] ( ξ : Basis ι 𝕜 E ) : Continuous ξ.equiv_fun
    :=
      by
        ( induction' hn : Fintype.card ι with n IH generalizing ι E )
          ·
            apply ξ.equiv_fun.to_linear_map.continuous_of_bound 0 fun x => _
              have : ξ.equiv_fun x = 0 := by · ext i exact Fintype.card_eq_zero_iff . 1 hn . elim i
              change ∥ ξ.equiv_fun x ∥ ≤ 0 * ∥ x ∥
              rw [ this ]
              simp [ norm_nonneg ]
          ·
            have : FiniteDimensional 𝕜 E := of_fintype_basis ξ
              have
                H₁
                  : ∀ s : Submodule 𝕜 E , finrank 𝕜 s = n → IsClosed ( s : Set E )
                  :=
                  by
                    intro s s_dim
                      let b := Basis.ofVectorSpace 𝕜 s
                      have
                        U
                          : UniformEmbedding b.equiv_fun.symm.to_equiv
                          :=
                          by
                            have
                                : Fintype.card Basis.OfVectorSpaceIndex 𝕜 s = n
                                  :=
                                  by · rw [ ← s_dim ] exact finrank_eq_card_basis b . symm
                              have : Continuous b.equiv_fun := IH b this
                              exact
                                b.equiv_fun.symm.uniform_embedding b.equiv_fun.symm.to_linear_map.continuous_on_pi this
                      have : IsComplete ( s : Set E )
                      exact complete_space_coe_iff_is_complete . 1 complete_space_congr U . 1 by infer_instance
                      exact this.is_closed
              have
                H₂
                  : ∀ f : E →ₗ[ 𝕜 ] 𝕜 , Continuous f
                  :=
                  by
                    intro f
                      have
                        : finrank 𝕜 f.ker = n ∨ finrank 𝕜 f.ker = n.succ
                          :=
                          by
                            have Z := f.finrank_range_add_finrank_ker
                              rw [ finrank_eq_card_basis ξ , hn ] at Z
                              by_cases' H : finrank 𝕜 f.range = 0
                              · right rw [ H ] at Z simpa using Z
                              ·
                                left
                                  have
                                    : finrank 𝕜 f.range = 1
                                      :=
                                      by
                                        refine' le_antisymmₓ _ zero_lt_iff.mpr H
                                          simpa [ finrank_self ] using f.range.finrank_le
                                  rw [ this , add_commₓ , Nat.add_one ] at Z
                                  exact Nat.succ.injₓ Z
                      have
                        : IsClosed ( f.ker : Set E )
                          :=
                          by
                            cases this
                              · exact H₁ _ this
                              ·
                                have
                                    : f.ker = ⊤
                                      :=
                                      by · apply eq_top_of_finrank_eq rw [ finrank_eq_card_basis ξ , hn , this ]
                                  simp [ this ]
                      exact LinearMap.continuous_iff_is_closed_ker . 2 this
              have
                : ∀ i : ι , ∃ C , 0 ≤ C ∧ ∀ x : E , ∥ ξ.equiv_fun x i ∥ ≤ C * ∥ x ∥
                  :=
                  by
                    intro i
                      let f : E →ₗ[ 𝕜 ] 𝕜 := LinearMap.proj i ∘ₗ ↑ ξ.equiv_fun
                      let f' : E →L[ 𝕜 ] 𝕜 := { f with cont := H₂ f }
                      exact ⟨ ∥ f' ∥ , norm_nonneg _ , fun x => ContinuousLinearMap.le_op_norm f' x ⟩
              choose C0 hC0 using this
              let C := ∑ i , C0 i
              have C_nonneg : 0 ≤ C := Finset.sum_nonneg fun i hi => hC0 i . 1
              have C0_le : ∀ i , C0 i ≤ C := fun i => Finset.single_le_sum fun j hj => hC0 j . 1 Finset.mem_univ _
              apply ξ.equiv_fun.to_linear_map.continuous_of_bound C fun x => _
              rw [ pi_semi_norm_le_iff ]
              · exact fun i => le_transₓ hC0 i . 2 x mul_le_mul_of_nonneg_right C0_le i norm_nonneg _
              · exact mul_nonneg C_nonneg norm_nonneg _

/--  Any linear map on a finite dimensional space over a complete field is continuous. -/
theorem LinearMap.continuous_of_finite_dimensional [FiniteDimensional 𝕜 E] (f : E →ₗ[𝕜] F') : Continuous f := by
  let b := Basis.ofVectorSpace 𝕜 E
  have A : Continuous b.equiv_fun := continuous_equiv_fun_basis b
  have B : Continuous (f.comp (b.equiv_fun.symm : (Basis.OfVectorSpaceIndex 𝕜 E → 𝕜) →ₗ[𝕜] E)) :=
    LinearMap.continuous_on_pi _
  have : Continuous (f.comp (b.equiv_fun.symm : (Basis.OfVectorSpaceIndex 𝕜 E → 𝕜) →ₗ[𝕜] E) ∘ b.equiv_fun) := B.comp A
  convert this
  ext x
  dsimp
  rw [Basis.equiv_fun_symm_apply, Basis.sum_repr]

theorem AffineMap.continuous_of_finite_dimensional {PE PF : Type _} [MetricSpace PE] [NormedAddTorsor E PE]
    [MetricSpace PF] [NormedAddTorsor F PF] [FiniteDimensional 𝕜 E] (f : PE →ᵃ[𝕜] PF) : Continuous f :=
  AffineMap.continuous_linear_iff.1 f.linear.continuous_of_finite_dimensional

namespace LinearMap

variable [FiniteDimensional 𝕜 E]

/--  The continuous linear map induced by a linear map on a finite dimensional space -/
def to_continuous_linear_map : (E →ₗ[𝕜] F') ≃ₗ[𝕜] E →L[𝕜] F' :=
  { toFun := fun f => ⟨f, f.continuous_of_finite_dimensional⟩, invFun := coeₓ, map_add' := fun f g => rfl,
    map_smul' := fun c f => rfl, left_inv := fun f => rfl, right_inv := fun f => ContinuousLinearMap.coe_injective rfl }

@[simp]
theorem coe_to_continuous_linear_map' (f : E →ₗ[𝕜] F') : ⇑f.to_continuous_linear_map = f :=
  rfl

@[simp]
theorem coe_to_continuous_linear_map (f : E →ₗ[𝕜] F') : (f.to_continuous_linear_map : E →ₗ[𝕜] F') = f :=
  rfl

@[simp]
theorem coe_to_continuous_linear_map_symm : ⇑(to_continuous_linear_map : (E →ₗ[𝕜] F') ≃ₗ[𝕜] E →L[𝕜] F').symm = coeₓ :=
  rfl

end LinearMap

/--  The continuous linear equivalence induced by a linear equivalence on a finite dimensional
space. -/
def LinearEquiv.toContinuousLinearEquiv [FiniteDimensional 𝕜 E] (e : E ≃ₗ[𝕜] F) : E ≃L[𝕜] F :=
  { e with continuous_to_fun := e.to_linear_map.continuous_of_finite_dimensional,
    continuous_inv_fun := by
      have : FiniteDimensional 𝕜 F := e.finite_dimensional
      exact e.symm.to_linear_map.continuous_of_finite_dimensional }

theorem LinearMap.exists_antilipschitz_with [FiniteDimensional 𝕜 E] (f : E →ₗ[𝕜] F) (hf : f.ker = ⊥) :
    ∃ K > 0, AntilipschitzWith K f := by
  cases subsingleton_or_nontrivial E <;> skip
  ·
    exact ⟨1, zero_lt_one, AntilipschitzWith.of_subsingleton⟩
  ·
    rw [LinearMap.ker_eq_bot] at hf
    let e : E ≃L[𝕜] f.range := (LinearEquiv.ofInjective f hf).toContinuousLinearEquiv
    exact ⟨_, e.nnnorm_symm_pos, e.antilipschitz⟩

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `LinearIndependent.eventually [])
  (Command.declSig
   [(Term.implicitBinder "{" [`ι] [] "}")
    (Term.instBinder "[" [] (Term.app `Fintype [`ι]) "]")
    (Term.implicitBinder "{" [`f] [":" (Term.arrow `ι "→" `E)] "}")
    (Term.explicitBinder "(" [`hf] [":" (Term.app `LinearIndependent [`𝕜 `f])] [] ")")]
   (Term.typeSpec
    ":"
    (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
     "∀ᶠ"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `g)] []))
     " in "
     (Term.app (Topology.Basic.term𝓝 "𝓝") [`f])
     ", "
     (Term.app `LinearIndependent [`𝕜 `g]))))
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
         ["[" [(Tactic.simpLemma [] [] `Fintype.linear_independent_iff')] "]"]
         [(Tactic.location "at" (Tactic.locationHyp [`hf] ["⊢"]))])
        [])
       (group
        (Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] (Term.app `LinearMap.exists_antilipschitz_with [(Term.hole "_") `hf]))]
         ["with"
          (Tactic.rcasesPat.tuple
           "⟨"
           [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `K)]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `K0)]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hK)]) [])]
           "⟩")])
        [])
       (group
        (Tactic.have''
         "have"
         []
         [(Term.typeSpec
           ":"
           (Term.app
            `tendsto
            [(Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`g] [(Term.typeSpec ":" (Term.arrow `ι "→" `E))])]
               "=>"
               (Algebra.BigOperators.Basic.«term∑_,_»
                "∑"
                (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                ", "
                (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» (Term.app `g [`i]) "-" (Term.app `f [`i])) "∥"))))
             (Term.app (Topology.Basic.term𝓝 "𝓝") [`f])
             («term_$__»
              (Topology.Basic.term𝓝 "𝓝")
              "$"
              (Algebra.BigOperators.Basic.«term∑_,_»
               "∑"
               (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
               ", "
               (Analysis.Normed.Group.Basic.«term∥_∥»
                "∥"
                («term_-_» (Term.app `f [`i]) "-" (Term.app `f [`i]))
                "∥")))]))])
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.app
          `tendsto_finset_sum
          [(Term.hole "_")
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`i `hi] [])]
             "=>"
             («term_$__»
              `tendsto.norm
              "$"
              (Term.app
               (Term.proj
                (Term.app (Term.proj (Term.app `continuous_apply [`i]) "." `Tendsto) [(Term.hole "_")])
                "."
                `sub)
               [`tendsto_const_nhds]))))]))
        [])
       (group
        (Tactic.simp
         "simp"
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `sub_self)
           ","
           (Tactic.simpLemma [] [] `norm_zero)
           ","
           (Tactic.simpLemma [] [] `Finset.sum_const_zero)]
          "]"]
         [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.app
          (Term.proj
           (Term.app
            `this.eventually
            [(«term_$__» `gt_mem_nhds "$" (Term.app (Term.proj `inv_pos "." (fieldIdx "2")) [`K0]))])
           "."
           `mono)
          [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`g `hg] [])] "=>" (Term.hole "_")))]))
        [])
       (group
        (Tactic.replace'
         "replace"
         [`hg []]
         [(Term.typeSpec
           ":"
           («term_<_»
            (Algebra.BigOperators.Basic.«term∑_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
             ", "
             (Term.app `nnnorm [(«term_-_» (Term.app `g [`i]) "-" (Term.app `f [`i]))]))
            "<"
            (Init.Logic.«term_⁻¹» `K "⁻¹")))])
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `Nnreal.coe_lt_coe)] "]") [])
                  [])
                 (group (Tactic.pushCast "push_cast" [] []) [])
                 (group (Tactic.exact "exact" `hg) [])])))
             [])])))
        [])
       (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `LinearMap.ker_eq_bot)] "]") []) [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.proj
          (Term.app
           `hK.add_sub_lipschitz_with
           [(«term_$__»
             `LipschitzWith.of_dist_le_mul
             "$"
             (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`v `u] [])] "=>" (Term.hole "_"))))
            `hg])
          "."
          `Injective))
        [])
       (group
        (Tactic.simp
         "simp"
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `dist_eq_norm)
           ","
           (Tactic.simpLemma [] [] `LinearMap.lsum_apply)
           ","
           (Tactic.simpLemma [] [] `Pi.sub_apply)
           ","
           (Tactic.simpLemma [] [] `LinearMap.sum_apply)
           ","
           (Tactic.simpLemma [] [] `LinearMap.comp_apply)
           ","
           (Tactic.simpLemma [] [] `LinearMap.proj_apply)
           ","
           (Tactic.simpLemma [] [] `LinearMap.smul_right_apply)
           ","
           (Tactic.simpLemma [] [] `LinearMap.id_apply)
           ","
           (Tactic.simpLemma [] ["←"] `Finset.sum_sub_distrib)
           ","
           (Tactic.simpLemma [] ["←"] `smul_sub)
           ","
           (Tactic.simpLemma [] ["←"] `sub_smul)
           ","
           (Tactic.simpLemma [] [] `Nnreal.coe_sum)
           ","
           (Tactic.simpLemma [] [] `coe_nnnorm)
           ","
           (Tactic.simpLemma [] [] `Finset.sum_mul)]
          "]"]
         [])
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.app
          `norm_sum_le_of_le
          [(Term.hole "_")
           (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i (Term.hole "_")] [])] "=>" (Term.hole "_")))]))
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `norm_smul) "," (Tactic.rwRule [] `mul_commₓ)] "]")
         [])
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.app
          `mul_le_mul_of_nonneg_left
          [(Term.app `norm_le_pi_norm [(«term_-_» `v "-" `u) `i]) (Term.app `norm_nonneg [(Term.hole "_")])]))
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
        ["[" [(Tactic.simpLemma [] [] `Fintype.linear_independent_iff')] "]"]
        [(Tactic.location "at" (Tactic.locationHyp [`hf] ["⊢"]))])
       [])
      (group
       (Tactic.rcases
        "rcases"
        [(Tactic.casesTarget [] (Term.app `LinearMap.exists_antilipschitz_with [(Term.hole "_") `hf]))]
        ["with"
         (Tactic.rcasesPat.tuple
          "⟨"
          [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `K)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `K0)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hK)]) [])]
          "⟩")])
       [])
      (group
       (Tactic.have''
        "have"
        []
        [(Term.typeSpec
          ":"
          (Term.app
           `tendsto
           [(Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`g] [(Term.typeSpec ":" (Term.arrow `ι "→" `E))])]
              "=>"
              (Algebra.BigOperators.Basic.«term∑_,_»
               "∑"
               (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
               ", "
               (Analysis.Normed.Group.Basic.«term∥_∥» "∥" («term_-_» (Term.app `g [`i]) "-" (Term.app `f [`i])) "∥"))))
            (Term.app (Topology.Basic.term𝓝 "𝓝") [`f])
            («term_$__»
             (Topology.Basic.term𝓝 "𝓝")
             "$"
             (Algebra.BigOperators.Basic.«term∑_,_»
              "∑"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
              ", "
              (Analysis.Normed.Group.Basic.«term∥_∥»
               "∥"
               («term_-_» (Term.app `f [`i]) "-" (Term.app `f [`i]))
               "∥")))]))])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.app
         `tendsto_finset_sum
         [(Term.hole "_")
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`i `hi] [])]
            "=>"
            («term_$__»
             `tendsto.norm
             "$"
             (Term.app
              (Term.proj
               (Term.app (Term.proj (Term.app `continuous_apply [`i]) "." `Tendsto) [(Term.hole "_")])
               "."
               `sub)
              [`tendsto_const_nhds]))))]))
       [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `sub_self)
          ","
          (Tactic.simpLemma [] [] `norm_zero)
          ","
          (Tactic.simpLemma [] [] `Finset.sum_const_zero)]
         "]"]
        [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         (Term.proj
          (Term.app
           `this.eventually
           [(«term_$__» `gt_mem_nhds "$" (Term.app (Term.proj `inv_pos "." (fieldIdx "2")) [`K0]))])
          "."
          `mono)
         [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`g `hg] [])] "=>" (Term.hole "_")))]))
       [])
      (group
       (Tactic.replace'
        "replace"
        [`hg []]
        [(Term.typeSpec
          ":"
          («term_<_»
           (Algebra.BigOperators.Basic.«term∑_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
            ", "
            (Term.app `nnnorm [(«term_-_» (Term.app `g [`i]) "-" (Term.app `f [`i]))]))
           "<"
           (Init.Logic.«term_⁻¹» `K "⁻¹")))])
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `Nnreal.coe_lt_coe)] "]") [])
                 [])
                (group (Tactic.pushCast "push_cast" [] []) [])
                (group (Tactic.exact "exact" `hg) [])])))
            [])])))
       [])
      (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `LinearMap.ker_eq_bot)] "]") []) [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.proj
         (Term.app
          `hK.add_sub_lipschitz_with
          [(«term_$__»
            `LipschitzWith.of_dist_le_mul
            "$"
            (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`v `u] [])] "=>" (Term.hole "_"))))
           `hg])
         "."
         `Injective))
       [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `dist_eq_norm)
          ","
          (Tactic.simpLemma [] [] `LinearMap.lsum_apply)
          ","
          (Tactic.simpLemma [] [] `Pi.sub_apply)
          ","
          (Tactic.simpLemma [] [] `LinearMap.sum_apply)
          ","
          (Tactic.simpLemma [] [] `LinearMap.comp_apply)
          ","
          (Tactic.simpLemma [] [] `LinearMap.proj_apply)
          ","
          (Tactic.simpLemma [] [] `LinearMap.smul_right_apply)
          ","
          (Tactic.simpLemma [] [] `LinearMap.id_apply)
          ","
          (Tactic.simpLemma [] ["←"] `Finset.sum_sub_distrib)
          ","
          (Tactic.simpLemma [] ["←"] `smul_sub)
          ","
          (Tactic.simpLemma [] ["←"] `sub_smul)
          ","
          (Tactic.simpLemma [] [] `Nnreal.coe_sum)
          ","
          (Tactic.simpLemma [] [] `coe_nnnorm)
          ","
          (Tactic.simpLemma [] [] `Finset.sum_mul)]
         "]"]
        [])
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         `norm_sum_le_of_le
         [(Term.hole "_")
          (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i (Term.hole "_")] [])] "=>" (Term.hole "_")))]))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `norm_smul) "," (Tactic.rwRule [] `mul_commₓ)] "]")
        [])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.app
         `mul_le_mul_of_nonneg_left
         [(Term.app `norm_le_pi_norm [(«term_-_» `v "-" `u) `i]) (Term.app `norm_nonneg [(Term.hole "_")])]))
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
    `mul_le_mul_of_nonneg_left
    [(Term.app `norm_le_pi_norm [(«term_-_» `v "-" `u) `i]) (Term.app `norm_nonneg [(Term.hole "_")])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `mul_le_mul_of_nonneg_left
   [(Term.app `norm_le_pi_norm [(«term_-_» `v "-" `u) `i]) (Term.app `norm_nonneg [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `norm_nonneg [(Term.hole "_")]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `norm_le_pi_norm [(«term_-_» `v "-" `u) `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  («term_-_» `v "-" `u)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `u
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  `v
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(«term_-_» `v "-" `u) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `norm_le_pi_norm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `norm_le_pi_norm [(Term.paren "(" [(«term_-_» `v "-" `u) []] ")") `i]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mul_le_mul_of_nonneg_left
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `norm_smul) "," (Tactic.rwRule [] `mul_commₓ)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mul_commₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `norm_smul
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    `norm_sum_le_of_le
    [(Term.hole "_")
     (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i (Term.hole "_")] [])] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `norm_sum_le_of_le
   [(Term.hole "_")
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i (Term.hole "_")] [])] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i (Term.hole "_")] [])] "=>" (Term.hole "_")))
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident.antiquot'
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
  `norm_sum_le_of_le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["["
    [(Tactic.simpLemma [] [] `dist_eq_norm)
     ","
     (Tactic.simpLemma [] [] `LinearMap.lsum_apply)
     ","
     (Tactic.simpLemma [] [] `Pi.sub_apply)
     ","
     (Tactic.simpLemma [] [] `LinearMap.sum_apply)
     ","
     (Tactic.simpLemma [] [] `LinearMap.comp_apply)
     ","
     (Tactic.simpLemma [] [] `LinearMap.proj_apply)
     ","
     (Tactic.simpLemma [] [] `LinearMap.smul_right_apply)
     ","
     (Tactic.simpLemma [] [] `LinearMap.id_apply)
     ","
     (Tactic.simpLemma [] ["←"] `Finset.sum_sub_distrib)
     ","
     (Tactic.simpLemma [] ["←"] `smul_sub)
     ","
     (Tactic.simpLemma [] ["←"] `sub_smul)
     ","
     (Tactic.simpLemma [] [] `Nnreal.coe_sum)
     ","
     (Tactic.simpLemma [] [] `coe_nnnorm)
     ","
     (Tactic.simpLemma [] [] `Finset.sum_mul)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.sum_mul
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `coe_nnnorm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Nnreal.coe_sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `sub_smul
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `smul_sub
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.sum_sub_distrib
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `LinearMap.id_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `LinearMap.smul_right_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `LinearMap.proj_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `LinearMap.comp_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `LinearMap.sum_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Pi.sub_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `LinearMap.lsum_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `dist_eq_norm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.proj
    (Term.app
     `hK.add_sub_lipschitz_with
     [(«term_$__»
       `LipschitzWith.of_dist_le_mul
       "$"
       (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`v `u] [])] "=>" (Term.hole "_"))))
      `hg])
    "."
    `Injective))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj
   (Term.app
    `hK.add_sub_lipschitz_with
    [(«term_$__»
      `LipschitzWith.of_dist_le_mul
      "$"
      (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`v `u] [])] "=>" (Term.hole "_"))))
     `hg])
   "."
   `Injective)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app
   `hK.add_sub_lipschitz_with
   [(«term_$__»
     `LipschitzWith.of_dist_le_mul
     "$"
     (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`v `u] [])] "=>" (Term.hole "_"))))
    `hg])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hg
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
   `LipschitzWith.of_dist_le_mul
   "$"
   (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`v `u] [])] "=>" (Term.hole "_"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`v `u] [])] "=>" (Term.hole "_")))
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  `LipschitzWith.of_dist_le_mul
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term_$__»
   `LipschitzWith.of_dist_le_mul
   "$"
   (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`v `u] [])] "=>" (Term.hole "_"))))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hK.add_sub_lipschitz_with
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `hK.add_sub_lipschitz_with
   [(Term.paren
     "("
     [(«term_$__»
       `LipschitzWith.of_dist_le_mul
       "$"
       (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`v `u] [])] "=>" (Term.hole "_"))))
      []]
     ")")
    `hg])
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `LinearMap.ker_eq_bot)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `LinearMap.ker_eq_bot
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `Nnreal.coe_lt_coe)] "]") []) [])
           (group (Tactic.pushCast "push_cast" [] []) [])
           (group (Tactic.exact "exact" `hg) [])])))
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
     [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `Nnreal.coe_lt_coe)] "]") []) [])
      (group (Tactic.pushCast "push_cast" [] []) [])
      (group (Tactic.exact "exact" `hg) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" `hg)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.pushCast "push_cast" [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.pushCast', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `Nnreal.coe_lt_coe)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Nnreal.coe_lt_coe
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.replace'
   "replace"
   [`hg []]
   [(Term.typeSpec
     ":"
     («term_<_»
      (Algebra.BigOperators.Basic.«term∑_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
       ", "
       (Term.app `nnnorm [(«term_-_» (Term.app `g [`i]) "-" (Term.app `f [`i]))]))
      "<"
      (Init.Logic.«term_⁻¹» `K "⁻¹")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.replace'', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_<_»
   (Algebra.BigOperators.Basic.«term∑_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
    ", "
    (Term.app `nnnorm [(«term_-_» (Term.app `g [`i]) "-" (Term.app `f [`i]))]))
   "<"
   (Init.Logic.«term_⁻¹» `K "⁻¹"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_⁻¹» `K "⁻¹")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_⁻¹»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `K
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Algebra.BigOperators.Basic.«term∑_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
   ", "
   (Term.app `nnnorm [(«term_-_» (Term.app `g [`i]) "-" (Term.app `f [`i]))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `nnnorm [(«term_-_» (Term.app `g [`i]) "-" (Term.app `f [`i]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_-_» (Term.app `g [`i]) "-" (Term.app `f [`i]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  (Term.app `g [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `g
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term_-_» (Term.app `g [`i]) "-" (Term.app `f [`i])) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `nnnorm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
protected
  theorem
    LinearIndependent.eventually
    { ι } [ Fintype ι ] { f : ι → E } ( hf : LinearIndependent 𝕜 f ) : ∀ᶠ g in 𝓝 f , LinearIndependent 𝕜 g
    :=
      by
        simp only [ Fintype.linear_independent_iff' ] at hf ⊢
          rcases LinearMap.exists_antilipschitz_with _ hf with ⟨ K , K0 , hK ⟩
          have : tendsto fun g : ι → E => ∑ i , ∥ g i - f i ∥ 𝓝 f 𝓝 $ ∑ i , ∥ f i - f i ∥
          exact tendsto_finset_sum _ fun i hi => tendsto.norm $ continuous_apply i . Tendsto _ . sub tendsto_const_nhds
          simp only [ sub_self , norm_zero , Finset.sum_const_zero ] at this
          refine' this.eventually gt_mem_nhds $ inv_pos . 2 K0 . mono fun g hg => _
          replace hg : ∑ i , nnnorm g i - f i < K ⁻¹
          · · rw [ ← Nnreal.coe_lt_coe ] push_cast exact hg
          rw [ LinearMap.ker_eq_bot ]
          refine' hK.add_sub_lipschitz_with LipschitzWith.of_dist_le_mul $ fun v u => _ hg . Injective
          simp
            only
            [
              dist_eq_norm
                ,
                LinearMap.lsum_apply
                ,
                Pi.sub_apply
                ,
                LinearMap.sum_apply
                ,
                LinearMap.comp_apply
                ,
                LinearMap.proj_apply
                ,
                LinearMap.smul_right_apply
                ,
                LinearMap.id_apply
                ,
                ← Finset.sum_sub_distrib
                ,
                ← smul_sub
                ,
                ← sub_smul
                ,
                Nnreal.coe_sum
                ,
                coe_nnnorm
                ,
                Finset.sum_mul
              ]
          refine' norm_sum_le_of_le _ fun i _ => _
          rw [ norm_smul , mul_commₓ ]
          exact mul_le_mul_of_nonneg_left norm_le_pi_norm v - u i norm_nonneg _

theorem is_open_set_of_linear_independent {ι : Type _} [Fintype ι] : IsOpen { f : ι → E | LinearIndependent 𝕜 f } :=
  is_open_iff_mem_nhds.2 $ fun f => LinearIndependent.eventually

theorem is_open_set_of_nat_le_rank (n : ℕ) : IsOpen { f : E →L[𝕜] F | ↑n ≤ rank (f : E →ₗ[𝕜] F) } := by
  simp only [le_rank_iff_exists_linear_independent_finset, set_of_exists, ← exists_prop]
  refine' is_open_bUnion fun t ht => _
  have : Continuous fun f : E →L[𝕜] F => fun x : (t : Set E) => f x
  exact continuous_pi fun x => (ContinuousLinearMap.apply 𝕜 F (x : E)).Continuous
  exact is_open_set_of_linear_independent.preimage this

/--  Two finite-dimensional normed spaces are continuously linearly equivalent if they have the same
(finite) dimension. -/
theorem FiniteDimensional.nonempty_continuous_linear_equiv_of_finrank_eq [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (cond : finrank 𝕜 E = finrank 𝕜 F) : Nonempty (E ≃L[𝕜] F) :=
  (nonempty_linear_equiv_of_finrank_eq cond).map LinearEquiv.toContinuousLinearEquiv

/--  Two finite-dimensional normed spaces are continuously linearly equivalent if and only if they
have the same (finite) dimension. -/
theorem FiniteDimensional.nonempty_continuous_linear_equiv_iff_finrank_eq [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 F] : Nonempty (E ≃L[𝕜] F) ↔ finrank 𝕜 E = finrank 𝕜 F :=
  ⟨fun ⟨h⟩ => h.to_linear_equiv.finrank_eq, fun h => FiniteDimensional.nonempty_continuous_linear_equiv_of_finrank_eq h⟩

/--  A continuous linear equivalence between two finite-dimensional normed spaces of the same
(finite) dimension. -/
def ContinuousLinearEquiv.ofFinrankEq [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (cond : finrank 𝕜 E = finrank 𝕜 F) : E ≃L[𝕜] F :=
  (linear_equiv.of_finrank_eq E F cond).toContinuousLinearEquiv

variable {ι : Type _} [Fintype ι]

/--  Construct a continuous linear map given the value at a finite basis. -/
def Basis.constrL (v : Basis ι 𝕜 E) (f : ι → F) : E →L[𝕜] F := by
  have : FiniteDimensional 𝕜 E := FiniteDimensional.of_fintype_basis v <;> exact (v.constr 𝕜 f).toContinuousLinearMap

@[simp, norm_cast]
theorem Basis.coe_constrL (v : Basis ι 𝕜 E) (f : ι → F) : (v.constrL f : E →ₗ[𝕜] F) = v.constr 𝕜 f :=
  rfl

/--  The continuous linear equivalence between a vector space over `𝕜` with a finite basis and
functions from its basis indexing type to `𝕜`. -/
def Basis.equivFunL (v : Basis ι 𝕜 E) : E ≃L[𝕜] ι → 𝕜 :=
  { v.equiv_fun with
    continuous_to_fun := by
      have : FiniteDimensional 𝕜 E := FiniteDimensional.of_fintype_basis v
      exact v.equiv_fun.to_linear_map.continuous_of_finite_dimensional,
    continuous_inv_fun := by
      change Continuous v.equiv_fun.symm.to_fun
      exact v.equiv_fun.symm.to_linear_map.continuous_of_finite_dimensional }

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
  (Command.declId `Basis.constrL_apply [])
  (Command.declSig
   [(Term.explicitBinder "(" [`v] [":" (Term.app `Basis [`ι `𝕜 `E])] [] ")")
    (Term.explicitBinder "(" [`f] [":" (Term.arrow `ι "→" `F)] [] ")")
    (Term.explicitBinder "(" [`e] [":" `E] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app (Term.app `v.constrL [`f]) [`e])
     "="
     (Algebra.BigOperators.Basic.«term∑_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
      ", "
      (Algebra.Group.Defs.«term_•_» (Term.app `v.equiv_fun [`e `i]) " • " (Term.app `f [`i]))))))
  (Command.declValSimple ":=" (Term.app `v.constr_apply_fintype [`𝕜 (Term.hole "_") (Term.hole "_")]) [])
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
  (Term.app `v.constr_apply_fintype [`𝕜 (Term.hole "_") (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `𝕜
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `v.constr_apply_fintype
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.app (Term.app `v.constrL [`f]) [`e])
   "="
   (Algebra.BigOperators.Basic.«term∑_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
    ", "
    (Algebra.Group.Defs.«term_•_» (Term.app `v.equiv_fun [`e `i]) " • " (Term.app `f [`i]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
   ", "
   (Algebra.Group.Defs.«term_•_» (Term.app `v.equiv_fun [`e `i]) " • " (Term.app `f [`i])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.Group.Defs.«term_•_» (Term.app `v.equiv_fun [`e `i]) " • " (Term.app `f [`i]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
  (Term.app `v.equiv_fun [`e `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `e
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `v.equiv_fun
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1022, (some 1023, term) <=? (some 73, term)
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
@[ simp ]
  theorem
    Basis.constrL_apply
    ( v : Basis ι 𝕜 E ) ( f : ι → F ) ( e : E ) : v.constrL f e = ∑ i , v.equiv_fun e i • f i
    := v.constr_apply_fintype 𝕜 _ _

@[simp]
theorem Basis.constrL_basis (v : Basis ι 𝕜 E) (f : ι → F) (i : ι) : (v.constrL f) (v i) = f i :=
  v.constr_basis 𝕜 _ _

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `Basis.sup_norm_le_norm [])
  (Command.declSig
   [(Term.explicitBinder "(" [`v] [":" (Term.app `Basis [`ι `𝕜 `E])] [] ")")]
   (Term.typeSpec
    ":"
    (Mathlib.ExtendedBinder.«term∃___,_»
     "∃"
     `C
     (Mathlib.ExtendedBinder.«binderTerm>_»
      ">"
      (Term.paren "(" [(numLit "0") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")"))
     ","
     (Term.forall
      "∀"
      [(Term.simpleBinder [`e] [(Term.typeSpec ":" `E)])]
      ","
      («term_≤_»
       (Algebra.BigOperators.Basic.«term∑_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
        ", "
        (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `v.equiv_fun [`e `i]) "∥"))
       "≤"
       (Finset.Data.Finset.Fold.«term_*_» `C "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥")))))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.set "set" `φ [] ":=" `v.equiv_funL.to_continuous_linear_map []) [])
       (group
        (Tactic.set
         "set"
         `C
         []
         ":="
         (Finset.Data.Finset.Fold.«term_*_»
          (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `φ "∥")
          "*"
          (Term.app `Fintype.card [`ι]))
         [])
        [])
       (group
        (Tactic.use
         "use"
         [(Term.app `max [`C (numLit "1")])
          ","
          (Term.app `lt_of_lt_of_leₓ [`zero_lt_one (Term.app `le_max_rightₓ [`C (numLit "1")])])])
        [])
       (group (Tactic.intro "intro" [`e]) [])
       (group
        (tacticCalc_
         "calc"
         [(calcStep
           («term_≤_»
            (Algebra.BigOperators.Basic.«term∑_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
             ", "
             (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `φ [`e `i]) "∥"))
            "≤"
            (Algebra.BigOperators.Basic.«term∑_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" `ι]))
             ", "
             (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `φ [`e]) "∥")))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.apply "apply" `Finset.sum_le_sum) [])
               (group
                (Tactic.exact
                 "exact"
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`i `hi] [])]
                   "=>"
                   (Term.app `norm_le_pi_norm [(Term.app `φ [`e]) `i]))))
                [])]))))
          (calcStep
           («term_=_»
            (Term.hole "_")
            "="
            (Finset.Data.Finset.Fold.«term_*_»
             (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `φ [`e]) "∥")
             "*"
             (Term.app `Fintype.card [`ι])))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.simpa
                 "simpa"
                 []
                 ["only"]
                 ["["
                  [(Tactic.simpLemma [] [] `mul_commₓ)
                   ","
                   (Tactic.simpLemma [] [] `Finset.sum_const)
                   ","
                   (Tactic.simpLemma [] [] `nsmul_eq_mul)]
                  "]"]
                 []
                 [])
                [])]))))
          (calcStep
           («term_≤_»
            (Term.hole "_")
            "≤"
            (Finset.Data.Finset.Fold.«term_*_»
             (Finset.Data.Finset.Fold.«term_*_»
              (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `φ "∥")
              "*"
              (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥"))
             "*"
             (Term.app `Fintype.card [`ι])))
           ":="
           (Term.app
            `mul_le_mul_of_nonneg_right
            [(Term.app `φ.le_op_norm [`e]) (Term.proj (Term.app `Fintype.card [`ι]) "." `cast_nonneg)]))
          (calcStep
           («term_=_»
            (Term.hole "_")
            "="
            (Finset.Data.Finset.Fold.«term_*_»
             (Finset.Data.Finset.Fold.«term_*_»
              (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `φ "∥")
              "*"
              (Term.app `Fintype.card [`ι]))
             "*"
             (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥")))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.Ring.tacticRing "ring") [])]))))
          (calcStep
           («term_≤_»
            (Term.hole "_")
            "≤"
            (Finset.Data.Finset.Fold.«term_*_»
             (Term.app `max [`C (numLit "1")])
             "*"
             (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥")))
           ":="
           (Term.app
            `mul_le_mul_of_nonneg_right
            [(Term.app `le_max_leftₓ [(Term.hole "_") (Term.hole "_")]) (Term.app `norm_nonneg [(Term.hole "_")])]))])
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
     [(group (Tactic.set "set" `φ [] ":=" `v.equiv_funL.to_continuous_linear_map []) [])
      (group
       (Tactic.set
        "set"
        `C
        []
        ":="
        (Finset.Data.Finset.Fold.«term_*_»
         (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `φ "∥")
         "*"
         (Term.app `Fintype.card [`ι]))
        [])
       [])
      (group
       (Tactic.use
        "use"
        [(Term.app `max [`C (numLit "1")])
         ","
         (Term.app `lt_of_lt_of_leₓ [`zero_lt_one (Term.app `le_max_rightₓ [`C (numLit "1")])])])
       [])
      (group (Tactic.intro "intro" [`e]) [])
      (group
       (tacticCalc_
        "calc"
        [(calcStep
          («term_≤_»
           (Algebra.BigOperators.Basic.«term∑_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
            ", "
            (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `φ [`e `i]) "∥"))
           "≤"
           (Algebra.BigOperators.Basic.«term∑_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" `ι]))
            ", "
            (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `φ [`e]) "∥")))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.apply "apply" `Finset.sum_le_sum) [])
              (group
               (Tactic.exact
                "exact"
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`i `hi] [])]
                  "=>"
                  (Term.app `norm_le_pi_norm [(Term.app `φ [`e]) `i]))))
               [])]))))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Finset.Data.Finset.Fold.«term_*_»
            (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `φ [`e]) "∥")
            "*"
            (Term.app `Fintype.card [`ι])))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.simpa
                "simpa"
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `mul_commₓ)
                  ","
                  (Tactic.simpLemma [] [] `Finset.sum_const)
                  ","
                  (Tactic.simpLemma [] [] `nsmul_eq_mul)]
                 "]"]
                []
                [])
               [])]))))
         (calcStep
          («term_≤_»
           (Term.hole "_")
           "≤"
           (Finset.Data.Finset.Fold.«term_*_»
            (Finset.Data.Finset.Fold.«term_*_»
             (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `φ "∥")
             "*"
             (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥"))
            "*"
            (Term.app `Fintype.card [`ι])))
          ":="
          (Term.app
           `mul_le_mul_of_nonneg_right
           [(Term.app `φ.le_op_norm [`e]) (Term.proj (Term.app `Fintype.card [`ι]) "." `cast_nonneg)]))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Finset.Data.Finset.Fold.«term_*_»
            (Finset.Data.Finset.Fold.«term_*_»
             (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `φ "∥")
             "*"
             (Term.app `Fintype.card [`ι]))
            "*"
            (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥")))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.Ring.tacticRing "ring") [])]))))
         (calcStep
          («term_≤_»
           (Term.hole "_")
           "≤"
           (Finset.Data.Finset.Fold.«term_*_»
            (Term.app `max [`C (numLit "1")])
            "*"
            (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥")))
          ":="
          (Term.app
           `mul_le_mul_of_nonneg_right
           [(Term.app `le_max_leftₓ [(Term.hole "_") (Term.hole "_")]) (Term.app `norm_nonneg [(Term.hole "_")])]))])
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
      (Algebra.BigOperators.Basic.«term∑_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
       ", "
       (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `φ [`e `i]) "∥"))
      "≤"
      (Algebra.BigOperators.Basic.«term∑_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" `ι]))
       ", "
       (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `φ [`e]) "∥")))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.apply "apply" `Finset.sum_le_sum) [])
         (group
          (Tactic.exact
           "exact"
           (Term.fun
            "fun"
            (Term.basicFun [(Term.simpleBinder [`i `hi] [])] "=>" (Term.app `norm_le_pi_norm [(Term.app `φ [`e]) `i]))))
          [])]))))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Finset.Data.Finset.Fold.«term_*_»
       (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `φ [`e]) "∥")
       "*"
       (Term.app `Fintype.card [`ι])))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.simpa
           "simpa"
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `mul_commₓ)
             ","
             (Tactic.simpLemma [] [] `Finset.sum_const)
             ","
             (Tactic.simpLemma [] [] `nsmul_eq_mul)]
            "]"]
           []
           [])
          [])]))))
    (calcStep
     («term_≤_»
      (Term.hole "_")
      "≤"
      (Finset.Data.Finset.Fold.«term_*_»
       (Finset.Data.Finset.Fold.«term_*_»
        (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `φ "∥")
        "*"
        (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥"))
       "*"
       (Term.app `Fintype.card [`ι])))
     ":="
     (Term.app
      `mul_le_mul_of_nonneg_right
      [(Term.app `φ.le_op_norm [`e]) (Term.proj (Term.app `Fintype.card [`ι]) "." `cast_nonneg)]))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Finset.Data.Finset.Fold.«term_*_»
       (Finset.Data.Finset.Fold.«term_*_»
        (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `φ "∥")
        "*"
        (Term.app `Fintype.card [`ι]))
       "*"
       (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥")))
     ":="
     (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.Ring.tacticRing "ring") [])]))))
    (calcStep
     («term_≤_»
      (Term.hole "_")
      "≤"
      (Finset.Data.Finset.Fold.«term_*_»
       (Term.app `max [`C (numLit "1")])
       "*"
       (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥")))
     ":="
     (Term.app
      `mul_le_mul_of_nonneg_right
      [(Term.app `le_max_leftₓ [(Term.hole "_") (Term.hole "_")]) (Term.app `norm_nonneg [(Term.hole "_")])]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticCalc_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `mul_le_mul_of_nonneg_right
   [(Term.app `le_max_leftₓ [(Term.hole "_") (Term.hole "_")]) (Term.app `norm_nonneg [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `norm_nonneg [(Term.hole "_")]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `le_max_leftₓ [(Term.hole "_") (Term.hole "_")])
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
  `le_max_leftₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `le_max_leftₓ [(Term.hole "_") (Term.hole "_")]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mul_le_mul_of_nonneg_right
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (Term.hole "_")
   "≤"
   (Finset.Data.Finset.Fold.«term_*_»
    (Term.app `max [`C (numLit "1")])
    "*"
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   (Term.app `max [`C (numLit "1")])
   "*"
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `e
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.app `max [`C (numLit "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `C
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `max
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.Ring.tacticRing "ring") [])])))
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.hole "_")
   "="
   (Finset.Data.Finset.Fold.«term_*_»
    (Finset.Data.Finset.Fold.«term_*_»
     (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `φ "∥")
     "*"
     (Term.app `Fintype.card [`ι]))
    "*"
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   (Finset.Data.Finset.Fold.«term_*_»
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `φ "∥")
    "*"
    (Term.app `Fintype.card [`ι]))
   "*"
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `e
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Finset.Data.Finset.Fold.«term_*_»
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `φ "∥")
   "*"
   (Term.app `Fintype.card [`ι]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Fintype.card [`ι])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ι
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Fintype.card
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `φ "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `φ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_»
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `φ "∥")
   "*"
   (Term.app `Fintype.card [`ι]))
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
  (Term.app
   `mul_le_mul_of_nonneg_right
   [(Term.app `φ.le_op_norm [`e]) (Term.proj (Term.app `Fintype.card [`ι]) "." `cast_nonneg)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `Fintype.card [`ι]) "." `cast_nonneg)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `Fintype.card [`ι])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ι
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Fintype.card
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Fintype.card [`ι]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `φ.le_op_norm [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `e
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `φ.le_op_norm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `φ.le_op_norm [`e]) []] ")")
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
    (Finset.Data.Finset.Fold.«term_*_»
     (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `φ "∥")
     "*"
     (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥"))
    "*"
    (Term.app `Fintype.card [`ι])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   (Finset.Data.Finset.Fold.«term_*_»
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `φ "∥")
    "*"
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥"))
   "*"
   (Term.app `Fintype.card [`ι]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Fintype.card [`ι])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ι
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Fintype.card
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Finset.Data.Finset.Fold.«term_*_»
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `φ "∥")
   "*"
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `e
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `φ "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `φ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_»
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `φ "∥")
   "*"
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥"))
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
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.simpa
        "simpa"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `mul_commₓ)
          ","
          (Tactic.simpLemma [] [] `Finset.sum_const)
          ","
          (Tactic.simpLemma [] [] `nsmul_eq_mul)]
         "]"]
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
  (Tactic.simpa
   "simpa"
   []
   ["only"]
   ["["
    [(Tactic.simpLemma [] [] `mul_commₓ)
     ","
     (Tactic.simpLemma [] [] `Finset.sum_const)
     ","
     (Tactic.simpLemma [] [] `nsmul_eq_mul)]
    "]"]
   []
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpa', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `nsmul_eq_mul
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.sum_const
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mul_commₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.hole "_")
   "="
   (Finset.Data.Finset.Fold.«term_*_»
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `φ [`e]) "∥")
    "*"
    (Term.app `Fintype.card [`ι])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `φ [`e]) "∥")
   "*"
   (Term.app `Fintype.card [`ι]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Fintype.card [`ι])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ι
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Fintype.card
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `φ [`e]) "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `φ [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `e
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `φ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.apply "apply" `Finset.sum_le_sum) [])
      (group
       (Tactic.exact
        "exact"
        (Term.fun
         "fun"
         (Term.basicFun [(Term.simpleBinder [`i `hi] [])] "=>" (Term.app `norm_le_pi_norm [(Term.app `φ [`e]) `i]))))
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
   (Term.fun
    "fun"
    (Term.basicFun [(Term.simpleBinder [`i `hi] [])] "=>" (Term.app `norm_le_pi_norm [(Term.app `φ [`e]) `i]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun [(Term.simpleBinder [`i `hi] [])] "=>" (Term.app `norm_le_pi_norm [(Term.app `φ [`e]) `i])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `norm_le_pi_norm [(Term.app `φ [`e]) `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `φ [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `e
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `φ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `φ [`e]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `norm_le_pi_norm
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
  (Tactic.apply "apply" `Finset.sum_le_sum)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.sum_le_sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (Algebra.BigOperators.Basic.«term∑_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
    ", "
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `φ [`e `i]) "∥"))
   "≤"
   (Algebra.BigOperators.Basic.«term∑_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" `ι]))
    ", "
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `φ [`e]) "∥")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" `ι]))
   ", "
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `φ [`e]) "∥"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `φ [`e]) "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `φ [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `e
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `φ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
  Basis.sup_norm_le_norm
  ( v : Basis ι 𝕜 E ) : ∃ C > ( 0 : ℝ ) , ∀ e : E , ∑ i , ∥ v.equiv_fun e i ∥ ≤ C * ∥ e ∥
  :=
    by
      set φ := v.equiv_funL.to_continuous_linear_map
        set C := ∥ φ ∥ * Fintype.card ι
        use max C 1 , lt_of_lt_of_leₓ zero_lt_one le_max_rightₓ C 1
        intro e
        calc
          ∑ i , ∥ φ e i ∥ ≤ ∑ i : ι , ∥ φ e ∥ := by apply Finset.sum_le_sum exact fun i hi => norm_le_pi_norm φ e i
            _ = ∥ φ e ∥ * Fintype.card ι := by simpa only [ mul_commₓ , Finset.sum_const , nsmul_eq_mul ]
            _ ≤ ∥ φ ∥ * ∥ e ∥ * Fintype.card ι := mul_le_mul_of_nonneg_right φ.le_op_norm e Fintype.card ι . cast_nonneg
            _ = ∥ φ ∥ * Fintype.card ι * ∥ e ∥ := by ring
            _ ≤ max C 1 * ∥ e ∥ := mul_le_mul_of_nonneg_right le_max_leftₓ _ _ norm_nonneg _

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `Basis.op_norm_le [])
  (Command.declSig
   [(Term.implicitBinder "{" [`ι] [":" (Term.type "Type" [(Level.hole "_")])] "}")
    (Term.instBinder "[" [] (Term.app `Fintype [`ι]) "]")
    (Term.explicitBinder "(" [`v] [":" (Term.app `Basis [`ι `𝕜 `E])] [] ")")]
   (Term.typeSpec
    ":"
    (Mathlib.ExtendedBinder.«term∃___,_»
     "∃"
     `C
     (Mathlib.ExtendedBinder.«binderTerm>_»
      ">"
      (Term.paren "(" [(numLit "0") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")"))
     ","
     (Term.forall
      "∀"
      [(Term.implicitBinder "{" [`u] [":" (Topology.Algebra.Module.«term_→L[_]_» `E " →L[" `𝕜 "] " `F)] "}")
       (Term.implicitBinder "{" [`M] [":" (Data.Real.Basic.termℝ "ℝ")] "}")]
      ","
      (Term.arrow
       («term_≤_» (numLit "0") "≤" `M)
       "→"
       (Term.arrow
        (Term.forall
         "∀"
         [(Term.simpleBinder [`i] [])]
         ","
         («term_≤_» (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `u [(Term.app `v [`i])]) "∥") "≤" `M))
        "→"
        («term_≤_»
         (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `u "∥")
         "≤"
         (Finset.Data.Finset.Fold.«term_*_» `C "*" `M))))))))
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
             [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `C)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `C_pos)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hC)]) [])]
             "⟩")])]
         [":"
          (Mathlib.ExtendedBinder.«term∃___,_»
           "∃"
           `C
           (Mathlib.ExtendedBinder.«binderTerm>_»
            ">"
            (Term.paren "(" [(numLit "0") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")"))
           ","
           (Term.forall
            "∀"
            [(Term.simpleBinder [`e] [(Term.typeSpec ":" `E)])]
            ","
            («term_≤_»
             (Algebra.BigOperators.Basic.«term∑_,_»
              "∑"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
              ", "
              (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `v.equiv_fun [`e `i]) "∥"))
             "≤"
             (Finset.Data.Finset.Fold.«term_*_» `C "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥")))))]
         [])
        [])
       (group (Tactic.exact "exact" `v.sup_norm_le_norm) [])
       (group (Tactic.use "use" [`C "," `C_pos]) [])
       (group (Tactic.intro "intro" [`u `M `hM `hu]) [])
       (group
        (Tactic.apply
         "apply"
         (Term.app `u.op_norm_le_bound [(Term.app `mul_nonneg [(Term.app `le_of_ltₓ [`C_pos]) `hM])]))
        [])
       (group (Tactic.intro "intro" [`e]) [])
       (group
        (tacticCalc_
         "calc"
         [(calcStep
           («term_=_»
            (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `u [`e]) "∥")
            "="
            (Analysis.Normed.Group.Basic.«term∥_∥»
             "∥"
             (Term.app
              `u
              [(Algebra.BigOperators.Basic.«term∑_,_»
                "∑"
                (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
                ", "
                (Algebra.Group.Defs.«term_•_» (Term.app `v.equiv_fun [`e `i]) " • " (Term.app `v [`i])))])
             "∥"))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `v.sum_equiv_fun)] "]") [])
                [])]))))
          (calcStep
           («term_=_»
            (Term.hole "_")
            "="
            (Analysis.Normed.Group.Basic.«term∥_∥»
             "∥"
             (Algebra.BigOperators.Basic.«term∑_,_»
              "∑"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
              ", "
              (Algebra.Group.Defs.«term_•_»
               (Term.app `v.equiv_fun [`e `i])
               " • "
               («term_$__» `u "$" (Term.app `v [`i]))))
             "∥"))
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
                 ["[" [(Tactic.simpLemma [] [] `u.map_sum) "," (Tactic.simpLemma [] [] `LinearMap.map_smul)] "]"]
                 [])
                [])]))))
          (calcStep
           («term_≤_»
            (Term.hole "_")
            "≤"
            (Algebra.BigOperators.Basic.«term∑_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
             ", "
             (Analysis.Normed.Group.Basic.«term∥_∥»
              "∥"
              (Algebra.Group.Defs.«term_•_»
               (Term.app `v.equiv_fun [`e `i])
               " • "
               («term_$__» `u "$" (Term.app `v [`i])))
              "∥")))
           ":="
           (Term.app `norm_sum_le [(Term.hole "_") (Term.hole "_")]))
          (calcStep
           («term_=_»
            (Term.hole "_")
            "="
            (Algebra.BigOperators.Basic.«term∑_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
             ", "
             (Finset.Data.Finset.Fold.«term_*_»
              (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `v.equiv_fun [`e `i]) "∥")
              "*"
              (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `u [(Term.app `v [`i])]) "∥"))))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `norm_smul)] "]"] []) [])]))))
          (calcStep
           («term_≤_»
            (Term.hole "_")
            "≤"
            (Algebra.BigOperators.Basic.«term∑_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
             ", "
             (Finset.Data.Finset.Fold.«term_*_»
              (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `v.equiv_fun [`e `i]) "∥")
              "*"
              `M)))
           ":="
           (Term.app
            `Finset.sum_le_sum
            [(Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`i `hi] [])]
               "=>"
               (Term.app
                `mul_le_mul_of_nonneg_left
                [(Term.app `hu [`i]) (Term.app `norm_nonneg [(Term.hole "_")])])))]))
          (calcStep
           («term_=_»
            (Term.hole "_")
            "="
            (Finset.Data.Finset.Fold.«term_*_»
             (Algebra.BigOperators.Basic.«term∑_,_»
              "∑"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
              ", "
              (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `v.equiv_fun [`e `i]) "∥"))
             "*"
             `M))
           ":="
           `finset.sum_mul.symm)
          (calcStep
           («term_≤_»
            (Term.hole "_")
            "≤"
            (Finset.Data.Finset.Fold.«term_*_»
             (Finset.Data.Finset.Fold.«term_*_» `C "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥"))
             "*"
             `M))
           ":="
           (Term.app `mul_le_mul_of_nonneg_right [(Term.app `hC [`e]) `hM]))
          (calcStep
           («term_=_»
            (Term.hole "_")
            "="
            (Finset.Data.Finset.Fold.«term_*_»
             (Finset.Data.Finset.Fold.«term_*_» `C "*" `M)
             "*"
             (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥")))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.Ring.tacticRing "ring") [])]))))])
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
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `C)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `C_pos)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hC)]) [])]
            "⟩")])]
        [":"
         (Mathlib.ExtendedBinder.«term∃___,_»
          "∃"
          `C
          (Mathlib.ExtendedBinder.«binderTerm>_»
           ">"
           (Term.paren "(" [(numLit "0") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")"))
          ","
          (Term.forall
           "∀"
           [(Term.simpleBinder [`e] [(Term.typeSpec ":" `E)])]
           ","
           («term_≤_»
            (Algebra.BigOperators.Basic.«term∑_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
             ", "
             (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `v.equiv_fun [`e `i]) "∥"))
            "≤"
            (Finset.Data.Finset.Fold.«term_*_» `C "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥")))))]
        [])
       [])
      (group (Tactic.exact "exact" `v.sup_norm_le_norm) [])
      (group (Tactic.use "use" [`C "," `C_pos]) [])
      (group (Tactic.intro "intro" [`u `M `hM `hu]) [])
      (group
       (Tactic.apply
        "apply"
        (Term.app `u.op_norm_le_bound [(Term.app `mul_nonneg [(Term.app `le_of_ltₓ [`C_pos]) `hM])]))
       [])
      (group (Tactic.intro "intro" [`e]) [])
      (group
       (tacticCalc_
        "calc"
        [(calcStep
          («term_=_»
           (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `u [`e]) "∥")
           "="
           (Analysis.Normed.Group.Basic.«term∥_∥»
            "∥"
            (Term.app
             `u
             [(Algebra.BigOperators.Basic.«term∑_,_»
               "∑"
               (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
               ", "
               (Algebra.Group.Defs.«term_•_» (Term.app `v.equiv_fun [`e `i]) " • " (Term.app `v [`i])))])
            "∥"))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `v.sum_equiv_fun)] "]") []) [])]))))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Analysis.Normed.Group.Basic.«term∥_∥»
            "∥"
            (Algebra.BigOperators.Basic.«term∑_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
             ", "
             (Algebra.Group.Defs.«term_•_»
              (Term.app `v.equiv_fun [`e `i])
              " • "
              («term_$__» `u "$" (Term.app `v [`i]))))
            "∥"))
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
                ["[" [(Tactic.simpLemma [] [] `u.map_sum) "," (Tactic.simpLemma [] [] `LinearMap.map_smul)] "]"]
                [])
               [])]))))
         (calcStep
          («term_≤_»
           (Term.hole "_")
           "≤"
           (Algebra.BigOperators.Basic.«term∑_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
            ", "
            (Analysis.Normed.Group.Basic.«term∥_∥»
             "∥"
             (Algebra.Group.Defs.«term_•_» (Term.app `v.equiv_fun [`e `i]) " • " («term_$__» `u "$" (Term.app `v [`i])))
             "∥")))
          ":="
          (Term.app `norm_sum_le [(Term.hole "_") (Term.hole "_")]))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Algebra.BigOperators.Basic.«term∑_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
            ", "
            (Finset.Data.Finset.Fold.«term_*_»
             (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `v.equiv_fun [`e `i]) "∥")
             "*"
             (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `u [(Term.app `v [`i])]) "∥"))))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `norm_smul)] "]"] []) [])]))))
         (calcStep
          («term_≤_»
           (Term.hole "_")
           "≤"
           (Algebra.BigOperators.Basic.«term∑_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
            ", "
            (Finset.Data.Finset.Fold.«term_*_»
             (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `v.equiv_fun [`e `i]) "∥")
             "*"
             `M)))
          ":="
          (Term.app
           `Finset.sum_le_sum
           [(Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`i `hi] [])]
              "=>"
              (Term.app `mul_le_mul_of_nonneg_left [(Term.app `hu [`i]) (Term.app `norm_nonneg [(Term.hole "_")])])))]))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Finset.Data.Finset.Fold.«term_*_»
            (Algebra.BigOperators.Basic.«term∑_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
             ", "
             (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `v.equiv_fun [`e `i]) "∥"))
            "*"
            `M))
          ":="
          `finset.sum_mul.symm)
         (calcStep
          («term_≤_»
           (Term.hole "_")
           "≤"
           (Finset.Data.Finset.Fold.«term_*_»
            (Finset.Data.Finset.Fold.«term_*_» `C "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥"))
            "*"
            `M))
          ":="
          (Term.app `mul_le_mul_of_nonneg_right [(Term.app `hC [`e]) `hM]))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Finset.Data.Finset.Fold.«term_*_»
            (Finset.Data.Finset.Fold.«term_*_» `C "*" `M)
            "*"
            (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥")))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.Ring.tacticRing "ring") [])]))))])
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
     («term_=_»
      (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `u [`e]) "∥")
      "="
      (Analysis.Normed.Group.Basic.«term∥_∥»
       "∥"
       (Term.app
        `u
        [(Algebra.BigOperators.Basic.«term∑_,_»
          "∑"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
          ", "
          (Algebra.Group.Defs.«term_•_» (Term.app `v.equiv_fun [`e `i]) " • " (Term.app `v [`i])))])
       "∥"))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `v.sum_equiv_fun)] "]") []) [])]))))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Analysis.Normed.Group.Basic.«term∥_∥»
       "∥"
       (Algebra.BigOperators.Basic.«term∑_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
        ", "
        (Algebra.Group.Defs.«term_•_» (Term.app `v.equiv_fun [`e `i]) " • " («term_$__» `u "$" (Term.app `v [`i]))))
       "∥"))
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
           ["[" [(Tactic.simpLemma [] [] `u.map_sum) "," (Tactic.simpLemma [] [] `LinearMap.map_smul)] "]"]
           [])
          [])]))))
    (calcStep
     («term_≤_»
      (Term.hole "_")
      "≤"
      (Algebra.BigOperators.Basic.«term∑_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
       ", "
       (Analysis.Normed.Group.Basic.«term∥_∥»
        "∥"
        (Algebra.Group.Defs.«term_•_» (Term.app `v.equiv_fun [`e `i]) " • " («term_$__» `u "$" (Term.app `v [`i])))
        "∥")))
     ":="
     (Term.app `norm_sum_le [(Term.hole "_") (Term.hole "_")]))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Algebra.BigOperators.Basic.«term∑_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
       ", "
       (Finset.Data.Finset.Fold.«term_*_»
        (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `v.equiv_fun [`e `i]) "∥")
        "*"
        (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `u [(Term.app `v [`i])]) "∥"))))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `norm_smul)] "]"] []) [])]))))
    (calcStep
     («term_≤_»
      (Term.hole "_")
      "≤"
      (Algebra.BigOperators.Basic.«term∑_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
       ", "
       (Finset.Data.Finset.Fold.«term_*_»
        (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `v.equiv_fun [`e `i]) "∥")
        "*"
        `M)))
     ":="
     (Term.app
      `Finset.sum_le_sum
      [(Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`i `hi] [])]
         "=>"
         (Term.app `mul_le_mul_of_nonneg_left [(Term.app `hu [`i]) (Term.app `norm_nonneg [(Term.hole "_")])])))]))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Finset.Data.Finset.Fold.«term_*_»
       (Algebra.BigOperators.Basic.«term∑_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
        ", "
        (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `v.equiv_fun [`e `i]) "∥"))
       "*"
       `M))
     ":="
     `finset.sum_mul.symm)
    (calcStep
     («term_≤_»
      (Term.hole "_")
      "≤"
      (Finset.Data.Finset.Fold.«term_*_»
       (Finset.Data.Finset.Fold.«term_*_» `C "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥"))
       "*"
       `M))
     ":="
     (Term.app `mul_le_mul_of_nonneg_right [(Term.app `hC [`e]) `hM]))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Finset.Data.Finset.Fold.«term_*_»
       (Finset.Data.Finset.Fold.«term_*_» `C "*" `M)
       "*"
       (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥")))
     ":="
     (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.Ring.tacticRing "ring") [])]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticCalc_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.Ring.tacticRing "ring") [])])))
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.hole "_")
   "="
   (Finset.Data.Finset.Fold.«term_*_»
    (Finset.Data.Finset.Fold.«term_*_» `C "*" `M)
    "*"
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   (Finset.Data.Finset.Fold.«term_*_» `C "*" `M)
   "*"
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `e
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Finset.Data.Finset.Fold.«term_*_» `C "*" `M)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `M
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `C
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Finset.Data.Finset.Fold.«term_*_» `C "*" `M) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.app `mul_le_mul_of_nonneg_right [(Term.app `hC [`e]) `hM])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hM
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `hC [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `e
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hC
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `hC [`e]) []] ")")
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
    (Finset.Data.Finset.Fold.«term_*_» `C "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥"))
    "*"
    `M))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   (Finset.Data.Finset.Fold.«term_*_» `C "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥"))
   "*"
   `M)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `M
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Finset.Data.Finset.Fold.«term_*_» `C "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `e
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `C
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_» `C "*" (Analysis.Normed.Group.Basic.«term∥_∥» "∥" `e "∥")) []]
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
  `finset.sum_mul.symm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.hole "_")
   "="
   (Finset.Data.Finset.Fold.«term_*_»
    (Algebra.BigOperators.Basic.«term∑_,_»
     "∑"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
     ", "
     (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `v.equiv_fun [`e `i]) "∥"))
    "*"
    `M))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   (Algebra.BigOperators.Basic.«term∑_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
    ", "
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `v.equiv_fun [`e `i]) "∥"))
   "*"
   `M)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `M
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Algebra.BigOperators.Basic.«term∑_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
   ", "
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `v.equiv_fun [`e `i]) "∥"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `v.equiv_fun [`e `i]) "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `v.equiv_fun [`e `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `e
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `v.equiv_fun
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
  Basis.op_norm_le
  { ι : Type _ } [ Fintype ι ] ( v : Basis ι 𝕜 E )
    : ∃ C > ( 0 : ℝ ) , ∀ { u : E →L[ 𝕜 ] F } { M : ℝ } , 0 ≤ M → ∀ i , ∥ u v i ∥ ≤ M → ∥ u ∥ ≤ C * M
  :=
    by
      obtain ⟨ C , C_pos , hC ⟩ : ∃ C > ( 0 : ℝ ) , ∀ e : E , ∑ i , ∥ v.equiv_fun e i ∥ ≤ C * ∥ e ∥
        exact v.sup_norm_le_norm
        use C , C_pos
        intro u M hM hu
        apply u.op_norm_le_bound mul_nonneg le_of_ltₓ C_pos hM
        intro e
        calc
          ∥ u e ∥ = ∥ u ∑ i , v.equiv_fun e i • v i ∥ := by rw [ v.sum_equiv_fun ]
            _ = ∥ ∑ i , v.equiv_fun e i • u $ v i ∥ := by simp [ u.map_sum , LinearMap.map_smul ]
            _ ≤ ∑ i , ∥ v.equiv_fun e i • u $ v i ∥ := norm_sum_le _ _
            _ = ∑ i , ∥ v.equiv_fun e i ∥ * ∥ u v i ∥ := by simp only [ norm_smul ]
            _ ≤ ∑ i , ∥ v.equiv_fun e i ∥ * M
              :=
              Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left hu i norm_nonneg _
            _ = ∑ i , ∥ v.equiv_fun e i ∥ * M := finset.sum_mul.symm
            _ ≤ C * ∥ e ∥ * M := mul_le_mul_of_nonneg_right hC e hM
            _ = C * M * ∥ e ∥ := by ring

instance [FiniteDimensional 𝕜 E] [second_countable_topology F] : second_countable_topology (E →L[𝕜] F) := by
  set d := FiniteDimensional.finrank 𝕜 E
  suffices : ∀, ∀ ε > (0 : ℝ), ∀, ∃ n : (E →L[𝕜] F) → Finₓ d → ℕ, ∀ f g : E →L[𝕜] F, n f = n g → dist f g ≤ ε
  exact
    Metric.second_countable_of_countable_discretization fun ε ε_pos =>
      ⟨Finₓ d → ℕ, by
        infer_instance, this ε ε_pos⟩
  intro ε ε_pos
  obtain ⟨u : ℕ → F, hu : DenseRange u⟩ := exists_dense_seq F
  let v := FiniteDimensional.finBasis 𝕜 E
  obtain ⟨C : ℝ, C_pos : 0 < C, hC : ∀ {φ : E →L[𝕜] F} {M : ℝ}, 0 ≤ M → (∀ i, ∥φ (v i)∥ ≤ M) → ∥φ∥ ≤ C*M⟩ :=
    v.op_norm_le
  have h_2C : 0 < 2*C := mul_pos zero_lt_two C_pos
  have hε2C : 0 < ε / 2*C := div_pos ε_pos h_2C
  have : ∀ φ : E →L[𝕜] F, ∃ n : Finₓ d → ℕ, ∥φ - (v.constrL $ (u ∘ n))∥ ≤ ε / 2 := by
    intro φ
    have : ∀ i, ∃ n, ∥φ (v i) - u n∥ ≤ ε / 2*C := by
      simp only [norm_sub_rev]
      intro i
      have : φ (v i) ∈ Closure (range u) := hu _
      obtain ⟨n, hn⟩ : ∃ n, ∥u n - φ (v i)∥ < ε / 2*C
      ·
        rw [mem_closure_iff_nhds_basis Metric.nhds_basis_ball] at this
        specialize this (ε / 2*C) hε2C
        simpa [dist_eq_norm]
      exact ⟨n, le_of_ltₓ hn⟩
    choose n hn using this
    use n
    replace hn : ∀ i : Finₓ d, ∥(φ - (v.constrL $ (u ∘ n))) (v i)∥ ≤ ε / 2*C
    ·
      simp [hn]
    have : (C*ε / 2*C) = ε / 2 := by
      rw [eq_div_iff (two_ne_zero : (2 : ℝ) ≠ 0), mul_commₓ, ← mul_assocₓ, mul_div_cancel' _ (ne_of_gtₓ h_2C)]
    specialize hC (le_of_ltₓ hε2C) hn
    rwa [this] at hC
  choose n hn using this
  set Φ := fun φ : E →L[𝕜] F => v.constrL $ (u ∘ n φ)
  change ∀ z, dist z (Φ z) ≤ ε / 2 at hn
  use n
  intro x y hxy
  calc dist x y ≤ dist x (Φ x)+dist (Φ x) y := dist_triangle _ _ _ _ = dist x (Φ x)+dist y (Φ y) := by
    simp [Φ, hxy, dist_comm]_ ≤ ε := by
    linarith [hn x, hn y]

variable (𝕜 E)

theorem FiniteDimensional.complete [FiniteDimensional 𝕜 E] : CompleteSpace E := by
  set e := ContinuousLinearEquiv.ofFinrankEq (@finrank_fin_fun 𝕜 _ (finrank 𝕜 E)).symm
  have : UniformEmbedding e.to_linear_equiv.to_equiv.symm := e.symm.uniform_embedding
  exact
    (complete_space_congr this).1
      (by
        infer_instance)

variable {𝕜 E}

/--  A finite-dimensional subspace is complete. -/
theorem Submodule.complete_of_finite_dimensional (s : Submodule 𝕜 E) [FiniteDimensional 𝕜 s] : IsComplete (s : Set E) :=
  complete_space_coe_iff_is_complete.1 (FiniteDimensional.complete 𝕜 s)

/--  A finite-dimensional subspace is closed. -/
theorem Submodule.closed_of_finite_dimensional (s : Submodule 𝕜 E) [FiniteDimensional 𝕜 s] : IsClosed (s : Set E) :=
  s.complete_of_finite_dimensional.is_closed

section Riesz

/--  In an infinite dimensional space, given a finite number of points, one may find a point
with norm at most `R` which is at distance at least `1` of all these points. -/
theorem exists_norm_le_le_norm_sub_of_finset {c : 𝕜} (hc : 1 < ∥c∥) {R : ℝ} (hR : ∥c∥ < R) (h : ¬FiniteDimensional 𝕜 E)
    (s : Finset E) : ∃ x : E, ∥x∥ ≤ R ∧ ∀, ∀ y ∈ s, ∀, 1 ≤ ∥y - x∥ := by
  let F := Submodule.span 𝕜 (s : Set E)
  have : FiniteDimensional 𝕜 F :=
    Module.finite_def.2 ((Submodule.fg_top _).2 (Submodule.fg_def.2 ⟨s, Finset.finite_to_set _, rfl⟩))
  have Fclosed : IsClosed (F : Set E) := Submodule.closed_of_finite_dimensional _
  have : ∃ x, x ∉ F := by
    contrapose! h
    have : (⊤ : Submodule 𝕜 E) = F := by
      ·
        ext x
        simp [h]
    have : FiniteDimensional 𝕜 (⊤ : Submodule 𝕜 E) := by
      rwa [this]
    refine' Module.finite_def.2 ((Submodule.fg_top _).1 (Module.finite_def.1 this))
  obtain ⟨x, xR, hx⟩ : ∃ x : E, ∥x∥ ≤ R ∧ ∀ y : E, y ∈ F → 1 ≤ ∥x - y∥ := riesz_lemma_of_norm_lt hc hR Fclosed this
  have hx' : ∀ y : E, y ∈ F → 1 ≤ ∥y - x∥ := by
    intro y hy
    rw [← norm_neg]
    simpa using hx y hy
  exact ⟨x, xR, fun y hy => hx' _ (Submodule.subset_span hy)⟩

/--  In an infinite-dimensional normed space, there exists a sequence of points which are all
bounded by `R` and at distance at least `1`. For a version not assuming `c` and `R`, see
`exists_seq_norm_le_one_le_norm_sub`. -/
theorem exists_seq_norm_le_one_le_norm_sub' {c : 𝕜} (hc : 1 < ∥c∥) {R : ℝ} (hR : ∥c∥ < R) (h : ¬FiniteDimensional 𝕜 E) :
    ∃ f : ℕ → E, (∀ n, ∥f n∥ ≤ R) ∧ ∀ m n, m ≠ n → 1 ≤ ∥f m - f n∥ := by
  have : IsSymm E fun x y : E => 1 ≤ ∥x - y∥ := by
    constructor
    intro x y hxy
    rw [← norm_neg]
    simpa
  apply exists_seq_of_forall_finset_exists' (fun x : E => ∥x∥ ≤ R) fun x : E y : E => 1 ≤ ∥x - y∥
  intro s hs
  exact exists_norm_le_le_norm_sub_of_finset hc hR h s

theorem exists_seq_norm_le_one_le_norm_sub (h : ¬FiniteDimensional 𝕜 E) :
    ∃ (R : ℝ)(f : ℕ → E), 1 < R ∧ (∀ n, ∥f n∥ ≤ R) ∧ ∀ m n, m ≠ n → 1 ≤ ∥f m - f n∥ := by
  obtain ⟨c, hc⟩ : ∃ c : 𝕜, 1 < ∥c∥ := NormedField.exists_one_lt_norm 𝕜
  have A : ∥c∥ < ∥c∥+1 := by
    linarith
  rcases exists_seq_norm_le_one_le_norm_sub' hc A h with ⟨f, hf⟩
  exact ⟨∥c∥+1, f, hc.trans A, hf.1, hf.2⟩

variable (𝕜)

/--  Riesz's theorem: if the unit ball is compact in a vector space, then the space is
finite-dimensional. -/
theorem finite_dimensional_of_is_compact_closed_ball {r : ℝ} (rpos : 0 < r)
    (h : IsCompact (Metric.ClosedBall (0 : E) r)) : FiniteDimensional 𝕜 E := by
  by_contra hfin
  obtain ⟨R, f, Rgt, fle, lef⟩ : ∃ (R : ℝ)(f : ℕ → E), 1 < R ∧ (∀ n, ∥f n∥ ≤ R) ∧ ∀ m n, m ≠ n → 1 ≤ ∥f m - f n∥ :=
    exists_seq_norm_le_one_le_norm_sub hfin
  have rRpos : 0 < r / R := div_pos rpos (zero_lt_one.trans Rgt)
  obtain ⟨c, hc⟩ : ∃ c : 𝕜, 0 < ∥c∥ ∧ ∥c∥ < r / R := NormedField.exists_norm_lt _ rRpos
  let g := fun n : ℕ => c • f n
  have A : ∀ n, g n ∈ Metric.ClosedBall (0 : E) r := by
    intro n
    simp only [norm_smul, dist_zero_right, Metric.mem_closed_ball]
    calc (∥c∥*∥f n∥) ≤ (r / R)*R := mul_le_mul hc.2.le (fle n) (norm_nonneg _) rRpos.le _ = r := by
      field_simp [(zero_lt_one.trans Rgt).ne']
  obtain ⟨x, hx, φ, φmono, φlim⟩ :
    ∃ (x : E)(H : x ∈ Metric.ClosedBall (0 : E) r)(φ : ℕ → ℕ), StrictMono φ ∧ tendsto (g ∘ φ) at_top (𝓝 x) :=
    h.tendsto_subseq A
  have B : CauchySeq (g ∘ φ) := φlim.cauchy_seq
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → dist ((g ∘ φ) n) ((g ∘ φ) N) < ∥c∥ := Metric.cauchy_seq_iff'.1 B ∥c∥ hc.1
  apply lt_irreflₓ ∥c∥
  calc ∥c∥ ≤ dist (g (φ (N+1))) (g (φ N)) := by
    conv_lhs => rw [← mul_oneₓ ∥c∥]
    simp only [g, dist_eq_norm, ← smul_sub, norm_smul, -mul_oneₓ]
    apply mul_le_mul_of_nonneg_left (lef _ _ (ne_of_gtₓ _)) (norm_nonneg _)
    exact φmono (Nat.lt_succ_selfₓ N)_ < ∥c∥ := hN (N+1) (Nat.le_succₓ N)

end Riesz

/--  An injective linear map with finite-dimensional domain is a closed embedding. -/
theorem LinearEquiv.closed_embedding_of_injective {f : E →ₗ[𝕜] F} (hf : f.ker = ⊥) [FiniteDimensional 𝕜 E] :
    ClosedEmbedding (⇑f) :=
  let g := LinearEquiv.ofInjective f (LinearMap.ker_eq_bot.mp hf)
  { embedding_subtype_coe.comp g.to_continuous_linear_equiv.to_homeomorph.embedding with
    closed_range := by
      have := f.finite_dimensional_range
      simpa [f.range_coe] using f.range.closed_of_finite_dimensional }

theorem ContinuousLinearMap.exists_right_inverse_of_surjective [FiniteDimensional 𝕜 F] (f : E →L[𝕜] F)
    (hf : f.range = ⊤) : ∃ g : F →L[𝕜] E, f.comp g = ContinuousLinearMap.id 𝕜 F :=
  let ⟨g, hg⟩ := (f : E →ₗ[𝕜] F).exists_right_inverse_of_surjective hf
  ⟨g.to_continuous_linear_map, ContinuousLinearMap.ext $ LinearMap.ext_iff.1 hg⟩

theorem closed_embedding_smul_left {c : E} (hc : c ≠ 0) : ClosedEmbedding fun x : 𝕜 => x • c :=
  LinearEquiv.closed_embedding_of_injective (LinearEquiv.ker_to_span_singleton 𝕜 E hc)

theorem is_closed_map_smul_left (c : E) : IsClosedMap fun x : 𝕜 => x • c := by
  by_cases' hc : c = 0
  ·
    simp_rw [hc, smul_zero]
    exact is_closed_map_const
  ·
    exact (closed_embedding_smul_left hc).IsClosedMap

end CompleteField

section ProperField

variable (𝕜 : Type u) [NondiscreteNormedField 𝕜] (E : Type v) [NormedGroup E] [NormedSpace 𝕜 E] [ProperSpace 𝕜]

/--  Any finite-dimensional vector space over a proper field is proper.
We do not register this as an instance to avoid an instance loop when trying to prove the
properness of `𝕜`, and the search for `𝕜` as an unknown metavariable. Declare the instance
explicitly when needed. -/
theorem FiniteDimensional.proper [FiniteDimensional 𝕜 E] : ProperSpace E := by
  set e := ContinuousLinearEquiv.ofFinrankEq (@finrank_fin_fun 𝕜 _ (finrank 𝕜 E)).symm
  exact e.symm.antilipschitz.proper_space e.symm.continuous e.symm.surjective

end ProperField

instance FiniteDimensional.proper_real (E : Type u) [NormedGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    ProperSpace E :=
  FiniteDimensional.proper ℝ E

attribute [instance] FiniteDimensional.proper_real

/--  In a finite dimensional vector space over `ℝ`, the series `∑ x, ∥f x∥` is unconditionally
summable if and only if the series `∑ x, f x` is unconditionally summable. One implication holds in
any complete normed space, while the other holds only in finite dimensional spaces. -/
theorem summable_norm_iff {α E : Type _} [NormedGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : α → E} :
    (Summable fun x => ∥f x∥) ↔ Summable f := by
  refine' ⟨summable_of_summable_norm, fun hf => _⟩
  suffices ∀ {N : ℕ} {g : α → Finₓ N → ℝ}, Summable g → Summable fun x => ∥g x∥by
    obtain v := fin_basis ℝ E
    set e := v.equiv_funL
    have : Summable fun x => ∥e (f x)∥ := this (e.summable.2 hf)
    refine' summable_of_norm_bounded _ (this.mul_left (↑nnnorm (e.symm : (Finₓ (finrank ℝ E) → ℝ) →L[ℝ] E))) fun i => _
    simpa using (e.symm : (Finₓ (finrank ℝ E) → ℝ) →L[ℝ] E).le_op_norm (e $ f i)
  (
    clear! E)
  intro N g hg
  have : ∀ i, Summable fun x => ∥g x i∥ := fun i => (Pi.summable.1 hg i).abs
  refine' summable_of_norm_bounded _ (summable_sum fun i hi : i ∈ Finset.univ => this i) fun x => _
  rw [norm_norm, pi_norm_le_iff]
  ·
    refine' fun i => Finset.single_le_sum (fun i hi => _) (Finset.mem_univ i)
    exact norm_nonneg (g x i)
  ·
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem summable_of_is_O' {ι E F : Type _} [NormedGroup E] [CompleteSpace E] [NormedGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {f : ι → E} {g : ι → F} (hg : Summable g) (h : is_O f g cofinite) : Summable f :=
  summable_of_is_O (summable_norm_iff.mpr hg) h.norm_right

theorem summable_of_is_O_nat' {E F : Type _} [NormedGroup E] [CompleteSpace E] [NormedGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {f : ℕ → E} {g : ℕ → F} (hg : Summable g) (h : is_O f g at_top) : Summable f :=
  summable_of_is_O_nat (summable_norm_iff.mpr hg) h.norm_right

theorem summable_of_is_equivalent {ι E : Type _} [NormedGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : ι → E}
    {g : ι → E} (hg : Summable g) (h : f ~[cofinite] g) : Summable f :=
  hg.trans_sub (summable_of_is_O' hg h.is_o.is_O)

theorem summable_of_is_equivalent_nat {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : ℕ → E}
    {g : ℕ → E} (hg : Summable g) (h : f ~[at_top] g) : Summable f :=
  hg.trans_sub (summable_of_is_O_nat' hg h.is_o.is_O)

theorem IsEquivalent.summable_iff {ι E : Type _} [NormedGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : ι → E}
    {g : ι → E} (h : f ~[cofinite] g) : Summable f ↔ Summable g :=
  ⟨fun hf => summable_of_is_equivalent hf h.symm, fun hg => summable_of_is_equivalent hg h⟩

theorem IsEquivalent.summable_iff_nat {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : ℕ → E}
    {g : ℕ → E} (h : f ~[at_top] g) : Summable f ↔ Summable g :=
  ⟨fun hf => summable_of_is_equivalent_nat hf h.symm, fun hg => summable_of_is_equivalent_nat hg h⟩

