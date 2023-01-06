/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis

! This file was ported from Lean 3 source module analysis.inner_product_space.dual
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.InnerProductSpace.Projection
import Mathbin.Analysis.NormedSpace.Dual
import Mathbin.Analysis.NormedSpace.Star.Basic

/-!
# The Fréchet-Riesz representation theorem

We consider an inner product space `E` over `𝕜`, which is either `ℝ` or `ℂ`. We define
`to_dual_map`, a conjugate-linear isometric embedding of `E` into its dual, which maps an element
`x` of the space to `λ y, ⟪x, y⟫`.

Under the hypothesis of completeness (i.e., for Hilbert spaces), we upgrade this to `to_dual`, a
conjugate-linear isometric *equivalence* of `E` onto its dual; that is, we establish the
surjectivity of `to_dual_map`.  This is the Fréchet-Riesz representation theorem: every element of
the dual of a Hilbert space `E` has the form `λ u, ⟪x, u⟫` for some `x : E`.

For a bounded sesquilinear form `B : E →L⋆[𝕜] E →L[𝕜] 𝕜`,
we define a map `inner_product_space.continuous_linear_map_of_bilin B : E →L[𝕜] E`,
given by substituting `E →L[𝕜] 𝕜` with `E` using `to_dual`.


## References

* [M. Einsiedler and T. Ward, *Functional Analysis, Spectral Theory, and Applications*]
  [EinsiedlerWard2017]

## Tags

dual, Fréchet-Riesz
-/


noncomputable section

open Classical ComplexConjugate

universe u v

namespace InnerProductSpace

open IsROrC ContinuousLinearMap

variable (𝕜 : Type _)

variable (E : Type _) [IsROrC 𝕜] [InnerProductSpace 𝕜 E]

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 E _ x y

-- mathport name: «expr †»
local postfix:90 "†" => starRingEnd _

/-- An element `x` of an inner product space `E` induces an element of the dual space `dual 𝕜 E`,
the map `λ y, ⟪x, y⟫`; moreover this operation is a conjugate-linear isometric embedding of `E`
into `dual 𝕜 E`.
If `E` is complete, this operation is surjective, hence a conjugate-linear isometric equivalence;
see `to_dual`.
-/
def toDualMap : E →ₗᵢ⋆[𝕜] NormedSpace.Dual 𝕜 E :=
  { innerSL with norm_map' := fun _ => innerSL_apply_norm }
#align inner_product_space.to_dual_map InnerProductSpace.toDualMap

variable {E}

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
      (Command.declId `to_dual_map_apply [])
      (Command.declSig
       [(Term.implicitBinder "{" [`x `y] [":" `E] "}")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `toDualMap [`𝕜 `E `x `y])
         "="
         (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫» "⟪" `x ", " `y "⟫"))))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app `toDualMap [`𝕜 `E `x `y])
       "="
       (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫» "⟪" `x ", " `y "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫» "⟪" `x ", " `y "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»', expected 'InnerProductSpace.Analysis.InnerProductSpace.Dual.term⟪_,_⟫._@.Analysis.InnerProductSpace.Dual._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ] theorem to_dual_map_apply { x y : E } : toDualMap 𝕜 E x y = ⟪ x , y ⟫ := rfl
#align inner_product_space.to_dual_map_apply InnerProductSpace.to_dual_map_apply

theorem innerSL_norm [Nontrivial E] : ‖(innerSL : E →L⋆[𝕜] E →L[𝕜] 𝕜)‖ = 1 :=
  show ‖(toDualMap 𝕜 E).toContinuousLinearMap‖ = 1 from
    LinearIsometry.norm_to_continuous_linear_map _
#align inner_product_space.innerSL_norm InnerProductSpace.innerSL_norm

variable {𝕜}

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `ext_inner_left_basis [])
      (Command.declSig
       [(Term.implicitBinder "{" [`ι] [":" (Term.type "Type" [(Level.hole "_")])] "}")
        (Term.implicitBinder "{" [`x `y] [":" `E] "}")
        (Term.explicitBinder "(" [`b] [":" (Term.app `Basis [`ι `𝕜 `E])] [] ")")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          (Term.forall
           "∀"
           [`i]
           [(Term.typeSpec ":" `ι)]
           ","
           («term_=_»
            (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
             "⟪"
             (Term.app `b [`i])
             ", "
             `x
             "⟫")
            "="
            (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
             "⟪"
             (Term.app `b [`i])
             ", "
             `y
             "⟫")))]
         []
         ")")]
       (Term.typeSpec ":" («term_=_» `x "=" `y)))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.apply
            "apply"
            (Term.proj (Term.proj (Term.app `to_dual_map [`𝕜 `E]) "." `map_eq_iff) "." `mp))
           []
           (Tactic.refine'
            "refine'"
            (Term.app
             (Term.proj
              (Term.app `Function.Injective.eq_iff [`ContinuousLinearMap.coe_injective])
              "."
              `mp)
             [(Term.app `Basis.ext [`b (Term.hole "_")])]))
           []
           (Tactic.intro "intro" [`i])
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `to_dual_map_apply)
              ","
              (Tactic.simpLemma [] [] `ContinuousLinearMap.coe_coe)]
             "]"]
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `inner_conj_sym)]
             "]")
            [])
           []
           (Tactic.nthRwRHS
            "nth_rw_rhs"
            (num "1")
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `inner_conj_sym)]
             "]")
            [])
           []
           (Tactic.exact
            "exact"
            (Term.app
             `congr_arg
             [(ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") (Term.app `h [`i])]))])))
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
           (Term.proj (Term.proj (Term.app `to_dual_map [`𝕜 `E]) "." `map_eq_iff) "." `mp))
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            (Term.proj
             (Term.app `Function.Injective.eq_iff [`ContinuousLinearMap.coe_injective])
             "."
             `mp)
            [(Term.app `Basis.ext [`b (Term.hole "_")])]))
          []
          (Tactic.intro "intro" [`i])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `to_dual_map_apply)
             ","
             (Tactic.simpLemma [] [] `ContinuousLinearMap.coe_coe)]
            "]"]
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `inner_conj_sym)]
            "]")
           [])
          []
          (Tactic.nthRwRHS
           "nth_rw_rhs"
           (num "1")
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `inner_conj_sym)]
            "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            `congr_arg
            [(ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") (Term.app `h [`i])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `congr_arg
        [(ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") (Term.app `h [`i])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `congr_arg
       [(ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") (Term.app `h [`i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `h [`i]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ComplexConjugate.Algebra.Star.Basic.star_ring_end', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ComplexConjugate.Algebra.Star.Basic.star_ring_end', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `congr_arg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.nthRwRHS
       "nth_rw_rhs"
       (num "1")
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `inner_conj_sym)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner_conj_sym
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `inner_conj_sym)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner_conj_sym
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
        [(Tactic.simpLemma [] [] `to_dual_map_apply)
         ","
         (Tactic.simpLemma [] [] `ContinuousLinearMap.coe_coe)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ContinuousLinearMap.coe_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `to_dual_map_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`i])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        (Term.proj
         (Term.app `Function.Injective.eq_iff [`ContinuousLinearMap.coe_injective])
         "."
         `mp)
        [(Term.app `Basis.ext [`b (Term.hole "_")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app `Function.Injective.eq_iff [`ContinuousLinearMap.coe_injective])
        "."
        `mp)
       [(Term.app `Basis.ext [`b (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Basis.ext [`b (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Basis.ext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Basis.ext [`b (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `Function.Injective.eq_iff [`ContinuousLinearMap.coe_injective]) "." `mp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Function.Injective.eq_iff [`ContinuousLinearMap.coe_injective])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ContinuousLinearMap.coe_injective
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Function.Injective.eq_iff
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Function.Injective.eq_iff [`ContinuousLinearMap.coe_injective])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply
       "apply"
       (Term.proj (Term.proj (Term.app `to_dual_map [`𝕜 `E]) "." `map_eq_iff) "." `mp))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj (Term.app `to_dual_map [`𝕜 `E]) "." `map_eq_iff) "." `mp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app `to_dual_map [`𝕜 `E]) "." `map_eq_iff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `to_dual_map [`𝕜 `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝕜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `to_dual_map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `to_dual_map [`𝕜 `E]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_» `x "=" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`i]
       [(Term.typeSpec ":" `ι)]
       ","
       («term_=_»
        (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
         "⟪"
         (Term.app `b [`i])
         ", "
         `x
         "⟫")
        "="
        (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
         "⟪"
         (Term.app `b [`i])
         ", "
         `y
         "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
        "⟪"
        (Term.app `b [`i])
        ", "
        `x
        "⟫")
       "="
       (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
        "⟪"
        (Term.app `b [`i])
        ", "
        `y
        "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
       "⟪"
       (Term.app `b [`i])
       ", "
       `y
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»', expected 'InnerProductSpace.Analysis.InnerProductSpace.Dual.term⟪_,_⟫._@.Analysis.InnerProductSpace.Dual._hyg.7'
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
  ext_inner_left_basis
  { ι : Type _ } { x y : E } ( b : Basis ι 𝕜 E ) ( h : ∀ i : ι , ⟪ b i , x ⟫ = ⟪ b i , y ⟫ ) : x = y
  :=
    by
      apply to_dual_map 𝕜 E . map_eq_iff . mp
        refine' Function.Injective.eq_iff ContinuousLinearMap.coe_injective . mp Basis.ext b _
        intro i
        simp only [ to_dual_map_apply , ContinuousLinearMap.coe_coe ]
        rw [ ← inner_conj_sym ]
        nth_rw_rhs 1 [ ← inner_conj_sym ]
        exact congr_arg conj h i
#align inner_product_space.ext_inner_left_basis InnerProductSpace.ext_inner_left_basis

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `ext_inner_right_basis [])
      (Command.declSig
       [(Term.implicitBinder "{" [`ι] [":" (Term.type "Type" [(Level.hole "_")])] "}")
        (Term.implicitBinder "{" [`x `y] [":" `E] "}")
        (Term.explicitBinder "(" [`b] [":" (Term.app `Basis [`ι `𝕜 `E])] [] ")")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          (Term.forall
           "∀"
           [`i]
           [(Term.typeSpec ":" `ι)]
           ","
           («term_=_»
            (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
             "⟪"
             `x
             ", "
             (Term.app `b [`i])
             "⟫")
            "="
            (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
             "⟪"
             `y
             ", "
             (Term.app `b [`i])
             "⟫")))]
         []
         ")")]
       (Term.typeSpec ":" («term_=_» `x "=" `y)))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.app
             `ext_inner_left_basis
             [`b (Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.hole "_")))]))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `inner_conj_sym)]
             "]")
            [])
           []
           (Tactic.nthRwRHS
            "nth_rw_rhs"
            (num "1")
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `inner_conj_sym)]
             "]")
            [])
           []
           (Tactic.exact
            "exact"
            (Term.app
             `congr_arg
             [(ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") (Term.app `h [`i])]))])))
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
            `ext_inner_left_basis
            [`b (Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.hole "_")))]))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `inner_conj_sym)]
            "]")
           [])
          []
          (Tactic.nthRwRHS
           "nth_rw_rhs"
           (num "1")
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `inner_conj_sym)]
            "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            `congr_arg
            [(ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") (Term.app `h [`i])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `congr_arg
        [(ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") (Term.app `h [`i])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `congr_arg
       [(ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj") (Term.app `h [`i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `h [`i]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ComplexConjugate.Algebra.Star.Basic.star_ring_end', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ComplexConjugate.Algebra.Star.Basic.star_ring_end', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (ComplexConjugate.Algebra.Star.Basic.star_ring_end "conj")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `congr_arg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.nthRwRHS
       "nth_rw_rhs"
       (num "1")
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `inner_conj_sym)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner_conj_sym
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `inner_conj_sym)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner_conj_sym
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `ext_inner_left_basis
        [`b (Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `ext_inner_left_basis
       [`b (Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ext_inner_left_basis
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_» `x "=" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.forall
       "∀"
       [`i]
       [(Term.typeSpec ":" `ι)]
       ","
       («term_=_»
        (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
         "⟪"
         `x
         ", "
         (Term.app `b [`i])
         "⟫")
        "="
        (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
         "⟪"
         `y
         ", "
         (Term.app `b [`i])
         "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
        "⟪"
        `x
        ", "
        (Term.app `b [`i])
        "⟫")
       "="
       (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
        "⟪"
        `y
        ", "
        (Term.app `b [`i])
        "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
       "⟪"
       `y
       ", "
       (Term.app `b [`i])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»', expected 'InnerProductSpace.Analysis.InnerProductSpace.Dual.term⟪_,_⟫._@.Analysis.InnerProductSpace.Dual._hyg.7'
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
  ext_inner_right_basis
  { ι : Type _ } { x y : E } ( b : Basis ι 𝕜 E ) ( h : ∀ i : ι , ⟪ x , b i ⟫ = ⟪ y , b i ⟫ ) : x = y
  :=
    by
      refine' ext_inner_left_basis b fun i => _
        rw [ ← inner_conj_sym ]
        nth_rw_rhs 1 [ ← inner_conj_sym ]
        exact congr_arg conj h i
#align inner_product_space.ext_inner_right_basis InnerProductSpace.ext_inner_right_basis

variable (𝕜) (E) [CompleteSpace E]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Fréchet-Riesz representation: any `ℓ` in the dual of a Hilbert space `E` is of the form\n`λ u, ⟪y, u⟫` for some `y : E`, i.e. `to_dual_map` is surjective.\n-/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `toDual [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Analysis.NormedSpace.LinearIsometry.«term_≃ₗᵢ⋆[_]_»
          `E
          " ≃ₗᵢ⋆["
          `𝕜
          "] "
          (Term.app `NormedSpace.Dual [`𝕜 `E])))])
      (Command.declValSimple
       ":="
       (Term.app
        `LinearIsometryEquiv.ofSurjective
        [(Term.app `toDualMap [`𝕜 `E])
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.intro "intro" [`ℓ])
             []
             (Mathlib.Tactic.set
              "set"
              []
              (Mathlib.Tactic.setArgsRest
               `Y
               []
               ":="
               (Term.app `LinearMap.ker [`ℓ])
               ["with" [] `hY]))
             []
             (Classical.«tacticBy_cases_:_»
              "by_cases"
              [`htriv ":"]
              («term_=_» `Y "=" (Order.BoundedOrder.«term⊤» "⊤")))
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`hℓ []]
                  [(Term.typeSpec ":" («term_=_» `ℓ "=" (num "0")))]
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
                         []
                         ":="
                         (Term.app `linear_map.ker_eq_top.mp [`htriv]))))
                      []
                      (Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq
                        "["
                        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `coe_zero)]
                        "]")
                       [(Tactic.location "at" (Tactic.locationHyp [`h'] []))])
                      []
                      (Tactic.apply "apply" `coe_injective)
                      []
                      (Tactic.exact "exact" `h')]))))))
               []
               (Tactic.exact
                "exact"
                (Term.anonymousCtor
                 "⟨"
                 [(num "0")
                  ","
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hℓ)] "]"] [])])))]
                 "⟩"))])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule
                   [(patternIgnore (token.«← » "←"))]
                   `Submodule.orthogonal_eq_bot_iff)]
                 "]")
                [(Tactic.location "at" (Tactic.locationHyp [`htriv] []))])
               []
               (Tactic.change
                "change"
                («term_≠_»
                 (Analysis.InnerProductSpace.Basic.«term_ᗮ» `Y "ᗮ")
                 "≠"
                 (Order.BoundedOrder.«term⊥» "⊥"))
                [(Tactic.location "at" (Tactic.locationHyp [`htriv] []))])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Submodule.ne_bot_iff)] "]")
                [(Tactic.location "at" (Tactic.locationHyp [`htriv] []))])
               []
               (Std.Tactic.obtain
                "obtain"
                [(Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z)])
                      [":" `E])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hz)])
                      [":" («term_∈_» `z "∈" (Analysis.InnerProductSpace.Basic.«term_ᗮ» `Y "ᗮ"))])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z_ne_0)])
                      [":" («term_≠_» `z "≠" (num "0"))])]
                    "⟩")])]
                []
                [":=" [`htriv]])
               []
               (Tactic.refine'
                "refine'"
                (Term.anonymousCtor
                 "⟨"
                 [(Algebra.Group.Defs.«term_•_»
                   («term_/_»
                    (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term_†»
                     (Term.app `ℓ [`z])
                     "†")
                    "/"
                    (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                     "⟪"
                     `z
                     ", "
                     `z
                     "⟫"))
                   " • "
                   `z)
                  ","
                  (Term.hole "_")]
                 "⟩"))
               []
               (Std.Tactic.Ext.«tacticExt___:_»
                "ext"
                [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))]
                [])
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`h₁ []]
                  [(Term.typeSpec
                    ":"
                    («term_∈_»
                     («term_-_»
                      (Algebra.Group.Defs.«term_•_» (Term.app `ℓ [`z]) " • " `x)
                      "-"
                      (Algebra.Group.Defs.«term_•_» (Term.app `ℓ [`x]) " • " `z))
                     "∈"
                     `Y))]
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
                        [(Tactic.rwRule [] `LinearMap.mem_ker)
                         ","
                         (Tactic.rwRule [] `map_sub)
                         ","
                         (Tactic.rwRule [] `ContinuousLinearMap.map_smul)
                         ","
                         (Tactic.rwRule [] `ContinuousLinearMap.map_smul)
                         ","
                         (Tactic.rwRule [] `Algebra.id.smul_eq_mul)
                         ","
                         (Tactic.rwRule [] `Algebra.id.smul_eq_mul)
                         ","
                         (Tactic.rwRule [] `mul_comm)]
                        "]")
                       [])
                      []
                      (Tactic.exact
                       "exact"
                       (Term.app
                        `sub_self
                        [(«term_*_» (Term.app `ℓ [`x]) "*" (Term.app `ℓ [`z]))]))]))))))
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`h₂ []]
                  [(Term.typeSpec
                    ":"
                    («term_=_»
                     («term_*_»
                      (Term.app `ℓ [`z])
                      "*"
                      (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                       "⟪"
                       `z
                       ", "
                       `x
                       "⟫"))
                     "="
                     («term_*_»
                      (Term.app `ℓ [`x])
                      "*"
                      (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                       "⟪"
                       `z
                       ", "
                       `z
                       "⟫"))))]
                  ":="
                  (Std.Tactic.haveI
                   "haveI"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`h₃ []]
                     []
                     ":="
                     (calc
                      "calc"
                      (calcStep
                       («term_=_»
                        (num "0")
                        "="
                        (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                         "⟪"
                         `z
                         ", "
                         («term_-_»
                          (Algebra.Group.Defs.«term_•_» (Term.app `ℓ [`z]) " • " `x)
                          "-"
                          (Algebra.Group.Defs.«term_•_» (Term.app `ℓ [`x]) " • " `z))
                         "⟫"))
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
                               []
                               (Term.app
                                (Term.proj (Term.app `Y.mem_orthogonal' [`z]) "." `mp)
                                [`hz]))]
                             "]")
                            [])
                           []
                           (Tactic.exact "exact" `h₁)]))))
                      [(calcStep
                        («term_=_»
                         (Term.hole "_")
                         "="
                         («term_-_»
                          (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                           "⟪"
                           `z
                           ", "
                           (Algebra.Group.Defs.«term_•_» (Term.app `ℓ [`z]) " • " `x)
                           "⟫")
                          "-"
                          (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                           "⟪"
                           `z
                           ", "
                           (Algebra.Group.Defs.«term_•_» (Term.app `ℓ [`x]) " • " `z)
                           "⟫")))
                        ":="
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(Tactic.rwSeq
                             "rw"
                             []
                             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `inner_sub_right)] "]")
                             [])]))))
                       (calcStep
                        («term_=_»
                         (Term.hole "_")
                         "="
                         («term_-_»
                          («term_*_»
                           (Term.app `ℓ [`z])
                           "*"
                           (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                            "⟪"
                            `z
                            ", "
                            `x
                            "⟫"))
                          "-"
                          («term_*_»
                           (Term.app `ℓ [`x])
                           "*"
                           (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                            "⟪"
                            `z
                            ", "
                            `z
                            "⟫"))))
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
                             ["[" [(Tactic.simpLemma [] [] `inner_smul_right)] "]"]
                             [])]))))])))
                   []
                   (Term.app `sub_eq_zero.mp [(Term.app `Eq.symm [`h₃])])))))
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`h₄ []]
                  []
                  ":="
                  (calc
                   "calc"
                   (calcStep
                    («term_=_»
                     (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                      "⟪"
                      (Algebra.Group.Defs.«term_•_»
                       («term_/_»
                        (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term_†»
                         (Term.app `ℓ [`z])
                         "†")
                        "/"
                        (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                         "⟪"
                         `z
                         ", "
                         `z
                         "⟫"))
                       " • "
                       `z)
                      ", "
                      `x
                      "⟫")
                     "="
                     («term_*_»
                      («term_/_»
                       (Term.app `ℓ [`z])
                       "/"
                       (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                        "⟪"
                        `z
                        ", "
                        `z
                        "⟫"))
                      "*"
                      (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                       "⟪"
                       `z
                       ", "
                       `x
                       "⟫")))
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
                          [(Tactic.simpLemma [] [] `inner_smul_left)
                           ","
                           (Tactic.simpLemma [] [] `conj_conj)]
                          "]"]
                         [])]))))
                   [(calcStep
                     («term_=_»
                      (Term.hole "_")
                      "="
                      («term_/_»
                       («term_*_»
                        (Term.app `ℓ [`z])
                        "*"
                        (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                         "⟪"
                         `z
                         ", "
                         `x
                         "⟫"))
                       "/"
                       (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                        "⟪"
                        `z
                        ", "
                        `z
                        "⟫")))
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
                           [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `div_mul_eq_mul_div)]
                           "]")
                          [])]))))
                    (calcStep
                     («term_=_»
                      (Term.hole "_")
                      "="
                      («term_/_»
                       («term_*_»
                        (Term.app `ℓ [`x])
                        "*"
                        (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                         "⟪"
                         `z
                         ", "
                         `z
                         "⟫"))
                       "/"
                       (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                        "⟪"
                        `z
                        ", "
                        `z
                        "⟫")))
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.rwSeq
                          "rw"
                          []
                          (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h₂)] "]")
                          [])]))))
                    (calcStep
                     («term_=_» (Term.hole "_") "=" (Term.app `ℓ [`x]))
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.tacticHave_
                          "have"
                          (Term.haveDecl
                           (Term.haveIdDecl
                            []
                            [(Term.typeSpec
                              ":"
                              («term_≠_»
                               (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                                "⟪"
                                `z
                                ", "
                                `z
                                "⟫")
                               "≠"
                               (num "0")))]
                            ":="
                            (Term.byTactic
                             "by"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(Tactic.change
                                 "change"
                                 (Term.arrow («term_=_» `z "=" (num "0")) "→" `False)
                                 [(Tactic.location "at" (Tactic.locationHyp [`z_ne_0] []))])
                                []
                                (Std.Tactic.tacticRwa__
                                 "rwa"
                                 (Tactic.rwRuleSeq
                                  "["
                                  [(Tactic.rwRule
                                    [(patternIgnore (token.«← » "←"))]
                                    `inner_self_eq_zero)]
                                  "]")
                                 [(Tactic.location "at" (Tactic.locationHyp [`z_ne_0] []))])]))))))
                         []
                         (Tactic.fieldSimp
                          "field_simp"
                          []
                          []
                          []
                          [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `this)] "]")]
                          [])]))))]))))
               []
               (Tactic.exact "exact" `h₄)])])))])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `LinearIsometryEquiv.ofSurjective
       [(Term.app `toDualMap [`𝕜 `E])
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.intro "intro" [`ℓ])
            []
            (Mathlib.Tactic.set
             "set"
             []
             (Mathlib.Tactic.setArgsRest `Y [] ":=" (Term.app `LinearMap.ker [`ℓ]) ["with" [] `hY]))
            []
            (Classical.«tacticBy_cases_:_»
             "by_cases"
             [`htriv ":"]
             («term_=_» `Y "=" (Order.BoundedOrder.«term⊤» "⊤")))
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`hℓ []]
                 [(Term.typeSpec ":" («term_=_» `ℓ "=" (num "0")))]
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
                        []
                        ":="
                        (Term.app `linear_map.ker_eq_top.mp [`htriv]))))
                     []
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `coe_zero)]
                       "]")
                      [(Tactic.location "at" (Tactic.locationHyp [`h'] []))])
                     []
                     (Tactic.apply "apply" `coe_injective)
                     []
                     (Tactic.exact "exact" `h')]))))))
              []
              (Tactic.exact
               "exact"
               (Term.anonymousCtor
                "⟨"
                [(num "0")
                 ","
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hℓ)] "]"] [])])))]
                "⟩"))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule
                  [(patternIgnore (token.«← » "←"))]
                  `Submodule.orthogonal_eq_bot_iff)]
                "]")
               [(Tactic.location "at" (Tactic.locationHyp [`htriv] []))])
              []
              (Tactic.change
               "change"
               («term_≠_»
                (Analysis.InnerProductSpace.Basic.«term_ᗮ» `Y "ᗮ")
                "≠"
                (Order.BoundedOrder.«term⊥» "⊥"))
               [(Tactic.location "at" (Tactic.locationHyp [`htriv] []))])
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Submodule.ne_bot_iff)] "]")
               [(Tactic.location "at" (Tactic.locationHyp [`htriv] []))])
              []
              (Std.Tactic.obtain
               "obtain"
               [(Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z)])
                     [":" `E])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hz)])
                     [":" («term_∈_» `z "∈" (Analysis.InnerProductSpace.Basic.«term_ᗮ» `Y "ᗮ"))])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z_ne_0)])
                     [":" («term_≠_» `z "≠" (num "0"))])]
                   "⟩")])]
               []
               [":=" [`htriv]])
              []
              (Tactic.refine'
               "refine'"
               (Term.anonymousCtor
                "⟨"
                [(Algebra.Group.Defs.«term_•_»
                  («term_/_»
                   (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term_†»
                    (Term.app `ℓ [`z])
                    "†")
                   "/"
                   (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                    "⟪"
                    `z
                    ", "
                    `z
                    "⟫"))
                  " • "
                  `z)
                 ","
                 (Term.hole "_")]
                "⟩"))
              []
              (Std.Tactic.Ext.«tacticExt___:_»
               "ext"
               [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))]
               [])
              []
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`h₁ []]
                 [(Term.typeSpec
                   ":"
                   («term_∈_»
                    («term_-_»
                     (Algebra.Group.Defs.«term_•_» (Term.app `ℓ [`z]) " • " `x)
                     "-"
                     (Algebra.Group.Defs.«term_•_» (Term.app `ℓ [`x]) " • " `z))
                    "∈"
                    `Y))]
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
                       [(Tactic.rwRule [] `LinearMap.mem_ker)
                        ","
                        (Tactic.rwRule [] `map_sub)
                        ","
                        (Tactic.rwRule [] `ContinuousLinearMap.map_smul)
                        ","
                        (Tactic.rwRule [] `ContinuousLinearMap.map_smul)
                        ","
                        (Tactic.rwRule [] `Algebra.id.smul_eq_mul)
                        ","
                        (Tactic.rwRule [] `Algebra.id.smul_eq_mul)
                        ","
                        (Tactic.rwRule [] `mul_comm)]
                       "]")
                      [])
                     []
                     (Tactic.exact
                      "exact"
                      (Term.app
                       `sub_self
                       [(«term_*_» (Term.app `ℓ [`x]) "*" (Term.app `ℓ [`z]))]))]))))))
              []
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`h₂ []]
                 [(Term.typeSpec
                   ":"
                   («term_=_»
                    («term_*_»
                     (Term.app `ℓ [`z])
                     "*"
                     (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                      "⟪"
                      `z
                      ", "
                      `x
                      "⟫"))
                    "="
                    («term_*_»
                     (Term.app `ℓ [`x])
                     "*"
                     (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                      "⟪"
                      `z
                      ", "
                      `z
                      "⟫"))))]
                 ":="
                 (Std.Tactic.haveI
                  "haveI"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`h₃ []]
                    []
                    ":="
                    (calc
                     "calc"
                     (calcStep
                      («term_=_»
                       (num "0")
                       "="
                       (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                        "⟪"
                        `z
                        ", "
                        («term_-_»
                         (Algebra.Group.Defs.«term_•_» (Term.app `ℓ [`z]) " • " `x)
                         "-"
                         (Algebra.Group.Defs.«term_•_» (Term.app `ℓ [`x]) " • " `z))
                        "⟫"))
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
                              []
                              (Term.app
                               (Term.proj (Term.app `Y.mem_orthogonal' [`z]) "." `mp)
                               [`hz]))]
                            "]")
                           [])
                          []
                          (Tactic.exact "exact" `h₁)]))))
                     [(calcStep
                       («term_=_»
                        (Term.hole "_")
                        "="
                        («term_-_»
                         (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                          "⟪"
                          `z
                          ", "
                          (Algebra.Group.Defs.«term_•_» (Term.app `ℓ [`z]) " • " `x)
                          "⟫")
                         "-"
                         (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                          "⟪"
                          `z
                          ", "
                          (Algebra.Group.Defs.«term_•_» (Term.app `ℓ [`x]) " • " `z)
                          "⟫")))
                       ":="
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Tactic.rwSeq
                            "rw"
                            []
                            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `inner_sub_right)] "]")
                            [])]))))
                      (calcStep
                       («term_=_»
                        (Term.hole "_")
                        "="
                        («term_-_»
                         («term_*_»
                          (Term.app `ℓ [`z])
                          "*"
                          (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                           "⟪"
                           `z
                           ", "
                           `x
                           "⟫"))
                         "-"
                         («term_*_»
                          (Term.app `ℓ [`x])
                          "*"
                          (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                           "⟪"
                           `z
                           ", "
                           `z
                           "⟫"))))
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
                            ["[" [(Tactic.simpLemma [] [] `inner_smul_right)] "]"]
                            [])]))))])))
                  []
                  (Term.app `sub_eq_zero.mp [(Term.app `Eq.symm [`h₃])])))))
              []
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`h₄ []]
                 []
                 ":="
                 (calc
                  "calc"
                  (calcStep
                   («term_=_»
                    (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                     "⟪"
                     (Algebra.Group.Defs.«term_•_»
                      («term_/_»
                       (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term_†»
                        (Term.app `ℓ [`z])
                        "†")
                       "/"
                       (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                        "⟪"
                        `z
                        ", "
                        `z
                        "⟫"))
                      " • "
                      `z)
                     ", "
                     `x
                     "⟫")
                    "="
                    («term_*_»
                     («term_/_»
                      (Term.app `ℓ [`z])
                      "/"
                      (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                       "⟪"
                       `z
                       ", "
                       `z
                       "⟫"))
                     "*"
                     (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                      "⟪"
                      `z
                      ", "
                      `x
                      "⟫")))
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
                         [(Tactic.simpLemma [] [] `inner_smul_left)
                          ","
                          (Tactic.simpLemma [] [] `conj_conj)]
                         "]"]
                        [])]))))
                  [(calcStep
                    («term_=_»
                     (Term.hole "_")
                     "="
                     («term_/_»
                      («term_*_»
                       (Term.app `ℓ [`z])
                       "*"
                       (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                        "⟪"
                        `z
                        ", "
                        `x
                        "⟫"))
                      "/"
                      (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                       "⟪"
                       `z
                       ", "
                       `z
                       "⟫")))
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
                          [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `div_mul_eq_mul_div)]
                          "]")
                         [])]))))
                   (calcStep
                    («term_=_»
                     (Term.hole "_")
                     "="
                     («term_/_»
                      («term_*_»
                       (Term.app `ℓ [`x])
                       "*"
                       (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                        "⟪"
                        `z
                        ", "
                        `z
                        "⟫"))
                      "/"
                      (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                       "⟪"
                       `z
                       ", "
                       `z
                       "⟫")))
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.rwSeq
                         "rw"
                         []
                         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h₂)] "]")
                         [])]))))
                   (calcStep
                    («term_=_» (Term.hole "_") "=" (Term.app `ℓ [`x]))
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.tacticHave_
                         "have"
                         (Term.haveDecl
                          (Term.haveIdDecl
                           []
                           [(Term.typeSpec
                             ":"
                             («term_≠_»
                              (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                               "⟪"
                               `z
                               ", "
                               `z
                               "⟫")
                              "≠"
                              (num "0")))]
                           ":="
                           (Term.byTactic
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented
                              [(Tactic.change
                                "change"
                                (Term.arrow («term_=_» `z "=" (num "0")) "→" `False)
                                [(Tactic.location "at" (Tactic.locationHyp [`z_ne_0] []))])
                               []
                               (Std.Tactic.tacticRwa__
                                "rwa"
                                (Tactic.rwRuleSeq
                                 "["
                                 [(Tactic.rwRule
                                   [(patternIgnore (token.«← » "←"))]
                                   `inner_self_eq_zero)]
                                 "]")
                                [(Tactic.location "at" (Tactic.locationHyp [`z_ne_0] []))])]))))))
                        []
                        (Tactic.fieldSimp
                         "field_simp"
                         []
                         []
                         []
                         [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `this)] "]")]
                         [])]))))]))))
              []
              (Tactic.exact "exact" `h₄)])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intro "intro" [`ℓ])
          []
          (Mathlib.Tactic.set
           "set"
           []
           (Mathlib.Tactic.setArgsRest `Y [] ":=" (Term.app `LinearMap.ker [`ℓ]) ["with" [] `hY]))
          []
          (Classical.«tacticBy_cases_:_»
           "by_cases"
           [`htriv ":"]
           («term_=_» `Y "=" (Order.BoundedOrder.«term⊤» "⊤")))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`hℓ []]
               [(Term.typeSpec ":" («term_=_» `ℓ "=" (num "0")))]
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
                      []
                      ":="
                      (Term.app `linear_map.ker_eq_top.mp [`htriv]))))
                   []
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `coe_zero)]
                     "]")
                    [(Tactic.location "at" (Tactic.locationHyp [`h'] []))])
                   []
                   (Tactic.apply "apply" `coe_injective)
                   []
                   (Tactic.exact "exact" `h')]))))))
            []
            (Tactic.exact
             "exact"
             (Term.anonymousCtor
              "⟨"
              [(num "0")
               ","
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `hℓ)] "]"] [])])))]
              "⟩"))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Submodule.orthogonal_eq_bot_iff)]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`htriv] []))])
            []
            (Tactic.change
             "change"
             («term_≠_»
              (Analysis.InnerProductSpace.Basic.«term_ᗮ» `Y "ᗮ")
              "≠"
              (Order.BoundedOrder.«term⊥» "⊥"))
             [(Tactic.location "at" (Tactic.locationHyp [`htriv] []))])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Submodule.ne_bot_iff)] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`htriv] []))])
            []
            (Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z)])
                   [":" `E])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hz)])
                   [":" («term_∈_» `z "∈" (Analysis.InnerProductSpace.Basic.«term_ᗮ» `Y "ᗮ"))])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z_ne_0)])
                   [":" («term_≠_» `z "≠" (num "0"))])]
                 "⟩")])]
             []
             [":=" [`htriv]])
            []
            (Tactic.refine'
             "refine'"
             (Term.anonymousCtor
              "⟨"
              [(Algebra.Group.Defs.«term_•_»
                («term_/_»
                 (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term_†» (Term.app `ℓ [`z]) "†")
                 "/"
                 (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫» "⟪" `z ", " `z "⟫"))
                " • "
                `z)
               ","
               (Term.hole "_")]
              "⟩"))
            []
            (Std.Tactic.Ext.«tacticExt___:_»
             "ext"
             [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))]
             [])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`h₁ []]
               [(Term.typeSpec
                 ":"
                 («term_∈_»
                  («term_-_»
                   (Algebra.Group.Defs.«term_•_» (Term.app `ℓ [`z]) " • " `x)
                   "-"
                   (Algebra.Group.Defs.«term_•_» (Term.app `ℓ [`x]) " • " `z))
                  "∈"
                  `Y))]
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
                     [(Tactic.rwRule [] `LinearMap.mem_ker)
                      ","
                      (Tactic.rwRule [] `map_sub)
                      ","
                      (Tactic.rwRule [] `ContinuousLinearMap.map_smul)
                      ","
                      (Tactic.rwRule [] `ContinuousLinearMap.map_smul)
                      ","
                      (Tactic.rwRule [] `Algebra.id.smul_eq_mul)
                      ","
                      (Tactic.rwRule [] `Algebra.id.smul_eq_mul)
                      ","
                      (Tactic.rwRule [] `mul_comm)]
                     "]")
                    [])
                   []
                   (Tactic.exact
                    "exact"
                    (Term.app
                     `sub_self
                     [(«term_*_» (Term.app `ℓ [`x]) "*" (Term.app `ℓ [`z]))]))]))))))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`h₂ []]
               [(Term.typeSpec
                 ":"
                 («term_=_»
                  («term_*_»
                   (Term.app `ℓ [`z])
                   "*"
                   (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                    "⟪"
                    `z
                    ", "
                    `x
                    "⟫"))
                  "="
                  («term_*_»
                   (Term.app `ℓ [`x])
                   "*"
                   (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                    "⟪"
                    `z
                    ", "
                    `z
                    "⟫"))))]
               ":="
               (Std.Tactic.haveI
                "haveI"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`h₃ []]
                  []
                  ":="
                  (calc
                   "calc"
                   (calcStep
                    («term_=_»
                     (num "0")
                     "="
                     (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                      "⟪"
                      `z
                      ", "
                      («term_-_»
                       (Algebra.Group.Defs.«term_•_» (Term.app `ℓ [`z]) " • " `x)
                       "-"
                       (Algebra.Group.Defs.«term_•_» (Term.app `ℓ [`x]) " • " `z))
                      "⟫"))
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
                            []
                            (Term.app
                             (Term.proj (Term.app `Y.mem_orthogonal' [`z]) "." `mp)
                             [`hz]))]
                          "]")
                         [])
                        []
                        (Tactic.exact "exact" `h₁)]))))
                   [(calcStep
                     («term_=_»
                      (Term.hole "_")
                      "="
                      («term_-_»
                       (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                        "⟪"
                        `z
                        ", "
                        (Algebra.Group.Defs.«term_•_» (Term.app `ℓ [`z]) " • " `x)
                        "⟫")
                       "-"
                       (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                        "⟪"
                        `z
                        ", "
                        (Algebra.Group.Defs.«term_•_» (Term.app `ℓ [`x]) " • " `z)
                        "⟫")))
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.rwSeq
                          "rw"
                          []
                          (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `inner_sub_right)] "]")
                          [])]))))
                    (calcStep
                     («term_=_»
                      (Term.hole "_")
                      "="
                      («term_-_»
                       («term_*_»
                        (Term.app `ℓ [`z])
                        "*"
                        (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                         "⟪"
                         `z
                         ", "
                         `x
                         "⟫"))
                       "-"
                       («term_*_»
                        (Term.app `ℓ [`x])
                        "*"
                        (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                         "⟪"
                         `z
                         ", "
                         `z
                         "⟫"))))
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
                          ["[" [(Tactic.simpLemma [] [] `inner_smul_right)] "]"]
                          [])]))))])))
                []
                (Term.app `sub_eq_zero.mp [(Term.app `Eq.symm [`h₃])])))))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`h₄ []]
               []
               ":="
               (calc
                "calc"
                (calcStep
                 («term_=_»
                  (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                   "⟪"
                   (Algebra.Group.Defs.«term_•_»
                    («term_/_»
                     (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term_†»
                      (Term.app `ℓ [`z])
                      "†")
                     "/"
                     (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                      "⟪"
                      `z
                      ", "
                      `z
                      "⟫"))
                    " • "
                    `z)
                   ", "
                   `x
                   "⟫")
                  "="
                  («term_*_»
                   («term_/_»
                    (Term.app `ℓ [`z])
                    "/"
                    (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                     "⟪"
                     `z
                     ", "
                     `z
                     "⟫"))
                   "*"
                   (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                    "⟪"
                    `z
                    ", "
                    `x
                    "⟫")))
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
                       [(Tactic.simpLemma [] [] `inner_smul_left)
                        ","
                        (Tactic.simpLemma [] [] `conj_conj)]
                       "]"]
                      [])]))))
                [(calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   («term_/_»
                    («term_*_»
                     (Term.app `ℓ [`z])
                     "*"
                     (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                      "⟪"
                      `z
                      ", "
                      `x
                      "⟫"))
                    "/"
                    (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                     "⟪"
                     `z
                     ", "
                     `z
                     "⟫")))
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
                        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `div_mul_eq_mul_div)]
                        "]")
                       [])]))))
                 (calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   («term_/_»
                    («term_*_»
                     (Term.app `ℓ [`x])
                     "*"
                     (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                      "⟪"
                      `z
                      ", "
                      `z
                      "⟫"))
                    "/"
                    (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                     "⟪"
                     `z
                     ", "
                     `z
                     "⟫")))
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h₂)] "]")
                       [])]))))
                 (calcStep
                  («term_=_» (Term.hole "_") "=" (Term.app `ℓ [`x]))
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.tacticHave_
                       "have"
                       (Term.haveDecl
                        (Term.haveIdDecl
                         []
                         [(Term.typeSpec
                           ":"
                           («term_≠_»
                            (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                             "⟪"
                             `z
                             ", "
                             `z
                             "⟫")
                            "≠"
                            (num "0")))]
                         ":="
                         (Term.byTactic
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented
                            [(Tactic.change
                              "change"
                              (Term.arrow («term_=_» `z "=" (num "0")) "→" `False)
                              [(Tactic.location "at" (Tactic.locationHyp [`z_ne_0] []))])
                             []
                             (Std.Tactic.tacticRwa__
                              "rwa"
                              (Tactic.rwRuleSeq
                               "["
                               [(Tactic.rwRule
                                 [(patternIgnore (token.«← » "←"))]
                                 `inner_self_eq_zero)]
                               "]")
                              [(Tactic.location "at" (Tactic.locationHyp [`z_ne_0] []))])]))))))
                      []
                      (Tactic.fieldSimp
                       "field_simp"
                       []
                       []
                       []
                       [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `this)] "]")]
                       [])]))))]))))
            []
            (Tactic.exact "exact" `h₄)])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Submodule.orthogonal_eq_bot_iff)]
          "]")
         [(Tactic.location "at" (Tactic.locationHyp [`htriv] []))])
        []
        (Tactic.change
         "change"
         («term_≠_»
          (Analysis.InnerProductSpace.Basic.«term_ᗮ» `Y "ᗮ")
          "≠"
          (Order.BoundedOrder.«term⊥» "⊥"))
         [(Tactic.location "at" (Tactic.locationHyp [`htriv] []))])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Submodule.ne_bot_iff)] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`htriv] []))])
        []
        (Std.Tactic.obtain
         "obtain"
         [(Std.Tactic.RCases.rcasesPatMed
           [(Std.Tactic.RCases.rcasesPat.tuple
             "⟨"
             [(Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z)])
               [":" `E])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hz)])
               [":" («term_∈_» `z "∈" (Analysis.InnerProductSpace.Basic.«term_ᗮ» `Y "ᗮ"))])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z_ne_0)])
               [":" («term_≠_» `z "≠" (num "0"))])]
             "⟩")])]
         []
         [":=" [`htriv]])
        []
        (Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [(Algebra.Group.Defs.«term_•_»
            («term_/_»
             (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term_†» (Term.app `ℓ [`z]) "†")
             "/"
             (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫» "⟪" `z ", " `z "⟫"))
            " • "
            `z)
           ","
           (Term.hole "_")]
          "⟩"))
        []
        (Std.Tactic.Ext.«tacticExt___:_»
         "ext"
         [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))]
         [])
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`h₁ []]
           [(Term.typeSpec
             ":"
             («term_∈_»
              («term_-_»
               (Algebra.Group.Defs.«term_•_» (Term.app `ℓ [`z]) " • " `x)
               "-"
               (Algebra.Group.Defs.«term_•_» (Term.app `ℓ [`x]) " • " `z))
              "∈"
              `Y))]
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
                 [(Tactic.rwRule [] `LinearMap.mem_ker)
                  ","
                  (Tactic.rwRule [] `map_sub)
                  ","
                  (Tactic.rwRule [] `ContinuousLinearMap.map_smul)
                  ","
                  (Tactic.rwRule [] `ContinuousLinearMap.map_smul)
                  ","
                  (Tactic.rwRule [] `Algebra.id.smul_eq_mul)
                  ","
                  (Tactic.rwRule [] `Algebra.id.smul_eq_mul)
                  ","
                  (Tactic.rwRule [] `mul_comm)]
                 "]")
                [])
               []
               (Tactic.exact
                "exact"
                (Term.app `sub_self [(«term_*_» (Term.app `ℓ [`x]) "*" (Term.app `ℓ [`z]))]))]))))))
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`h₂ []]
           [(Term.typeSpec
             ":"
             («term_=_»
              («term_*_»
               (Term.app `ℓ [`z])
               "*"
               (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫» "⟪" `z ", " `x "⟫"))
              "="
              («term_*_»
               (Term.app `ℓ [`x])
               "*"
               (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                "⟪"
                `z
                ", "
                `z
                "⟫"))))]
           ":="
           (Std.Tactic.haveI
            "haveI"
            (Term.haveDecl
             (Term.haveIdDecl
              [`h₃ []]
              []
              ":="
              (calc
               "calc"
               (calcStep
                («term_=_»
                 (num "0")
                 "="
                 (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                  "⟪"
                  `z
                  ", "
                  («term_-_»
                   (Algebra.Group.Defs.«term_•_» (Term.app `ℓ [`z]) " • " `x)
                   "-"
                   (Algebra.Group.Defs.«term_•_» (Term.app `ℓ [`x]) " • " `z))
                  "⟫"))
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
                        []
                        (Term.app (Term.proj (Term.app `Y.mem_orthogonal' [`z]) "." `mp) [`hz]))]
                      "]")
                     [])
                    []
                    (Tactic.exact "exact" `h₁)]))))
               [(calcStep
                 («term_=_»
                  (Term.hole "_")
                  "="
                  («term_-_»
                   (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                    "⟪"
                    `z
                    ", "
                    (Algebra.Group.Defs.«term_•_» (Term.app `ℓ [`z]) " • " `x)
                    "⟫")
                   "-"
                   (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                    "⟪"
                    `z
                    ", "
                    (Algebra.Group.Defs.«term_•_» (Term.app `ℓ [`x]) " • " `z)
                    "⟫")))
                 ":="
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `inner_sub_right)] "]")
                      [])]))))
                (calcStep
                 («term_=_»
                  (Term.hole "_")
                  "="
                  («term_-_»
                   («term_*_»
                    (Term.app `ℓ [`z])
                    "*"
                    (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                     "⟪"
                     `z
                     ", "
                     `x
                     "⟫"))
                   "-"
                   («term_*_»
                    (Term.app `ℓ [`x])
                    "*"
                    (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                     "⟪"
                     `z
                     ", "
                     `z
                     "⟫"))))
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
                      ["[" [(Tactic.simpLemma [] [] `inner_smul_right)] "]"]
                      [])]))))])))
            []
            (Term.app `sub_eq_zero.mp [(Term.app `Eq.symm [`h₃])])))))
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`h₄ []]
           []
           ":="
           (calc
            "calc"
            (calcStep
             («term_=_»
              (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
               "⟪"
               (Algebra.Group.Defs.«term_•_»
                («term_/_»
                 (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term_†» (Term.app `ℓ [`z]) "†")
                 "/"
                 (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫» "⟪" `z ", " `z "⟫"))
                " • "
                `z)
               ", "
               `x
               "⟫")
              "="
              («term_*_»
               («term_/_»
                (Term.app `ℓ [`z])
                "/"
                (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫» "⟪" `z ", " `z "⟫"))
               "*"
               (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫» "⟪" `z ", " `x "⟫")))
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
                   [(Tactic.simpLemma [] [] `inner_smul_left)
                    ","
                    (Tactic.simpLemma [] [] `conj_conj)]
                   "]"]
                  [])]))))
            [(calcStep
              («term_=_»
               (Term.hole "_")
               "="
               («term_/_»
                («term_*_»
                 (Term.app `ℓ [`z])
                 "*"
                 (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫» "⟪" `z ", " `x "⟫"))
                "/"
                (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫» "⟪" `z ", " `z "⟫")))
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
                    [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `div_mul_eq_mul_div)]
                    "]")
                   [])]))))
             (calcStep
              («term_=_»
               (Term.hole "_")
               "="
               («term_/_»
                («term_*_»
                 (Term.app `ℓ [`x])
                 "*"
                 (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫» "⟪" `z ", " `z "⟫"))
                "/"
                (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫» "⟪" `z ", " `z "⟫")))
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h₂)] "]") [])]))))
             (calcStep
              («term_=_» (Term.hole "_") "=" (Term.app `ℓ [`x]))
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     []
                     [(Term.typeSpec
                       ":"
                       («term_≠_»
                        (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                         "⟪"
                         `z
                         ", "
                         `z
                         "⟫")
                        "≠"
                        (num "0")))]
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.change
                          "change"
                          (Term.arrow («term_=_» `z "=" (num "0")) "→" `False)
                          [(Tactic.location "at" (Tactic.locationHyp [`z_ne_0] []))])
                         []
                         (Std.Tactic.tacticRwa__
                          "rwa"
                          (Tactic.rwRuleSeq
                           "["
                           [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `inner_self_eq_zero)]
                           "]")
                          [(Tactic.location "at" (Tactic.locationHyp [`z_ne_0] []))])]))))))
                  []
                  (Tactic.fieldSimp
                   "field_simp"
                   []
                   []
                   []
                   [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `this)] "]")]
                   [])]))))]))))
        []
        (Tactic.exact "exact" `h₄)])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `h₄)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₄
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`h₄ []]
         []
         ":="
         (calc
          "calc"
          (calcStep
           («term_=_»
            (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
             "⟪"
             (Algebra.Group.Defs.«term_•_»
              («term_/_»
               (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term_†» (Term.app `ℓ [`z]) "†")
               "/"
               (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫» "⟪" `z ", " `z "⟫"))
              " • "
              `z)
             ", "
             `x
             "⟫")
            "="
            («term_*_»
             («term_/_»
              (Term.app `ℓ [`z])
              "/"
              (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫» "⟪" `z ", " `z "⟫"))
             "*"
             (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫» "⟪" `z ", " `x "⟫")))
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
                 [(Tactic.simpLemma [] [] `inner_smul_left) "," (Tactic.simpLemma [] [] `conj_conj)]
                 "]"]
                [])]))))
          [(calcStep
            («term_=_»
             (Term.hole "_")
             "="
             («term_/_»
              («term_*_»
               (Term.app `ℓ [`z])
               "*"
               (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫» "⟪" `z ", " `x "⟫"))
              "/"
              (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫» "⟪" `z ", " `z "⟫")))
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
                  [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `div_mul_eq_mul_div)]
                  "]")
                 [])]))))
           (calcStep
            («term_=_»
             (Term.hole "_")
             "="
             («term_/_»
              («term_*_»
               (Term.app `ℓ [`x])
               "*"
               (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫» "⟪" `z ", " `z "⟫"))
              "/"
              (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫» "⟪" `z ", " `z "⟫")))
            ":="
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h₂)] "]") [])]))))
           (calcStep
            («term_=_» (Term.hole "_") "=" (Term.app `ℓ [`x]))
            ":="
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   []
                   [(Term.typeSpec
                     ":"
                     («term_≠_»
                      (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                       "⟪"
                       `z
                       ", "
                       `z
                       "⟫")
                      "≠"
                      (num "0")))]
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Tactic.change
                        "change"
                        (Term.arrow («term_=_» `z "=" (num "0")) "→" `False)
                        [(Tactic.location "at" (Tactic.locationHyp [`z_ne_0] []))])
                       []
                       (Std.Tactic.tacticRwa__
                        "rwa"
                        (Tactic.rwRuleSeq
                         "["
                         [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `inner_self_eq_zero)]
                         "]")
                        [(Tactic.location "at" (Tactic.locationHyp [`z_ne_0] []))])]))))))
                []
                (Tactic.fieldSimp
                 "field_simp"
                 []
                 []
                 []
                 [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `this)] "]")]
                 [])]))))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calc
       "calc"
       (calcStep
        («term_=_»
         (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
          "⟪"
          (Algebra.Group.Defs.«term_•_»
           («term_/_»
            (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term_†» (Term.app `ℓ [`z]) "†")
            "/"
            (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫» "⟪" `z ", " `z "⟫"))
           " • "
           `z)
          ", "
          `x
          "⟫")
         "="
         («term_*_»
          («term_/_»
           (Term.app `ℓ [`z])
           "/"
           (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫» "⟪" `z ", " `z "⟫"))
          "*"
          (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫» "⟪" `z ", " `x "⟫")))
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
              [(Tactic.simpLemma [] [] `inner_smul_left) "," (Tactic.simpLemma [] [] `conj_conj)]
              "]"]
             [])]))))
       [(calcStep
         («term_=_»
          (Term.hole "_")
          "="
          («term_/_»
           («term_*_»
            (Term.app `ℓ [`z])
            "*"
            (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫» "⟪" `z ", " `x "⟫"))
           "/"
           (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫» "⟪" `z ", " `z "⟫")))
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
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `div_mul_eq_mul_div)]
               "]")
              [])]))))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          («term_/_»
           («term_*_»
            (Term.app `ℓ [`x])
            "*"
            (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫» "⟪" `z ", " `z "⟫"))
           "/"
           (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫» "⟪" `z ", " `z "⟫")))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h₂)] "]") [])]))))
        (calcStep
         («term_=_» (Term.hole "_") "=" (Term.app `ℓ [`x]))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec
                  ":"
                  («term_≠_»
                   (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
                    "⟪"
                    `z
                    ", "
                    `z
                    "⟫")
                   "≠"
                   (num "0")))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.change
                     "change"
                     (Term.arrow («term_=_» `z "=" (num "0")) "→" `False)
                     [(Tactic.location "at" (Tactic.locationHyp [`z_ne_0] []))])
                    []
                    (Std.Tactic.tacticRwa__
                     "rwa"
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `inner_self_eq_zero)]
                      "]")
                     [(Tactic.location "at" (Tactic.locationHyp [`z_ne_0] []))])]))))))
             []
             (Tactic.fieldSimp
              "field_simp"
              []
              []
              []
              [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `this)] "]")]
              [])]))))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               («term_≠_»
                (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫» "⟪" `z ", " `z "⟫")
                "≠"
                (num "0")))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.change
                  "change"
                  (Term.arrow («term_=_» `z "=" (num "0")) "→" `False)
                  [(Tactic.location "at" (Tactic.locationHyp [`z_ne_0] []))])
                 []
                 (Std.Tactic.tacticRwa__
                  "rwa"
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `inner_self_eq_zero)]
                   "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`z_ne_0] []))])]))))))
          []
          (Tactic.fieldSimp
           "field_simp"
           []
           []
           []
           [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `this)] "]")]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.fieldSimp
       "field_simp"
       []
       []
       []
       [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `this)] "]")]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
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
           («term_≠_»
            (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫» "⟪" `z ", " `z "⟫")
            "≠"
            (num "0")))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.change
              "change"
              (Term.arrow («term_=_» `z "=" (num "0")) "→" `False)
              [(Tactic.location "at" (Tactic.locationHyp [`z_ne_0] []))])
             []
             (Std.Tactic.tacticRwa__
              "rwa"
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `inner_self_eq_zero)]
               "]")
              [(Tactic.location "at" (Tactic.locationHyp [`z_ne_0] []))])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.change
           "change"
           (Term.arrow («term_=_» `z "=" (num "0")) "→" `False)
           [(Tactic.location "at" (Tactic.locationHyp [`z_ne_0] []))])
          []
          (Std.Tactic.tacticRwa__
           "rwa"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `inner_self_eq_zero)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`z_ne_0] []))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `inner_self_eq_zero)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`z_ne_0] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z_ne_0
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inner_self_eq_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       (Term.arrow («term_=_» `z "=" (num "0")) "→" `False)
       [(Tactic.location "at" (Tactic.locationHyp [`z_ne_0] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z_ne_0
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow («term_=_» `z "=" (num "0")) "→" `False)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `False
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      («term_=_» `z "=" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `z
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_»
       (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫» "⟪" `z ", " `z "⟫")
       "≠"
       (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫» "⟪" `z ", " `z "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»', expected 'InnerProductSpace.Analysis.InnerProductSpace.Dual.term⟪_,_⟫._@.Analysis.InnerProductSpace.Dual._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
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
    Fréchet-Riesz representation: any `ℓ` in the dual of a Hilbert space `E` is of the form
    `λ u, ⟪y, u⟫` for some `y : E`, i.e. `to_dual_map` is surjective.
    -/
  def
    toDual
    : E ≃ₗᵢ⋆[ 𝕜 ] NormedSpace.Dual 𝕜 E
    :=
      LinearIsometryEquiv.ofSurjective
        toDualMap 𝕜 E
          by
            intro ℓ
              set Y := LinearMap.ker ℓ with hY
              by_cases htriv : Y = ⊤
              ·
                have
                    hℓ
                      : ℓ = 0
                      :=
                      by
                        have h' := linear_map.ker_eq_top.mp htriv
                          rw [ ← coe_zero ] at h'
                          apply coe_injective
                          exact h'
                  exact ⟨ 0 , by simp [ hℓ ] ⟩
              ·
                rw [ ← Submodule.orthogonal_eq_bot_iff ] at htriv
                  change Y ᗮ ≠ ⊥ at htriv
                  rw [ Submodule.ne_bot_iff ] at htriv
                  obtain ⟨ z : E , hz : z ∈ Y ᗮ , z_ne_0 : z ≠ 0 ⟩ := htriv
                  refine' ⟨ ℓ z † / ⟪ z , z ⟫ • z , _ ⟩
                  ext x
                  have
                    h₁
                      : ℓ z • x - ℓ x • z ∈ Y
                      :=
                      by
                        rw
                            [
                              LinearMap.mem_ker
                                ,
                                map_sub
                                ,
                                ContinuousLinearMap.map_smul
                                ,
                                ContinuousLinearMap.map_smul
                                ,
                                Algebra.id.smul_eq_mul
                                ,
                                Algebra.id.smul_eq_mul
                                ,
                                mul_comm
                              ]
                          exact sub_self ℓ x * ℓ z
                  have
                    h₂
                      : ℓ z * ⟪ z , x ⟫ = ℓ x * ⟪ z , z ⟫
                      :=
                      haveI
                        h₃
                          :=
                          calc
                            0 = ⟪ z , ℓ z • x - ℓ x • z ⟫
                              :=
                              by rw [ Y.mem_orthogonal' z . mp hz ] exact h₁
                            _ = ⟪ z , ℓ z • x ⟫ - ⟪ z , ℓ x • z ⟫ := by rw [ inner_sub_right ]
                              _ = ℓ z * ⟪ z , x ⟫ - ℓ x * ⟪ z , z ⟫ := by simp [ inner_smul_right ]
                        sub_eq_zero.mp Eq.symm h₃
                  have
                    h₄
                      :=
                      calc
                        ⟪ ℓ z † / ⟪ z , z ⟫ • z , x ⟫ = ℓ z / ⟪ z , z ⟫ * ⟪ z , x ⟫
                          :=
                          by simp [ inner_smul_left , conj_conj ]
                        _ = ℓ z * ⟪ z , x ⟫ / ⟪ z , z ⟫ := by rw [ ← div_mul_eq_mul_div ]
                          _ = ℓ x * ⟪ z , z ⟫ / ⟪ z , z ⟫ := by rw [ h₂ ]
                          _ = ℓ x
                            :=
                            by
                              have
                                  : ⟪ z , z ⟫ ≠ 0
                                    :=
                                    by
                                      change z = 0 → False at z_ne_0
                                        rwa [ ← inner_self_eq_zero ] at z_ne_0
                                field_simp [ this ]
                  exact h₄
#align inner_product_space.to_dual InnerProductSpace.toDual

variable {𝕜} {E}

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
      (Command.declId `to_dual_apply [])
      (Command.declSig
       [(Term.implicitBinder "{" [`x `y] [":" `E] "}")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `toDual [`𝕜 `E `x `y])
         "="
         (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫» "⟪" `x ", " `y "⟫"))))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app `toDual [`𝕜 `E `x `y])
       "="
       (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫» "⟪" `x ", " `y "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫» "⟪" `x ", " `y "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»', expected 'InnerProductSpace.Analysis.InnerProductSpace.Dual.term⟪_,_⟫._@.Analysis.InnerProductSpace.Dual._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ] theorem to_dual_apply { x y : E } : toDual 𝕜 E x y = ⟪ x , y ⟫ := rfl
#align inner_product_space.to_dual_apply InnerProductSpace.to_dual_apply

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
      (Command.declId `to_dual_symm_apply [])
      (Command.declSig
       [(Term.implicitBinder "{" [`x] [":" `E] "}")
        (Term.implicitBinder "{" [`y] [":" (Term.app `NormedSpace.Dual [`𝕜 `E])] "}")]
       (Term.typeSpec
        ":"
        («term_=_»
         (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
          "⟪"
          (Term.app (Term.proj (Term.app `toDual [`𝕜 `E]) "." `symm) [`y])
          ", "
          `x
          "⟫")
         "="
         (Term.app `y [`x]))))
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
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `to_dual_apply)]
             "]")
            [])
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["[" [(Tactic.simpLemma [] [] `LinearIsometryEquiv.apply_symm_apply)] "]"]
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
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `to_dual_apply)]
            "]")
           [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["[" [(Tactic.simpLemma [] [] `LinearIsometryEquiv.apply_symm_apply)] "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["[" [(Tactic.simpLemma [] [] `LinearIsometryEquiv.apply_symm_apply)] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearIsometryEquiv.apply_symm_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `to_dual_apply)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `to_dual_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
        "⟪"
        (Term.app (Term.proj (Term.app `toDual [`𝕜 `E]) "." `symm) [`y])
        ", "
        `x
        "⟫")
       "="
       (Term.app `y [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `y [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
       "⟪"
       (Term.app (Term.proj (Term.app `toDual [`𝕜 `E]) "." `symm) [`y])
       ", "
       `x
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»', expected 'InnerProductSpace.Analysis.InnerProductSpace.Dual.term⟪_,_⟫._@.Analysis.InnerProductSpace.Dual._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    to_dual_symm_apply
    { x : E } { y : NormedSpace.Dual 𝕜 E } : ⟪ toDual 𝕜 E . symm y , x ⟫ = y x
    := by rw [ ← to_dual_apply ] simp only [ LinearIsometryEquiv.apply_symm_apply ]
#align inner_product_space.to_dual_symm_apply InnerProductSpace.to_dual_symm_apply

variable {E 𝕜}

/-- Maps a bounded sesquilinear form to its continuous linear map,
given by interpreting the form as a map `B : E →L⋆[𝕜] normed_space.dual 𝕜 E`
and dualizing the result using `to_dual`.
-/
def continuousLinearMapOfBilin (B : E →L⋆[𝕜] E →L[𝕜] 𝕜) : E →L[𝕜] E :=
  comp (toDual 𝕜 E).symm.toContinuousLinearEquiv.toContinuousLinearMap B
#align
  inner_product_space.continuous_linear_map_of_bilin InnerProductSpace.continuousLinearMapOfBilin

-- mathport name: «expr ♯»
local postfix:1024 "♯" => continuousLinearMapOfBilin

variable (B : E →L⋆[𝕜] E →L[𝕜] 𝕜)

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
      (Command.declId `continuous_linear_map_of_bilin_apply [])
      (Command.declSig
       [(Term.explicitBinder "(" [`v `w] [":" `E] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
          "⟪"
          (Term.app (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term_♯» `B "♯") [`v])
          ", "
          `w
          "⟫")
         "="
         (Term.app `B [`v `w]))))
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
            ["[" [(Tactic.simpLemma [] [] `continuous_linear_map_of_bilin)] "]"]
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
           ["[" [(Tactic.simpLemma [] [] `continuous_linear_map_of_bilin)] "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["[" [(Tactic.simpLemma [] [] `continuous_linear_map_of_bilin)] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `continuous_linear_map_of_bilin
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
        "⟪"
        (Term.app (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term_♯» `B "♯") [`v])
        ", "
        `w
        "⟫")
       "="
       (Term.app `B [`v `w]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `B [`v `w])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `w
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `v
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `B
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»
       "⟪"
       (Term.app (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term_♯» `B "♯") [`v])
       ", "
       `w
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫»', expected 'InnerProductSpace.Analysis.InnerProductSpace.Dual.term⟪_,_⟫._@.Analysis.InnerProductSpace.Dual._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    continuous_linear_map_of_bilin_apply
    ( v w : E ) : ⟪ B ♯ v , w ⟫ = B v w
    := by simp [ continuous_linear_map_of_bilin ]
#align
  inner_product_space.continuous_linear_map_of_bilin_apply InnerProductSpace.continuous_linear_map_of_bilin_apply

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `unique_continuous_linear_map_of_bilin [])
      (Command.declSig
       [(Term.implicitBinder "{" [`v `f] [":" `E] "}")
        (Term.explicitBinder
         "("
         [`is_lax_milgram]
         [":"
          (Term.forall
           "∀"
           [`w]
           []
           ","
           («term_=_»
            (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term⟪_,_⟫» "⟪" `f ", " `w "⟫")
            "="
            (Term.app `B [`v `w])))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         `f
         "="
         (Term.app (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term_♯» `B "♯") [`v]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine' "refine'" (Term.app `ext_inner_right [`𝕜 (Term.hole "_")]))
           []
           (Tactic.intro "intro" [`w])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `continuous_linear_map_of_bilin_apply)] "]")
            [])
           []
           (Tactic.exact "exact" (Term.app `is_lax_milgram [`w]))])))
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
         [(Tactic.refine' "refine'" (Term.app `ext_inner_right [`𝕜 (Term.hole "_")]))
          []
          (Tactic.intro "intro" [`w])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `continuous_linear_map_of_bilin_apply)] "]")
           [])
          []
          (Tactic.exact "exact" (Term.app `is_lax_milgram [`w]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `is_lax_milgram [`w]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `is_lax_milgram [`w])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `w
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_lax_milgram
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `continuous_linear_map_of_bilin_apply)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `continuous_linear_map_of_bilin_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`w])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `w
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine' "refine'" (Term.app `ext_inner_right [`𝕜 (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ext_inner_right [`𝕜 (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `𝕜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ext_inner_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       `f
       "="
       (Term.app (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term_♯» `B "♯") [`v]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term_♯» `B "♯") [`v])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `v
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (InnerProductSpace.Analysis.InnerProductSpace.Dual.«term_♯» `B "♯")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'InnerProductSpace.Analysis.InnerProductSpace.Dual.«term_♯»', expected 'InnerProductSpace.Analysis.InnerProductSpace.Dual.term_♯._@.Analysis.InnerProductSpace.Dual._hyg.121'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  unique_continuous_linear_map_of_bilin
  { v f : E } ( is_lax_milgram : ∀ w , ⟪ f , w ⟫ = B v w ) : f = B ♯ v
  :=
    by
      refine' ext_inner_right 𝕜 _
        intro w
        rw [ continuous_linear_map_of_bilin_apply ]
        exact is_lax_milgram w
#align
  inner_product_space.unique_continuous_linear_map_of_bilin InnerProductSpace.unique_continuous_linear_map_of_bilin

end InnerProductSpace

