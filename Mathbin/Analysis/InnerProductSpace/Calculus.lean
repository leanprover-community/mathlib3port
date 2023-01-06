/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module analysis.inner_product_space.calculus
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.InnerProductSpace.PiL2
import Mathbin.Analysis.SpecialFunctions.Sqrt

/-!
# Calculus in inner product spaces

In this file we prove that the inner product and square of the norm in an inner space are
infinitely `ℝ`-smooth. In order to state these results, we need a `normed_space ℝ E`
instance. Though we can deduce this structure from `inner_product_space 𝕜 E`, this instance may be
not definitionally equal to some other “natural” instance. So, we assume `[normed_space ℝ E]`.

We also prove that functions to a `euclidean_space` are (higher) differentiable if and only if
their components are. This follows from the corresponding fact for finite product of normed spaces,
and from the equivalence of norms in finite dimensions.

## TODO

The last part of the file should be generalized to `pi_Lp`.
-/


noncomputable section

open IsROrC Real Filter

open BigOperators Classical TopologicalSpace

section DerivInner

variable {𝕜 E F : Type _} [IsROrC 𝕜]

variable [InnerProductSpace 𝕜 E] [InnerProductSpace ℝ F]

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

variable [NormedSpace ℝ E]

/-- Derivative of the inner product. -/
def fderivInnerClm (p : E × E) : E × E →L[ℝ] 𝕜 :=
  isBoundedBilinearMapInner.deriv p
#align fderiv_inner_clm fderivInnerClm

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
      (Command.declId `fderiv_inner_clm_apply [])
      (Command.declSig
       [(Term.explicitBinder "(" [`p `x] [":" («term_×_» `E "×" `E)] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app `fderivInnerClm [`p `x])
         "="
         («term_+_»
          (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
           "⟪"
           (Term.proj `p "." (fieldIdx "1"))
           ", "
           (Term.proj `x "." (fieldIdx "2"))
           "⟫")
          "+"
          (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
           "⟪"
           (Term.proj `x "." (fieldIdx "1"))
           ", "
           (Term.proj `p "." (fieldIdx "2"))
           "⟫")))))
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
       (Term.app `fderivInnerClm [`p `x])
       "="
       («term_+_»
        (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
         "⟪"
         (Term.proj `p "." (fieldIdx "1"))
         ", "
         (Term.proj `x "." (fieldIdx "2"))
         "⟫")
        "+"
        (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
         "⟪"
         (Term.proj `x "." (fieldIdx "1"))
         ", "
         (Term.proj `p "." (fieldIdx "2"))
         "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
        "⟪"
        (Term.proj `p "." (fieldIdx "1"))
        ", "
        (Term.proj `x "." (fieldIdx "2"))
        "⟫")
       "+"
       (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
        "⟪"
        (Term.proj `x "." (fieldIdx "1"))
        ", "
        (Term.proj `p "." (fieldIdx "2"))
        "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
       "⟪"
       (Term.proj `x "." (fieldIdx "1"))
       ", "
       (Term.proj `p "." (fieldIdx "2"))
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Calculus.term⟪_,_⟫._@.Analysis.InnerProductSpace.Calculus._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    fderiv_inner_clm_apply
    ( p x : E × E ) : fderivInnerClm p x = ⟪ p . 1 , x . 2 ⟫ + ⟪ x . 1 , p . 2 ⟫
    := rfl
#align fderiv_inner_clm_apply fderiv_inner_clm_apply

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `cont_diff_inner [])
      (Command.declSig
       [(Term.implicitBinder "{" [`n] [] "}")]
       (Term.typeSpec
        ":"
        (Term.app
         `ContDiff
         [(Data.Real.Basic.termℝ "ℝ")
          `n
          (Term.fun
           "fun"
           (Term.basicFun
            [`p]
            [(Term.typeSpec ":" («term_×_» `E "×" `E))]
            "=>"
            (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
             "⟪"
             (Term.proj `p "." (fieldIdx "1"))
             ", "
             (Term.proj `p "." (fieldIdx "2"))
             "⟫")))])))
      (Command.declValSimple ":=" (Term.proj `isBoundedBilinearMapInner "." `ContDiff) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `isBoundedBilinearMapInner "." `ContDiff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `isBoundedBilinearMapInner
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `ContDiff
       [(Data.Real.Basic.termℝ "ℝ")
        `n
        (Term.fun
         "fun"
         (Term.basicFun
          [`p]
          [(Term.typeSpec ":" («term_×_» `E "×" `E))]
          "=>"
          (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
           "⟪"
           (Term.proj `p "." (fieldIdx "1"))
           ", "
           (Term.proj `p "." (fieldIdx "2"))
           "⟫")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`p]
        [(Term.typeSpec ":" («term_×_» `E "×" `E))]
        "=>"
        (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
         "⟪"
         (Term.proj `p "." (fieldIdx "1"))
         ", "
         (Term.proj `p "." (fieldIdx "2"))
         "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
       "⟪"
       (Term.proj `p "." (fieldIdx "1"))
       ", "
       (Term.proj `p "." (fieldIdx "2"))
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Calculus.term⟪_,_⟫._@.Analysis.InnerProductSpace.Calculus._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  cont_diff_inner
  { n } : ContDiff ℝ n fun p : E × E => ⟪ p . 1 , p . 2 ⟫
  := isBoundedBilinearMapInner . ContDiff
#align cont_diff_inner cont_diff_inner

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `cont_diff_at_inner [])
      (Command.declSig
       [(Term.implicitBinder "{" [`p] [":" («term_×_» `E "×" `E)] "}")
        (Term.implicitBinder "{" [`n] [] "}")]
       (Term.typeSpec
        ":"
        (Term.app
         `ContDiffAt
         [(Data.Real.Basic.termℝ "ℝ")
          `n
          (Term.fun
           "fun"
           (Term.basicFun
            [`p]
            [(Term.typeSpec ":" («term_×_» `E "×" `E))]
            "=>"
            (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
             "⟪"
             (Term.proj `p "." (fieldIdx "1"))
             ", "
             (Term.proj `p "." (fieldIdx "2"))
             "⟫")))
          `p])))
      (Command.declValSimple ":=" (Term.proj `cont_diff_inner "." `ContDiffAt) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `cont_diff_inner "." `ContDiffAt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `cont_diff_inner
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `ContDiffAt
       [(Data.Real.Basic.termℝ "ℝ")
        `n
        (Term.fun
         "fun"
         (Term.basicFun
          [`p]
          [(Term.typeSpec ":" («term_×_» `E "×" `E))]
          "=>"
          (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
           "⟪"
           (Term.proj `p "." (fieldIdx "1"))
           ", "
           (Term.proj `p "." (fieldIdx "2"))
           "⟫")))
        `p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`p]
        [(Term.typeSpec ":" («term_×_» `E "×" `E))]
        "=>"
        (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
         "⟪"
         (Term.proj `p "." (fieldIdx "1"))
         ", "
         (Term.proj `p "." (fieldIdx "2"))
         "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
       "⟪"
       (Term.proj `p "." (fieldIdx "1"))
       ", "
       (Term.proj `p "." (fieldIdx "2"))
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Calculus.term⟪_,_⟫._@.Analysis.InnerProductSpace.Calculus._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  cont_diff_at_inner
  { p : E × E } { n } : ContDiffAt ℝ n fun p : E × E => ⟪ p . 1 , p . 2 ⟫ p
  := cont_diff_inner . ContDiffAt
#align cont_diff_at_inner cont_diff_at_inner

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `differentiable_inner [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `Differentiable
         [(Data.Real.Basic.termℝ "ℝ")
          (Term.fun
           "fun"
           (Term.basicFun
            [`p]
            [(Term.typeSpec ":" («term_×_» `E "×" `E))]
            "=>"
            (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
             "⟪"
             (Term.proj `p "." (fieldIdx "1"))
             ", "
             (Term.proj `p "." (fieldIdx "2"))
             "⟫")))])))
      (Command.declValSimple ":=" (Term.proj `isBoundedBilinearMapInner "." `DifferentiableAt) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `isBoundedBilinearMapInner "." `DifferentiableAt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `isBoundedBilinearMapInner
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Differentiable
       [(Data.Real.Basic.termℝ "ℝ")
        (Term.fun
         "fun"
         (Term.basicFun
          [`p]
          [(Term.typeSpec ":" («term_×_» `E "×" `E))]
          "=>"
          (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
           "⟪"
           (Term.proj `p "." (fieldIdx "1"))
           ", "
           (Term.proj `p "." (fieldIdx "2"))
           "⟫")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`p]
        [(Term.typeSpec ":" («term_×_» `E "×" `E))]
        "=>"
        (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
         "⟪"
         (Term.proj `p "." (fieldIdx "1"))
         ", "
         (Term.proj `p "." (fieldIdx "2"))
         "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
       "⟪"
       (Term.proj `p "." (fieldIdx "1"))
       ", "
       (Term.proj `p "." (fieldIdx "2"))
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Calculus.term⟪_,_⟫._@.Analysis.InnerProductSpace.Calculus._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  differentiable_inner
  : Differentiable ℝ fun p : E × E => ⟪ p . 1 , p . 2 ⟫
  := isBoundedBilinearMapInner . DifferentiableAt
#align differentiable_inner differentiable_inner

variable {G : Type _} [NormedAddCommGroup G] [NormedSpace ℝ G] {f g : G → E} {f' g' : G →L[ℝ] E}
  {s : Set G} {x : G} {n : ℕ∞}

include 𝕜

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `ContDiffWithinAt.inner [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`hf]
         [":" (Term.app `ContDiffWithinAt [(Data.Real.Basic.termℝ "ℝ") `n `f `s `x])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hg]
         [":" (Term.app `ContDiffWithinAt [(Data.Real.Basic.termℝ "ℝ") `n `g `s `x])]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `ContDiffWithinAt
         [(Data.Real.Basic.termℝ "ℝ")
          `n
          (Term.fun
           "fun"
           (Term.basicFun
            [`x]
            []
            "=>"
            (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
             "⟪"
             (Term.app `f [`x])
             ", "
             (Term.app `g [`x])
             "⟫")))
          `s
          `x])))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj `cont_diff_at_inner "." `comp_cont_diff_within_at)
        [`x (Term.app (Term.proj `hf "." `Prod) [`hg])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `cont_diff_at_inner "." `comp_cont_diff_within_at)
       [`x (Term.app (Term.proj `hf "." `Prod) [`hg])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `hf "." `Prod) [`hg])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `hf "." `Prod)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `hf "." `Prod) [`hg])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `cont_diff_at_inner "." `comp_cont_diff_within_at)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `cont_diff_at_inner
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `ContDiffWithinAt
       [(Data.Real.Basic.termℝ "ℝ")
        `n
        (Term.fun
         "fun"
         (Term.basicFun
          [`x]
          []
          "=>"
          (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
           "⟪"
           (Term.app `f [`x])
           ", "
           (Term.app `g [`x])
           "⟫")))
        `s
        `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
         "⟪"
         (Term.app `f [`x])
         ", "
         (Term.app `g [`x])
         "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
       "⟪"
       (Term.app `f [`x])
       ", "
       (Term.app `g [`x])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Calculus.term⟪_,_⟫._@.Analysis.InnerProductSpace.Calculus._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  ContDiffWithinAt.inner
  ( hf : ContDiffWithinAt ℝ n f s x ) ( hg : ContDiffWithinAt ℝ n g s x )
    : ContDiffWithinAt ℝ n fun x => ⟪ f x , g x ⟫ s x
  := cont_diff_at_inner . comp_cont_diff_within_at x hf . Prod hg
#align cont_diff_within_at.inner ContDiffWithinAt.inner

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `ContDiffAt.inner [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`hf]
         [":" (Term.app `ContDiffAt [(Data.Real.Basic.termℝ "ℝ") `n `f `x])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hg]
         [":" (Term.app `ContDiffAt [(Data.Real.Basic.termℝ "ℝ") `n `g `x])]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `ContDiffAt
         [(Data.Real.Basic.termℝ "ℝ")
          `n
          (Term.fun
           "fun"
           (Term.basicFun
            [`x]
            []
            "=>"
            (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
             "⟪"
             (Term.app `f [`x])
             ", "
             (Term.app `g [`x])
             "⟫")))
          `x])))
      (Command.declValSimple ":=" (Term.app (Term.proj `hf "." `inner) [`hg]) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `hf "." `inner) [`hg])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `hf "." `inner)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `ContDiffAt
       [(Data.Real.Basic.termℝ "ℝ")
        `n
        (Term.fun
         "fun"
         (Term.basicFun
          [`x]
          []
          "=>"
          (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
           "⟪"
           (Term.app `f [`x])
           ", "
           (Term.app `g [`x])
           "⟫")))
        `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
         "⟪"
         (Term.app `f [`x])
         ", "
         (Term.app `g [`x])
         "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
       "⟪"
       (Term.app `f [`x])
       ", "
       (Term.app `g [`x])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Calculus.term⟪_,_⟫._@.Analysis.InnerProductSpace.Calculus._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  ContDiffAt.inner
  ( hf : ContDiffAt ℝ n f x ) ( hg : ContDiffAt ℝ n g x ) : ContDiffAt ℝ n fun x => ⟪ f x , g x ⟫ x
  := hf . inner hg
#align cont_diff_at.inner ContDiffAt.inner

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `ContDiffOn.inner [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`hf]
         [":" (Term.app `ContDiffOn [(Data.Real.Basic.termℝ "ℝ") `n `f `s])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hg]
         [":" (Term.app `ContDiffOn [(Data.Real.Basic.termℝ "ℝ") `n `g `s])]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `ContDiffOn
         [(Data.Real.Basic.termℝ "ℝ")
          `n
          (Term.fun
           "fun"
           (Term.basicFun
            [`x]
            []
            "=>"
            (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
             "⟪"
             (Term.app `f [`x])
             ", "
             (Term.app `g [`x])
             "⟫")))
          `s])))
      (Command.declValSimple
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [`x `hx]
         []
         "=>"
         (Term.app (Term.proj (Term.app `hf [`x `hx]) "." `inner) [(Term.app `hg [`x `hx])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x `hx]
        []
        "=>"
        (Term.app (Term.proj (Term.app `hf [`x `hx]) "." `inner) [(Term.app `hg [`x `hx])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `hf [`x `hx]) "." `inner) [(Term.app `hg [`x `hx])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hg [`x `hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `hg [`x `hx]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `hf [`x `hx]) "." `inner)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `hf [`x `hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `hf [`x `hx]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `ContDiffOn
       [(Data.Real.Basic.termℝ "ℝ")
        `n
        (Term.fun
         "fun"
         (Term.basicFun
          [`x]
          []
          "=>"
          (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
           "⟪"
           (Term.app `f [`x])
           ", "
           (Term.app `g [`x])
           "⟫")))
        `s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
         "⟪"
         (Term.app `f [`x])
         ", "
         (Term.app `g [`x])
         "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
       "⟪"
       (Term.app `f [`x])
       ", "
       (Term.app `g [`x])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Calculus.term⟪_,_⟫._@.Analysis.InnerProductSpace.Calculus._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  ContDiffOn.inner
  ( hf : ContDiffOn ℝ n f s ) ( hg : ContDiffOn ℝ n g s ) : ContDiffOn ℝ n fun x => ⟪ f x , g x ⟫ s
  := fun x hx => hf x hx . inner hg x hx
#align cont_diff_on.inner ContDiffOn.inner

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `ContDiff.inner [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`hf]
         [":" (Term.app `ContDiff [(Data.Real.Basic.termℝ "ℝ") `n `f])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hg]
         [":" (Term.app `ContDiff [(Data.Real.Basic.termℝ "ℝ") `n `g])]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `ContDiff
         [(Data.Real.Basic.termℝ "ℝ")
          `n
          (Term.fun
           "fun"
           (Term.basicFun
            [`x]
            []
            "=>"
            (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
             "⟪"
             (Term.app `f [`x])
             ", "
             (Term.app `g [`x])
             "⟫")))])))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj `cont_diff_inner "." `comp)
        [(Term.app (Term.proj `hf "." `Prod) [`hg])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `cont_diff_inner "." `comp) [(Term.app (Term.proj `hf "." `Prod) [`hg])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `hf "." `Prod) [`hg])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `hf "." `Prod)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `hf "." `Prod) [`hg])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `cont_diff_inner "." `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `cont_diff_inner
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `ContDiff
       [(Data.Real.Basic.termℝ "ℝ")
        `n
        (Term.fun
         "fun"
         (Term.basicFun
          [`x]
          []
          "=>"
          (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
           "⟪"
           (Term.app `f [`x])
           ", "
           (Term.app `g [`x])
           "⟫")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
         "⟪"
         (Term.app `f [`x])
         ", "
         (Term.app `g [`x])
         "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
       "⟪"
       (Term.app `f [`x])
       ", "
       (Term.app `g [`x])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Calculus.term⟪_,_⟫._@.Analysis.InnerProductSpace.Calculus._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  ContDiff.inner
  ( hf : ContDiff ℝ n f ) ( hg : ContDiff ℝ n g ) : ContDiff ℝ n fun x => ⟪ f x , g x ⟫
  := cont_diff_inner . comp hf . Prod hg
#align cont_diff.inner ContDiff.inner

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `HasFderivWithinAt.inner [])
      (Command.declSig
       [(Term.explicitBinder "(" [`hf] [":" (Term.app `HasFderivWithinAt [`f `f' `s `x])] [] ")")
        (Term.explicitBinder "(" [`hg] [":" (Term.app `HasFderivWithinAt [`g `g' `s `x])] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `HasFderivWithinAt
         [(Term.fun
           "fun"
           (Term.basicFun
            [`t]
            []
            "=>"
            (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
             "⟪"
             (Term.app `f [`t])
             ", "
             (Term.app `g [`t])
             "⟫")))
          («term_<|_»
           (Term.proj
            (Term.app
             `fderivInnerClm
             [(Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")])
            "."
            `comp)
           "<|"
           (Term.app (Term.proj `f' "." `Prod) [`g']))
          `s
          `x])))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (Term.app
          (Term.proj `isBoundedBilinearMapInner "." `HasFderivAt)
          [(Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")])
         "."
         `compHasFderivWithinAt)
        [`x (Term.app (Term.proj `hf "." `Prod) [`hg])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app
         (Term.proj `isBoundedBilinearMapInner "." `HasFderivAt)
         [(Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")])
        "."
        `compHasFderivWithinAt)
       [`x (Term.app (Term.proj `hf "." `Prod) [`hg])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `hf "." `Prod) [`hg])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `hf "." `Prod)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `hf "." `Prod) [`hg])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        (Term.proj `isBoundedBilinearMapInner "." `HasFderivAt)
        [(Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")])
       "."
       `compHasFderivWithinAt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj `isBoundedBilinearMapInner "." `HasFderivAt)
       [(Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `g [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `isBoundedBilinearMapInner "." `HasFderivAt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `isBoundedBilinearMapInner
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj `isBoundedBilinearMapInner "." `HasFderivAt)
      [(Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `HasFderivWithinAt
       [(Term.fun
         "fun"
         (Term.basicFun
          [`t]
          []
          "=>"
          (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
           "⟪"
           (Term.app `f [`t])
           ", "
           (Term.app `g [`t])
           "⟫")))
        («term_<|_»
         (Term.proj
          (Term.app
           `fderivInnerClm
           [(Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")])
          "."
          `comp)
         "<|"
         (Term.app (Term.proj `f' "." `Prod) [`g']))
        `s
        `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_<|_»
       (Term.proj
        (Term.app
         `fderivInnerClm
         [(Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")])
        "."
        `comp)
       "<|"
       (Term.app (Term.proj `f' "." `Prod) [`g']))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `f' "." `Prod) [`g'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `f' "." `Prod)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj
       (Term.app
        `fderivInnerClm
        [(Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")])
       "."
       `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `fderivInnerClm
       [(Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `g [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fderivInnerClm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `fderivInnerClm [(Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_»
      (Term.proj
       (Term.paren
        "("
        (Term.app
         `fderivInnerClm
         [(Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")])
        ")")
       "."
       `comp)
      "<|"
      (Term.app (Term.proj `f' "." `Prod) [`g']))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`t]
        []
        "=>"
        (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
         "⟪"
         (Term.app `f [`t])
         ", "
         (Term.app `g [`t])
         "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
       "⟪"
       (Term.app `f [`t])
       ", "
       (Term.app `g [`t])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Calculus.term⟪_,_⟫._@.Analysis.InnerProductSpace.Calculus._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  HasFderivWithinAt.inner
  ( hf : HasFderivWithinAt f f' s x ) ( hg : HasFderivWithinAt g g' s x )
    :
      HasFderivWithinAt
        fun t => ⟪ f t , g t ⟫ fderivInnerClm ( f x , g x ) . comp <| f' . Prod g' s x
  := isBoundedBilinearMapInner . HasFderivAt ( f x , g x ) . compHasFderivWithinAt x hf . Prod hg
#align has_fderiv_within_at.inner HasFderivWithinAt.inner

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `HasStrictFderivAt.inner [])
      (Command.declSig
       [(Term.explicitBinder "(" [`hf] [":" (Term.app `HasStrictFderivAt [`f `f' `x])] [] ")")
        (Term.explicitBinder "(" [`hg] [":" (Term.app `HasStrictFderivAt [`g `g' `x])] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `HasStrictFderivAt
         [(Term.fun
           "fun"
           (Term.basicFun
            [`t]
            []
            "=>"
            (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
             "⟪"
             (Term.app `f [`t])
             ", "
             (Term.app `g [`t])
             "⟫")))
          («term_<|_»
           (Term.proj
            (Term.app
             `fderivInnerClm
             [(Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")])
            "."
            `comp)
           "<|"
           (Term.app (Term.proj `f' "." `Prod) [`g']))
          `x])))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (Term.app
          (Term.proj `isBoundedBilinearMapInner "." `HasStrictFderivAt)
          [(Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")])
         "."
         `comp)
        [`x (Term.app (Term.proj `hf "." `Prod) [`hg])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app
         (Term.proj `isBoundedBilinearMapInner "." `HasStrictFderivAt)
         [(Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")])
        "."
        `comp)
       [`x (Term.app (Term.proj `hf "." `Prod) [`hg])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `hf "." `Prod) [`hg])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `hf "." `Prod)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `hf "." `Prod) [`hg])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        (Term.proj `isBoundedBilinearMapInner "." `HasStrictFderivAt)
        [(Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")])
       "."
       `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj `isBoundedBilinearMapInner "." `HasStrictFderivAt)
       [(Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `g [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `isBoundedBilinearMapInner "." `HasStrictFderivAt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `isBoundedBilinearMapInner
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj `isBoundedBilinearMapInner "." `HasStrictFderivAt)
      [(Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `HasStrictFderivAt
       [(Term.fun
         "fun"
         (Term.basicFun
          [`t]
          []
          "=>"
          (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
           "⟪"
           (Term.app `f [`t])
           ", "
           (Term.app `g [`t])
           "⟫")))
        («term_<|_»
         (Term.proj
          (Term.app
           `fderivInnerClm
           [(Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")])
          "."
          `comp)
         "<|"
         (Term.app (Term.proj `f' "." `Prod) [`g']))
        `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_<|_»
       (Term.proj
        (Term.app
         `fderivInnerClm
         [(Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")])
        "."
        `comp)
       "<|"
       (Term.app (Term.proj `f' "." `Prod) [`g']))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `f' "." `Prod) [`g'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `f' "." `Prod)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj
       (Term.app
        `fderivInnerClm
        [(Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")])
       "."
       `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `fderivInnerClm
       [(Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `g [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fderivInnerClm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `fderivInnerClm [(Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_»
      (Term.proj
       (Term.paren
        "("
        (Term.app
         `fderivInnerClm
         [(Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")])
        ")")
       "."
       `comp)
      "<|"
      (Term.app (Term.proj `f' "." `Prod) [`g']))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`t]
        []
        "=>"
        (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
         "⟪"
         (Term.app `f [`t])
         ", "
         (Term.app `g [`t])
         "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
       "⟪"
       (Term.app `f [`t])
       ", "
       (Term.app `g [`t])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Calculus.term⟪_,_⟫._@.Analysis.InnerProductSpace.Calculus._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  HasStrictFderivAt.inner
  ( hf : HasStrictFderivAt f f' x ) ( hg : HasStrictFderivAt g g' x )
    : HasStrictFderivAt fun t => ⟪ f t , g t ⟫ fderivInnerClm ( f x , g x ) . comp <| f' . Prod g' x
  := isBoundedBilinearMapInner . HasStrictFderivAt ( f x , g x ) . comp x hf . Prod hg
#align has_strict_fderiv_at.inner HasStrictFderivAt.inner

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `HasFderivAt.inner [])
      (Command.declSig
       [(Term.explicitBinder "(" [`hf] [":" (Term.app `HasFderivAt [`f `f' `x])] [] ")")
        (Term.explicitBinder "(" [`hg] [":" (Term.app `HasFderivAt [`g `g' `x])] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `HasFderivAt
         [(Term.fun
           "fun"
           (Term.basicFun
            [`t]
            []
            "=>"
            (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
             "⟪"
             (Term.app `f [`t])
             ", "
             (Term.app `g [`t])
             "⟫")))
          («term_<|_»
           (Term.proj
            (Term.app
             `fderivInnerClm
             [(Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")])
            "."
            `comp)
           "<|"
           (Term.app (Term.proj `f' "." `Prod) [`g']))
          `x])))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (Term.app
          (Term.proj `isBoundedBilinearMapInner "." `HasFderivAt)
          [(Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")])
         "."
         `comp)
        [`x (Term.app (Term.proj `hf "." `Prod) [`hg])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app
         (Term.proj `isBoundedBilinearMapInner "." `HasFderivAt)
         [(Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")])
        "."
        `comp)
       [`x (Term.app (Term.proj `hf "." `Prod) [`hg])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `hf "." `Prod) [`hg])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `hf "." `Prod)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `hf "." `Prod) [`hg])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        (Term.proj `isBoundedBilinearMapInner "." `HasFderivAt)
        [(Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")])
       "."
       `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj `isBoundedBilinearMapInner "." `HasFderivAt)
       [(Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `g [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `isBoundedBilinearMapInner "." `HasFderivAt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `isBoundedBilinearMapInner
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj `isBoundedBilinearMapInner "." `HasFderivAt)
      [(Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `HasFderivAt
       [(Term.fun
         "fun"
         (Term.basicFun
          [`t]
          []
          "=>"
          (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
           "⟪"
           (Term.app `f [`t])
           ", "
           (Term.app `g [`t])
           "⟫")))
        («term_<|_»
         (Term.proj
          (Term.app
           `fderivInnerClm
           [(Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")])
          "."
          `comp)
         "<|"
         (Term.app (Term.proj `f' "." `Prod) [`g']))
        `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_<|_»
       (Term.proj
        (Term.app
         `fderivInnerClm
         [(Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")])
        "."
        `comp)
       "<|"
       (Term.app (Term.proj `f' "." `Prod) [`g']))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `f' "." `Prod) [`g'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `f' "." `Prod)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj
       (Term.app
        `fderivInnerClm
        [(Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")])
       "."
       `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `fderivInnerClm
       [(Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `g [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `fderivInnerClm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `fderivInnerClm [(Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_»
      (Term.proj
       (Term.paren
        "("
        (Term.app
         `fderivInnerClm
         [(Term.tuple "(" [(Term.app `f [`x]) "," [(Term.app `g [`x])]] ")")])
        ")")
       "."
       `comp)
      "<|"
      (Term.app (Term.proj `f' "." `Prod) [`g']))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`t]
        []
        "=>"
        (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
         "⟪"
         (Term.app `f [`t])
         ", "
         (Term.app `g [`t])
         "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
       "⟪"
       (Term.app `f [`t])
       ", "
       (Term.app `g [`t])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Calculus.term⟪_,_⟫._@.Analysis.InnerProductSpace.Calculus._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  HasFderivAt.inner
  ( hf : HasFderivAt f f' x ) ( hg : HasFderivAt g g' x )
    : HasFderivAt fun t => ⟪ f t , g t ⟫ fderivInnerClm ( f x , g x ) . comp <| f' . Prod g' x
  := isBoundedBilinearMapInner . HasFderivAt ( f x , g x ) . comp x hf . Prod hg
#align has_fderiv_at.inner HasFderivAt.inner

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `HasDerivWithinAt.inner [])
      (Command.declSig
       [(Term.implicitBinder "{" [`f `g] [":" (Term.arrow (Data.Real.Basic.termℝ "ℝ") "→" `E)] "}")
        (Term.implicitBinder "{" [`f' `g'] [":" `E] "}")
        (Term.implicitBinder "{" [`s] [":" (Term.app `Set [(Data.Real.Basic.termℝ "ℝ")])] "}")
        (Term.implicitBinder "{" [`x] [":" (Data.Real.Basic.termℝ "ℝ")] "}")
        (Term.explicitBinder "(" [`hf] [":" (Term.app `HasDerivWithinAt [`f `f' `s `x])] [] ")")
        (Term.explicitBinder "(" [`hg] [":" (Term.app `HasDerivWithinAt [`g `g' `s `x])] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `HasDerivWithinAt
         [(Term.fun
           "fun"
           (Term.basicFun
            [`t]
            []
            "=>"
            (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
             "⟪"
             (Term.app `f [`t])
             ", "
             (Term.app `g [`t])
             "⟫")))
          («term_+_»
           (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫» "⟪" (Term.app `f [`x]) ", " `g' "⟫")
           "+"
           (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫» "⟪" `f' ", " (Term.app `g [`x]) "⟫"))
          `s
          `x])))
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
             []
             []
             ["using"
              (Term.proj
               (Term.app `hf.has_fderiv_within_at.inner [`hg.has_fderiv_within_at])
               "."
               `HasDerivWithinAt)]))])))
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
            []
            []
            ["using"
             (Term.proj
              (Term.app `hf.has_fderiv_within_at.inner [`hg.has_fderiv_within_at])
              "."
              `HasDerivWithinAt)]))])))
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
        []
        ["using"
         (Term.proj
          (Term.app `hf.has_fderiv_within_at.inner [`hg.has_fderiv_within_at])
          "."
          `HasDerivWithinAt)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app `hf.has_fderiv_within_at.inner [`hg.has_fderiv_within_at])
       "."
       `HasDerivWithinAt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `hf.has_fderiv_within_at.inner [`hg.has_fderiv_within_at])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg.has_fderiv_within_at
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hf.has_fderiv_within_at.inner
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `hf.has_fderiv_within_at.inner [`hg.has_fderiv_within_at])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `HasDerivWithinAt
       [(Term.fun
         "fun"
         (Term.basicFun
          [`t]
          []
          "=>"
          (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
           "⟪"
           (Term.app `f [`t])
           ", "
           (Term.app `g [`t])
           "⟫")))
        («term_+_»
         (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫» "⟪" (Term.app `f [`x]) ", " `g' "⟫")
         "+"
         (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫» "⟪" `f' ", " (Term.app `g [`x]) "⟫"))
        `s
        `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_+_»
       (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫» "⟪" (Term.app `f [`x]) ", " `g' "⟫")
       "+"
       (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫» "⟪" `f' ", " (Term.app `g [`x]) "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫» "⟪" `f' ", " (Term.app `g [`x]) "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Calculus.term⟪_,_⟫._@.Analysis.InnerProductSpace.Calculus._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  HasDerivWithinAt.inner
  { f g : ℝ → E }
      { f' g' : E }
      { s : Set ℝ }
      { x : ℝ }
      ( hf : HasDerivWithinAt f f' s x )
      ( hg : HasDerivWithinAt g g' s x )
    : HasDerivWithinAt fun t => ⟪ f t , g t ⟫ ⟪ f x , g' ⟫ + ⟪ f' , g x ⟫ s x
  := by simpa using hf.has_fderiv_within_at.inner hg.has_fderiv_within_at . HasDerivWithinAt
#align has_deriv_within_at.inner HasDerivWithinAt.inner

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `HasDerivAt.inner [])
      (Command.declSig
       [(Term.implicitBinder "{" [`f `g] [":" (Term.arrow (Data.Real.Basic.termℝ "ℝ") "→" `E)] "}")
        (Term.implicitBinder "{" [`f' `g'] [":" `E] "}")
        (Term.implicitBinder "{" [`x] [":" (Data.Real.Basic.termℝ "ℝ")] "}")]
       (Term.typeSpec
        ":"
        (Term.arrow
         (Term.app `HasDerivAt [`f `f' `x])
         "→"
         (Term.arrow
          (Term.app `HasDerivAt [`g `g' `x])
          "→"
          (Term.app
           `HasDerivAt
           [(Term.fun
             "fun"
             (Term.basicFun
              [`t]
              []
              "=>"
              (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
               "⟪"
               (Term.app `f [`t])
               ", "
               (Term.app `g [`t])
               "⟫")))
            («term_+_»
             (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫» "⟪" (Term.app `f [`x]) ", " `g' "⟫")
             "+"
             (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫» "⟪" `f' ", " (Term.app `g [`x]) "⟫"))
            `x])))))
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
               [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `has_deriv_within_at_univ)]
               "]")]
             ["using" `HasDerivWithinAt.inner]))])))
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
              [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `has_deriv_within_at_univ)]
              "]")]
            ["using" `HasDerivWithinAt.inner]))])))
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
          [(Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `has_deriv_within_at_univ)]
          "]")]
        ["using" `HasDerivWithinAt.inner]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `HasDerivWithinAt.inner
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `has_deriv_within_at_univ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Term.app `HasDerivAt [`f `f' `x])
       "→"
       (Term.arrow
        (Term.app `HasDerivAt [`g `g' `x])
        "→"
        (Term.app
         `HasDerivAt
         [(Term.fun
           "fun"
           (Term.basicFun
            [`t]
            []
            "=>"
            (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
             "⟪"
             (Term.app `f [`t])
             ", "
             (Term.app `g [`t])
             "⟫")))
          («term_+_»
           (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫» "⟪" (Term.app `f [`x]) ", " `g' "⟫")
           "+"
           (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫» "⟪" `f' ", " (Term.app `g [`x]) "⟫"))
          `x])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow
       (Term.app `HasDerivAt [`g `g' `x])
       "→"
       (Term.app
        `HasDerivAt
        [(Term.fun
          "fun"
          (Term.basicFun
           [`t]
           []
           "=>"
           (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
            "⟪"
            (Term.app `f [`t])
            ", "
            (Term.app `g [`t])
            "⟫")))
         («term_+_»
          (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫» "⟪" (Term.app `f [`x]) ", " `g' "⟫")
          "+"
          (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫» "⟪" `f' ", " (Term.app `g [`x]) "⟫"))
         `x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `HasDerivAt
       [(Term.fun
         "fun"
         (Term.basicFun
          [`t]
          []
          "=>"
          (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
           "⟪"
           (Term.app `f [`t])
           ", "
           (Term.app `g [`t])
           "⟫")))
        («term_+_»
         (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫» "⟪" (Term.app `f [`x]) ", " `g' "⟫")
         "+"
         (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫» "⟪" `f' ", " (Term.app `g [`x]) "⟫"))
        `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_+_»
       (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫» "⟪" (Term.app `f [`x]) ", " `g' "⟫")
       "+"
       (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫» "⟪" `f' ", " (Term.app `g [`x]) "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫» "⟪" `f' ", " (Term.app `g [`x]) "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Calculus.term⟪_,_⟫._@.Analysis.InnerProductSpace.Calculus._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  HasDerivAt.inner
  { f g : ℝ → E } { f' g' : E } { x : ℝ }
    :
      HasDerivAt f f' x
        →
        HasDerivAt g g' x → HasDerivAt fun t => ⟪ f t , g t ⟫ ⟪ f x , g' ⟫ + ⟪ f' , g x ⟫ x
  := by simpa only [ ← has_deriv_within_at_univ ] using HasDerivWithinAt.inner
#align has_deriv_at.inner HasDerivAt.inner

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `DifferentiableWithinAt.inner [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`hf]
         [":" (Term.app `DifferentiableWithinAt [(Data.Real.Basic.termℝ "ℝ") `f `s `x])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hg]
         [":" (Term.app `DifferentiableWithinAt [(Data.Real.Basic.termℝ "ℝ") `g `s `x])]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `DifferentiableWithinAt
         [(Data.Real.Basic.termℝ "ℝ")
          (Term.fun
           "fun"
           (Term.basicFun
            [`x]
            []
            "=>"
            (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
             "⟪"
             (Term.app `f [`x])
             ", "
             (Term.app `g [`x])
             "⟫")))
          `s
          `x])))
      (Command.declValSimple
       ":="
       (Term.proj
        (Term.app
         (Term.proj
          (Term.proj (Term.app `differentiable_inner [(Term.hole "_")]) "." `HasFderivAt)
          "."
          `compHasFderivWithinAt)
         [`x (Term.proj (Term.app (Term.proj `hf "." `Prod) [`hg]) "." `HasFderivWithinAt)])
        "."
        `DifferentiableWithinAt)
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        (Term.proj
         (Term.proj (Term.app `differentiable_inner [(Term.hole "_")]) "." `HasFderivAt)
         "."
         `compHasFderivWithinAt)
        [`x (Term.proj (Term.app (Term.proj `hf "." `Prod) [`hg]) "." `HasFderivWithinAt)])
       "."
       `DifferentiableWithinAt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj
        (Term.proj (Term.app `differentiable_inner [(Term.hole "_")]) "." `HasFderivAt)
        "."
        `compHasFderivWithinAt)
       [`x (Term.proj (Term.app (Term.proj `hf "." `Prod) [`hg]) "." `HasFderivWithinAt)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app (Term.proj `hf "." `Prod) [`hg]) "." `HasFderivWithinAt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `hf "." `Prod) [`hg])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `hf "." `Prod)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `hf "." `Prod) [`hg])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.proj (Term.app `differentiable_inner [(Term.hole "_")]) "." `HasFderivAt)
       "."
       `compHasFderivWithinAt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app `differentiable_inner [(Term.hole "_")]) "." `HasFderivAt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `differentiable_inner [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `differentiable_inner
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `differentiable_inner [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj
       (Term.proj
        (Term.paren "(" (Term.app `differentiable_inner [(Term.hole "_")]) ")")
        "."
        `HasFderivAt)
       "."
       `compHasFderivWithinAt)
      [`x
       (Term.proj
        (Term.paren "(" (Term.app (Term.proj `hf "." `Prod) [`hg]) ")")
        "."
        `HasFderivWithinAt)])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `DifferentiableWithinAt
       [(Data.Real.Basic.termℝ "ℝ")
        (Term.fun
         "fun"
         (Term.basicFun
          [`x]
          []
          "=>"
          (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
           "⟪"
           (Term.app `f [`x])
           ", "
           (Term.app `g [`x])
           "⟫")))
        `s
        `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
         "⟪"
         (Term.app `f [`x])
         ", "
         (Term.app `g [`x])
         "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
       "⟪"
       (Term.app `f [`x])
       ", "
       (Term.app `g [`x])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Calculus.term⟪_,_⟫._@.Analysis.InnerProductSpace.Calculus._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  DifferentiableWithinAt.inner
  ( hf : DifferentiableWithinAt ℝ f s x ) ( hg : DifferentiableWithinAt ℝ g s x )
    : DifferentiableWithinAt ℝ fun x => ⟪ f x , g x ⟫ s x
  :=
    differentiable_inner _ . HasFderivAt . compHasFderivWithinAt x hf . Prod hg . HasFderivWithinAt
      .
      DifferentiableWithinAt
#align differentiable_within_at.inner DifferentiableWithinAt.inner

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `DifferentiableAt.inner [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`hf]
         [":" (Term.app `DifferentiableAt [(Data.Real.Basic.termℝ "ℝ") `f `x])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hg]
         [":" (Term.app `DifferentiableAt [(Data.Real.Basic.termℝ "ℝ") `g `x])]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `DifferentiableAt
         [(Data.Real.Basic.termℝ "ℝ")
          (Term.fun
           "fun"
           (Term.basicFun
            [`x]
            []
            "=>"
            (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
             "⟪"
             (Term.app `f [`x])
             ", "
             (Term.app `g [`x])
             "⟫")))
          `x])))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj (Term.app `differentiable_inner [(Term.hole "_")]) "." `comp)
        [`x (Term.app (Term.proj `hf "." `Prod) [`hg])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `differentiable_inner [(Term.hole "_")]) "." `comp)
       [`x (Term.app (Term.proj `hf "." `Prod) [`hg])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `hf "." `Prod) [`hg])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `hf "." `Prod)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `hf "." `Prod) [`hg])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `differentiable_inner [(Term.hole "_")]) "." `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `differentiable_inner [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `differentiable_inner
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `differentiable_inner [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `DifferentiableAt
       [(Data.Real.Basic.termℝ "ℝ")
        (Term.fun
         "fun"
         (Term.basicFun
          [`x]
          []
          "=>"
          (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
           "⟪"
           (Term.app `f [`x])
           ", "
           (Term.app `g [`x])
           "⟫")))
        `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
         "⟪"
         (Term.app `f [`x])
         ", "
         (Term.app `g [`x])
         "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
       "⟪"
       (Term.app `f [`x])
       ", "
       (Term.app `g [`x])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Calculus.term⟪_,_⟫._@.Analysis.InnerProductSpace.Calculus._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  DifferentiableAt.inner
  ( hf : DifferentiableAt ℝ f x ) ( hg : DifferentiableAt ℝ g x )
    : DifferentiableAt ℝ fun x => ⟪ f x , g x ⟫ x
  := differentiable_inner _ . comp x hf . Prod hg
#align differentiable_at.inner DifferentiableAt.inner

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `DifferentiableOn.inner [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`hf]
         [":" (Term.app `DifferentiableOn [(Data.Real.Basic.termℝ "ℝ") `f `s])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hg]
         [":" (Term.app `DifferentiableOn [(Data.Real.Basic.termℝ "ℝ") `g `s])]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `DifferentiableOn
         [(Data.Real.Basic.termℝ "ℝ")
          (Term.fun
           "fun"
           (Term.basicFun
            [`x]
            []
            "=>"
            (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
             "⟪"
             (Term.app `f [`x])
             ", "
             (Term.app `g [`x])
             "⟫")))
          `s])))
      (Command.declValSimple
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [`x `hx]
         []
         "=>"
         (Term.app (Term.proj (Term.app `hf [`x `hx]) "." `inner) [(Term.app `hg [`x `hx])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x `hx]
        []
        "=>"
        (Term.app (Term.proj (Term.app `hf [`x `hx]) "." `inner) [(Term.app `hg [`x `hx])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `hf [`x `hx]) "." `inner) [(Term.app `hg [`x `hx])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hg [`x `hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `hg [`x `hx]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `hf [`x `hx]) "." `inner)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `hf [`x `hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `hf [`x `hx]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `DifferentiableOn
       [(Data.Real.Basic.termℝ "ℝ")
        (Term.fun
         "fun"
         (Term.basicFun
          [`x]
          []
          "=>"
          (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
           "⟪"
           (Term.app `f [`x])
           ", "
           (Term.app `g [`x])
           "⟫")))
        `s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
         "⟪"
         (Term.app `f [`x])
         ", "
         (Term.app `g [`x])
         "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
       "⟪"
       (Term.app `f [`x])
       ", "
       (Term.app `g [`x])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Calculus.term⟪_,_⟫._@.Analysis.InnerProductSpace.Calculus._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  DifferentiableOn.inner
  ( hf : DifferentiableOn ℝ f s ) ( hg : DifferentiableOn ℝ g s )
    : DifferentiableOn ℝ fun x => ⟪ f x , g x ⟫ s
  := fun x hx => hf x hx . inner hg x hx
#align differentiable_on.inner DifferentiableOn.inner

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `Differentiable.inner [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`hf]
         [":" (Term.app `Differentiable [(Data.Real.Basic.termℝ "ℝ") `f])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hg]
         [":" (Term.app `Differentiable [(Data.Real.Basic.termℝ "ℝ") `g])]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `Differentiable
         [(Data.Real.Basic.termℝ "ℝ")
          (Term.fun
           "fun"
           (Term.basicFun
            [`x]
            []
            "=>"
            (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
             "⟪"
             (Term.app `f [`x])
             ", "
             (Term.app `g [`x])
             "⟫")))])))
      (Command.declValSimple
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [`x]
         []
         "=>"
         (Term.app (Term.proj (Term.app `hf [`x]) "." `inner) [(Term.app `hg [`x])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (Term.app (Term.proj (Term.app `hf [`x]) "." `inner) [(Term.app `hg [`x])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `hf [`x]) "." `inner) [(Term.app `hg [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hg [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `hg [`x]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `hf [`x]) "." `inner)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `hf [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `hf [`x]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Differentiable
       [(Data.Real.Basic.termℝ "ℝ")
        (Term.fun
         "fun"
         (Term.basicFun
          [`x]
          []
          "=>"
          (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
           "⟪"
           (Term.app `f [`x])
           ", "
           (Term.app `g [`x])
           "⟫")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
         "⟪"
         (Term.app `f [`x])
         ", "
         (Term.app `g [`x])
         "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
       "⟪"
       (Term.app `f [`x])
       ", "
       (Term.app `g [`x])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Calculus.term⟪_,_⟫._@.Analysis.InnerProductSpace.Calculus._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  Differentiable.inner
  ( hf : Differentiable ℝ f ) ( hg : Differentiable ℝ g ) : Differentiable ℝ fun x => ⟪ f x , g x ⟫
  := fun x => hf x . inner hg x
#align differentiable.inner Differentiable.inner

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `fderiv_inner_apply [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`hf]
         [":" (Term.app `DifferentiableAt [(Data.Real.Basic.termℝ "ℝ") `f `x])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hg]
         [":" (Term.app `DifferentiableAt [(Data.Real.Basic.termℝ "ℝ") `g `x])]
         []
         ")")
        (Term.explicitBinder "(" [`y] [":" `G] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          `fderiv
          [(Data.Real.Basic.termℝ "ℝ")
           (Term.fun
            "fun"
            (Term.basicFun
             [`t]
             []
             "=>"
             (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
              "⟪"
              (Term.app `f [`t])
              ", "
              (Term.app `g [`t])
              "⟫")))
           `x
           `y])
         "="
         («term_+_»
          (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
           "⟪"
           (Term.app `f [`x])
           ", "
           (Term.app `fderiv [(Data.Real.Basic.termℝ "ℝ") `g `x `y])
           "⟫")
          "+"
          (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
           "⟪"
           (Term.app `fderiv [(Data.Real.Basic.termℝ "ℝ") `f `x `y])
           ", "
           (Term.app `g [`x])
           "⟫")))))
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
               []
               (Term.proj (Term.app `hf.has_fderiv_at.inner [`hg.has_fderiv_at]) "." `fderiv))]
             "]")
            [])
           []
           (Tactic.tacticRfl "rfl")])))
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
              []
              (Term.proj (Term.app `hf.has_fderiv_at.inner [`hg.has_fderiv_at]) "." `fderiv))]
            "]")
           [])
          []
          (Tactic.tacticRfl "rfl")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          []
          (Term.proj (Term.app `hf.has_fderiv_at.inner [`hg.has_fderiv_at]) "." `fderiv))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `hf.has_fderiv_at.inner [`hg.has_fderiv_at]) "." `fderiv)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `hf.has_fderiv_at.inner [`hg.has_fderiv_at])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hg.has_fderiv_at
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hf.has_fderiv_at.inner
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `hf.has_fderiv_at.inner [`hg.has_fderiv_at])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        `fderiv
        [(Data.Real.Basic.termℝ "ℝ")
         (Term.fun
          "fun"
          (Term.basicFun
           [`t]
           []
           "=>"
           (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
            "⟪"
            (Term.app `f [`t])
            ", "
            (Term.app `g [`t])
            "⟫")))
         `x
         `y])
       "="
       («term_+_»
        (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
         "⟪"
         (Term.app `f [`x])
         ", "
         (Term.app `fderiv [(Data.Real.Basic.termℝ "ℝ") `g `x `y])
         "⟫")
        "+"
        (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
         "⟪"
         (Term.app `fderiv [(Data.Real.Basic.termℝ "ℝ") `f `x `y])
         ", "
         (Term.app `g [`x])
         "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
        "⟪"
        (Term.app `f [`x])
        ", "
        (Term.app `fderiv [(Data.Real.Basic.termℝ "ℝ") `g `x `y])
        "⟫")
       "+"
       (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
        "⟪"
        (Term.app `fderiv [(Data.Real.Basic.termℝ "ℝ") `f `x `y])
        ", "
        (Term.app `g [`x])
        "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
       "⟪"
       (Term.app `fderiv [(Data.Real.Basic.termℝ "ℝ") `f `x `y])
       ", "
       (Term.app `g [`x])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Calculus.term⟪_,_⟫._@.Analysis.InnerProductSpace.Calculus._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  fderiv_inner_apply
  ( hf : DifferentiableAt ℝ f x ) ( hg : DifferentiableAt ℝ g x ) ( y : G )
    : fderiv ℝ fun t => ⟪ f t , g t ⟫ x y = ⟪ f x , fderiv ℝ g x y ⟫ + ⟪ fderiv ℝ f x y , g x ⟫
  := by rw [ hf.has_fderiv_at.inner hg.has_fderiv_at . fderiv ] rfl
#align fderiv_inner_apply fderiv_inner_apply

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `deriv_inner_apply [])
      (Command.declSig
       [(Term.implicitBinder "{" [`f `g] [":" (Term.arrow (Data.Real.Basic.termℝ "ℝ") "→" `E)] "}")
        (Term.implicitBinder "{" [`x] [":" (Data.Real.Basic.termℝ "ℝ")] "}")
        (Term.explicitBinder
         "("
         [`hf]
         [":" (Term.app `DifferentiableAt [(Data.Real.Basic.termℝ "ℝ") `f `x])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hg]
         [":" (Term.app `DifferentiableAt [(Data.Real.Basic.termℝ "ℝ") `g `x])]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          `deriv
          [(Term.fun
            "fun"
            (Term.basicFun
             [`t]
             []
             "=>"
             (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
              "⟪"
              (Term.app `f [`t])
              ", "
              (Term.app `g [`t])
              "⟫")))
           `x])
         "="
         («term_+_»
          (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
           "⟪"
           (Term.app `f [`x])
           ", "
           (Term.app `deriv [`g `x])
           "⟫")
          "+"
          (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
           "⟪"
           (Term.app `deriv [`f `x])
           ", "
           (Term.app `g [`x])
           "⟫")))))
      (Command.declValSimple
       ":="
       (Term.proj
        (Term.app
         (Term.proj (Term.proj `hf "." `HasDerivAt) "." `inner)
         [(Term.proj `hg "." `HasDerivAt)])
        "."
        `deriv)
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        (Term.proj (Term.proj `hf "." `HasDerivAt) "." `inner)
        [(Term.proj `hg "." `HasDerivAt)])
       "."
       `deriv)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj (Term.proj `hf "." `HasDerivAt) "." `inner)
       [(Term.proj `hg "." `HasDerivAt)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `hg "." `HasDerivAt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj `hf "." `HasDerivAt) "." `inner)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `hf "." `HasDerivAt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.proj `hf "." `HasDerivAt) "." `inner)
      [(Term.proj `hg "." `HasDerivAt)])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        `deriv
        [(Term.fun
          "fun"
          (Term.basicFun
           [`t]
           []
           "=>"
           (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
            "⟪"
            (Term.app `f [`t])
            ", "
            (Term.app `g [`t])
            "⟫")))
         `x])
       "="
       («term_+_»
        (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
         "⟪"
         (Term.app `f [`x])
         ", "
         (Term.app `deriv [`g `x])
         "⟫")
        "+"
        (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
         "⟪"
         (Term.app `deriv [`f `x])
         ", "
         (Term.app `g [`x])
         "⟫")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
        "⟪"
        (Term.app `f [`x])
        ", "
        (Term.app `deriv [`g `x])
        "⟫")
       "+"
       (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
        "⟪"
        (Term.app `deriv [`f `x])
        ", "
        (Term.app `g [`x])
        "⟫"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»
       "⟪"
       (Term.app `deriv [`f `x])
       ", "
       (Term.app `g [`x])
       "⟫")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.InnerProductSpace.Calculus.«term⟪_,_⟫»', expected 'Analysis.InnerProductSpace.Calculus.term⟪_,_⟫._@.Analysis.InnerProductSpace.Calculus._hyg.7'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  deriv_inner_apply
  { f g : ℝ → E } { x : ℝ } ( hf : DifferentiableAt ℝ f x ) ( hg : DifferentiableAt ℝ g x )
    : deriv fun t => ⟪ f t , g t ⟫ x = ⟪ f x , deriv g x ⟫ + ⟪ deriv f x , g x ⟫
  := hf . HasDerivAt . inner hg . HasDerivAt . deriv
#align deriv_inner_apply deriv_inner_apply

theorem cont_diff_norm_sq : ContDiff ℝ n fun x : E => ‖x‖ ^ 2 :=
  by
  simp only [sq, ← inner_self_eq_norm_mul_norm]
  exact (re_clm : 𝕜 →L[ℝ] ℝ).ContDiff.comp (cont_diff_id.inner cont_diff_id)
#align cont_diff_norm_sq cont_diff_norm_sq

theorem ContDiff.norm_sq (hf : ContDiff ℝ n f) : ContDiff ℝ n fun x => ‖f x‖ ^ 2 :=
  cont_diff_norm_sq.comp hf
#align cont_diff.norm_sq ContDiff.norm_sq

theorem ContDiffWithinAt.norm_sq (hf : ContDiffWithinAt ℝ n f s x) :
    ContDiffWithinAt ℝ n (fun y => ‖f y‖ ^ 2) s x :=
  cont_diff_norm_sq.ContDiffAt.comp_cont_diff_within_at x hf
#align cont_diff_within_at.norm_sq ContDiffWithinAt.norm_sq

theorem ContDiffAt.norm_sq (hf : ContDiffAt ℝ n f x) : ContDiffAt ℝ n (fun y => ‖f y‖ ^ 2) x :=
  hf.normSq
#align cont_diff_at.norm_sq ContDiffAt.norm_sq

theorem cont_diff_at_norm {x : E} (hx : x ≠ 0) : ContDiffAt ℝ n norm x :=
  by
  have : ‖id x‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_pos_iff.2 hx).ne'
  simpa only [id, sqrt_sq, norm_nonneg] using cont_diff_at_id.norm_sq.sqrt this
#align cont_diff_at_norm cont_diff_at_norm

theorem ContDiffAt.norm (hf : ContDiffAt ℝ n f x) (h0 : f x ≠ 0) :
    ContDiffAt ℝ n (fun y => ‖f y‖) x :=
  (cont_diff_at_norm h0).comp x hf
#align cont_diff_at.norm ContDiffAt.norm

theorem ContDiffAt.dist (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) (hne : f x ≠ g x) :
    ContDiffAt ℝ n (fun y => dist (f y) (g y)) x :=
  by
  simp only [dist_eq_norm]
  exact (hf.sub hg).norm (sub_ne_zero.2 hne)
#align cont_diff_at.dist ContDiffAt.dist

theorem ContDiffWithinAt.norm (hf : ContDiffWithinAt ℝ n f s x) (h0 : f x ≠ 0) :
    ContDiffWithinAt ℝ n (fun y => ‖f y‖) s x :=
  (cont_diff_at_norm h0).comp_cont_diff_within_at x hf
#align cont_diff_within_at.norm ContDiffWithinAt.norm

theorem ContDiffWithinAt.dist (hf : ContDiffWithinAt ℝ n f s x) (hg : ContDiffWithinAt ℝ n g s x)
    (hne : f x ≠ g x) : ContDiffWithinAt ℝ n (fun y => dist (f y) (g y)) s x :=
  by
  simp only [dist_eq_norm]
  exact (hf.sub hg).norm (sub_ne_zero.2 hne)
#align cont_diff_within_at.dist ContDiffWithinAt.dist

theorem ContDiffOn.norm_sq (hf : ContDiffOn ℝ n f s) : ContDiffOn ℝ n (fun y => ‖f y‖ ^ 2) s :=
  fun x hx => (hf x hx).normSq
#align cont_diff_on.norm_sq ContDiffOn.norm_sq

theorem ContDiffOn.norm (hf : ContDiffOn ℝ n f s) (h0 : ∀ x ∈ s, f x ≠ 0) :
    ContDiffOn ℝ n (fun y => ‖f y‖) s := fun x hx => (hf x hx).norm (h0 x hx)
#align cont_diff_on.norm ContDiffOn.norm

theorem ContDiffOn.dist (hf : ContDiffOn ℝ n f s) (hg : ContDiffOn ℝ n g s)
    (hne : ∀ x ∈ s, f x ≠ g x) : ContDiffOn ℝ n (fun y => dist (f y) (g y)) s := fun x hx =>
  (hf x hx).dist (hg x hx) (hne x hx)
#align cont_diff_on.dist ContDiffOn.dist

theorem ContDiff.norm (hf : ContDiff ℝ n f) (h0 : ∀ x, f x ≠ 0) : ContDiff ℝ n fun y => ‖f y‖ :=
  cont_diff_iff_cont_diff_at.2 fun x => hf.ContDiffAt.norm (h0 x)
#align cont_diff.norm ContDiff.norm

theorem ContDiff.dist (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) (hne : ∀ x, f x ≠ g x) :
    ContDiff ℝ n fun y => dist (f y) (g y) :=
  cont_diff_iff_cont_diff_at.2 fun x => hf.ContDiffAt.dist hg.ContDiffAt (hne x)
#align cont_diff.dist ContDiff.dist

omit 𝕜

theorem hasStrictFderivAtNormSq (x : F) :
    HasStrictFderivAt (fun x => ‖x‖ ^ 2) (bit0 (innerSL x : F →L[ℝ] ℝ)) x :=
  by
  simp only [sq, ← inner_self_eq_norm_mul_norm]
  convert (hasStrictFderivAtId x).inner (hasStrictFderivAtId x)
  ext y
  simp [bit0, real_inner_comm]
#align has_strict_fderiv_at_norm_sq hasStrictFderivAtNormSq

include 𝕜

theorem DifferentiableAt.norm_sq (hf : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun y => ‖f y‖ ^ 2) x :=
  (cont_diff_at_id.normSq.DifferentiableAt le_rfl).comp x hf
#align differentiable_at.norm_sq DifferentiableAt.norm_sq

theorem DifferentiableAt.norm (hf : DifferentiableAt ℝ f x) (h0 : f x ≠ 0) :
    DifferentiableAt ℝ (fun y => ‖f y‖) x :=
  ((cont_diff_at_norm h0).DifferentiableAt le_rfl).comp x hf
#align differentiable_at.norm DifferentiableAt.norm

theorem DifferentiableAt.dist (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hne : f x ≠ g x) : DifferentiableAt ℝ (fun y => dist (f y) (g y)) x :=
  by
  simp only [dist_eq_norm]
  exact (hf.sub hg).norm (sub_ne_zero.2 hne)
#align differentiable_at.dist DifferentiableAt.dist

theorem Differentiable.norm_sq (hf : Differentiable ℝ f) : Differentiable ℝ fun y => ‖f y‖ ^ 2 :=
  fun x => (hf x).normSq
#align differentiable.norm_sq Differentiable.norm_sq

theorem Differentiable.norm (hf : Differentiable ℝ f) (h0 : ∀ x, f x ≠ 0) :
    Differentiable ℝ fun y => ‖f y‖ := fun x => (hf x).norm (h0 x)
#align differentiable.norm Differentiable.norm

theorem Differentiable.dist (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hne : ∀ x, f x ≠ g x) : Differentiable ℝ fun y => dist (f y) (g y) := fun x =>
  (hf x).dist (hg x) (hne x)
#align differentiable.dist Differentiable.dist

theorem DifferentiableWithinAt.norm_sq (hf : DifferentiableWithinAt ℝ f s x) :
    DifferentiableWithinAt ℝ (fun y => ‖f y‖ ^ 2) s x :=
  (cont_diff_at_id.normSq.DifferentiableAt le_rfl).comp_differentiable_within_at x hf
#align differentiable_within_at.norm_sq DifferentiableWithinAt.norm_sq

theorem DifferentiableWithinAt.norm (hf : DifferentiableWithinAt ℝ f s x) (h0 : f x ≠ 0) :
    DifferentiableWithinAt ℝ (fun y => ‖f y‖) s x :=
  ((cont_diff_at_id.norm h0).DifferentiableAt le_rfl).comp_differentiable_within_at x hf
#align differentiable_within_at.norm DifferentiableWithinAt.norm

theorem DifferentiableWithinAt.dist (hf : DifferentiableWithinAt ℝ f s x)
    (hg : DifferentiableWithinAt ℝ g s x) (hne : f x ≠ g x) :
    DifferentiableWithinAt ℝ (fun y => dist (f y) (g y)) s x :=
  by
  simp only [dist_eq_norm]
  exact (hf.sub hg).norm (sub_ne_zero.2 hne)
#align differentiable_within_at.dist DifferentiableWithinAt.dist

theorem DifferentiableOn.norm_sq (hf : DifferentiableOn ℝ f s) :
    DifferentiableOn ℝ (fun y => ‖f y‖ ^ 2) s := fun x hx => (hf x hx).normSq
#align differentiable_on.norm_sq DifferentiableOn.norm_sq

theorem DifferentiableOn.norm (hf : DifferentiableOn ℝ f s) (h0 : ∀ x ∈ s, f x ≠ 0) :
    DifferentiableOn ℝ (fun y => ‖f y‖) s := fun x hx => (hf x hx).norm (h0 x hx)
#align differentiable_on.norm DifferentiableOn.norm

theorem DifferentiableOn.dist (hf : DifferentiableOn ℝ f s) (hg : DifferentiableOn ℝ g s)
    (hne : ∀ x ∈ s, f x ≠ g x) : DifferentiableOn ℝ (fun y => dist (f y) (g y)) s := fun x hx =>
  (hf x hx).dist (hg x hx) (hne x hx)
#align differentiable_on.dist DifferentiableOn.dist

end DerivInner

section PiLike

open ContinuousLinearMap

variable {𝕜 ι H : Type _} [IsROrC 𝕜] [NormedAddCommGroup H] [NormedSpace 𝕜 H] [Fintype ι]
  {f : H → EuclideanSpace 𝕜 ι} {f' : H →L[𝕜] EuclideanSpace 𝕜 ι} {t : Set H} {y : H}

theorem differentiable_within_at_euclidean :
    DifferentiableWithinAt 𝕜 f t y ↔ ∀ i, DifferentiableWithinAt 𝕜 (fun x => f x i) t y :=
  by
  rw [← (EuclideanSpace.equiv ι 𝕜).comp_differentiable_within_at_iff, differentiable_within_at_pi]
  rfl
#align differentiable_within_at_euclidean differentiable_within_at_euclidean

theorem differentiable_at_euclidean :
    DifferentiableAt 𝕜 f y ↔ ∀ i, DifferentiableAt 𝕜 (fun x => f x i) y :=
  by
  rw [← (EuclideanSpace.equiv ι 𝕜).comp_differentiable_at_iff, differentiable_at_pi]
  rfl
#align differentiable_at_euclidean differentiable_at_euclidean

theorem differentiable_on_euclidean :
    DifferentiableOn 𝕜 f t ↔ ∀ i, DifferentiableOn 𝕜 (fun x => f x i) t :=
  by
  rw [← (EuclideanSpace.equiv ι 𝕜).comp_differentiable_on_iff, differentiable_on_pi]
  rfl
#align differentiable_on_euclidean differentiable_on_euclidean

theorem differentiable_euclidean : Differentiable 𝕜 f ↔ ∀ i, Differentiable 𝕜 fun x => f x i :=
  by
  rw [← (EuclideanSpace.equiv ι 𝕜).comp_differentiable_iff, differentiable_pi]
  rfl
#align differentiable_euclidean differentiable_euclidean

theorem has_strict_fderiv_at_euclidean :
    HasStrictFderivAt f f' y ↔
      ∀ i, HasStrictFderivAt (fun x => f x i) (EuclideanSpace.proj i ∘L f') y :=
  by
  rw [← (EuclideanSpace.equiv ι 𝕜).comp_has_strict_fderiv_at_iff, has_strict_fderiv_at_pi']
  rfl
#align has_strict_fderiv_at_euclidean has_strict_fderiv_at_euclidean

theorem has_fderiv_within_at_euclidean :
    HasFderivWithinAt f f' t y ↔
      ∀ i, HasFderivWithinAt (fun x => f x i) (EuclideanSpace.proj i ∘L f') t y :=
  by
  rw [← (EuclideanSpace.equiv ι 𝕜).comp_has_fderiv_within_at_iff, has_fderiv_within_at_pi']
  rfl
#align has_fderiv_within_at_euclidean has_fderiv_within_at_euclidean

theorem cont_diff_within_at_euclidean {n : ℕ∞} :
    ContDiffWithinAt 𝕜 n f t y ↔ ∀ i, ContDiffWithinAt 𝕜 n (fun x => f x i) t y :=
  by
  rw [← (EuclideanSpace.equiv ι 𝕜).comp_cont_diff_within_at_iff, cont_diff_within_at_pi]
  rfl
#align cont_diff_within_at_euclidean cont_diff_within_at_euclidean

theorem cont_diff_at_euclidean {n : ℕ∞} :
    ContDiffAt 𝕜 n f y ↔ ∀ i, ContDiffAt 𝕜 n (fun x => f x i) y :=
  by
  rw [← (EuclideanSpace.equiv ι 𝕜).comp_cont_diff_at_iff, cont_diff_at_pi]
  rfl
#align cont_diff_at_euclidean cont_diff_at_euclidean

theorem cont_diff_on_euclidean {n : ℕ∞} :
    ContDiffOn 𝕜 n f t ↔ ∀ i, ContDiffOn 𝕜 n (fun x => f x i) t :=
  by
  rw [← (EuclideanSpace.equiv ι 𝕜).comp_cont_diff_on_iff, cont_diff_on_pi]
  rfl
#align cont_diff_on_euclidean cont_diff_on_euclidean

theorem cont_diff_euclidean {n : ℕ∞} : ContDiff 𝕜 n f ↔ ∀ i, ContDiff 𝕜 n fun x => f x i :=
  by
  rw [← (EuclideanSpace.equiv ι 𝕜).comp_cont_diff_iff, cont_diff_pi]
  rfl
#align cont_diff_euclidean cont_diff_euclidean

end PiLike

section DiffeomorphUnitBall

open Metric hiding mem_nhds_iff

variable {n : ℕ∞} {E : Type _} [InnerProductSpace ℝ E]

theorem cont_diff_homeomorph_unit_ball : (ContDiff ℝ n) fun x : E => (homeomorphUnitBall x : E) :=
  by
  suffices ContDiff ℝ n fun x => (1 + ‖x‖ ^ 2).sqrt⁻¹ by exact this.smul cont_diff_id
  have h : ∀ x : E, 0 < 1 + ‖x‖ ^ 2 := fun x => by positivity
  refine' ContDiff.inv _ fun x => real.sqrt_ne_zero'.mpr (h x)
  exact (cont_diff_const.add cont_diff_norm_sq).sqrt fun x => (h x).Ne.symm
#align cont_diff_homeomorph_unit_ball cont_diff_homeomorph_unit_ball

theorem cont_diff_on_homeomorph_unit_ball_symm {f : E → E}
    (h : ∀ (y) (hy : y ∈ ball (0 : E) 1), f y = homeomorphUnitBall.symm ⟨y, hy⟩) :
    ContDiffOn ℝ n f <| ball 0 1 := by
  intro y hy
  apply ContDiffAt.cont_diff_within_at
  have hf : f =ᶠ[𝓝 y] fun y => (1 - ‖(y : E)‖ ^ 2).sqrt⁻¹ • (y : E) :=
    by
    rw [eventually_eq_iff_exists_mem]
    refine'
      ⟨ball (0 : E) 1, mem_nhds_iff.mpr ⟨ball (0 : E) 1, Set.Subset.refl _, is_open_ball, hy⟩,
        fun z hz => _⟩
    rw [h z hz]
    rfl
  refine' ContDiffAt.congr_of_eventually_eq _ hf
  suffices ContDiffAt ℝ n (fun y => (1 - ‖(y : E)‖ ^ 2).sqrt⁻¹) y by exact this.smul cont_diff_at_id
  have h : 0 < 1 - ‖(y : E)‖ ^ 2 := by
    rwa [mem_ball_zero_iff, ← _root_.abs_one, ← abs_norm_eq_norm, ← sq_lt_sq, one_pow, ← sub_pos] at
      hy
  refine' ContDiffAt.inv _ (real.sqrt_ne_zero'.mpr h)
  refine' ContDiffAt.comp _ (cont_diff_at_sqrt h.ne.symm) _
  exact cont_diff_at_const.sub cont_diff_norm_sq.cont_diff_at
#align cont_diff_on_homeomorph_unit_ball_symm cont_diff_on_homeomorph_unit_ball_symm

end DiffeomorphUnitBall

