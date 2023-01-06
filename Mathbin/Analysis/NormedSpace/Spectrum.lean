/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux

! This file was ported from Lean 3 source module analysis.normed_space.spectrum
! leanprover-community/mathlib commit 26f081a2fb920140ed5bc5cc5344e84bcc7cb2b2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Algebra.Spectrum
import Mathbin.Analysis.SpecialFunctions.Pow
import Mathbin.Analysis.Complex.Liouville
import Mathbin.Analysis.Complex.Polynomial
import Mathbin.Analysis.Analytic.RadiusLiminf
import Mathbin.Topology.Algebra.Module.CharacterSpace
import Mathbin.Analysis.NormedSpace.Exponential

/-!
# The spectrum of elements in a complete normed algebra

This file contains the basic theory for the resolvent and spectrum of a Banach algebra.

## Main definitions

* `spectral_radius : ℝ≥0∞`: supremum of `‖k‖₊` for all `k ∈ spectrum 𝕜 a`
* `normed_ring.alg_equiv_complex_of_complete`: **Gelfand-Mazur theorem** For a complex
  Banach division algebra, the natural `algebra_map ℂ A` is an algebra isomorphism whose inverse
  is given by selecting the (unique) element of `spectrum ℂ a`

## Main statements

* `spectrum.is_open_resolvent_set`: the resolvent set is open.
* `spectrum.is_closed`: the spectrum is closed.
* `spectrum.subset_closed_ball_norm`: the spectrum is a subset of closed disk of radius
  equal to the norm.
* `spectrum.is_compact`: the spectrum is compact.
* `spectrum.spectral_radius_le_nnnorm`: the spectral radius is bounded above by the norm.
* `spectrum.has_deriv_at_resolvent`: the resolvent function is differentiable on the resolvent set.
* `spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius`: Gelfand's formula for the
  spectral radius in Banach algebras over `ℂ`.
* `spectrum.nonempty`: the spectrum of any element in a complex Banach algebra is nonempty.


## TODO

* compute all derivatives of `resolvent a`.

-/


open Ennreal Nnreal

/-- The *spectral radius* is the supremum of the `nnnorm` (`‖⬝‖₊`) of elements in the spectrum,
    coerced into an element of `ℝ≥0∞`. Note that it is possible for `spectrum 𝕜 a = ∅`. In this
    case, `spectral_radius a = 0`.  It is also possible that `spectrum 𝕜 a` be unbounded (though
    not for Banach algebras, see `spectrum.is_bounded`, below).  In this case,
    `spectral_radius a = ∞`. -/
noncomputable def spectralRadius (𝕜 : Type _) {A : Type _} [NormedField 𝕜] [Ring A] [Algebra 𝕜 A]
    (a : A) : ℝ≥0∞ :=
  ⨆ k ∈ spectrum 𝕜 a, ‖k‖₊
#align spectral_radius spectralRadius

variable {𝕜 : Type _} {A : Type _}

namespace spectrum

section SpectrumCompact

open Filter

variable [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]

-- mathport name: exprσ
local notation "σ" => spectrum 𝕜

-- mathport name: exprρ
local notation "ρ" => resolventSet 𝕜

-- mathport name: «expr↑ₐ»
local notation "↑ₐ" => algebraMap 𝕜 A

@[simp]
theorem SpectralRadius.of_subsingleton [Subsingleton A] (a : A) : spectralRadius 𝕜 a = 0 := by
  simp [spectralRadius]
#align spectrum.spectral_radius.of_subsingleton spectrum.SpectralRadius.of_subsingleton

@[simp]
theorem spectral_radius_zero : spectralRadius 𝕜 (0 : A) = 0 :=
  by
  nontriviality A
  simp [spectralRadius]
#align spectrum.spectral_radius_zero spectrum.spectral_radius_zero

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mem_resolvent_set_of_spectral_radius_lt [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a] [":" `A] "}")
        (Term.implicitBinder "{" [`k] [":" `𝕜] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          («term_<_»
           (Term.app `spectralRadius [`𝕜 `a])
           "<"
           (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" `k "‖₊"))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_∈_» `k "∈" (Term.app (spectrum.Analysis.NormedSpace.Spectrum.termρ "ρ") [`a]))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj `not_not "." `mp)
        [(Term.fun
          "fun"
          (Term.basicFun
           [`hn]
           []
           "=>"
           («term_<|_» (Term.proj `h "." `not_le) "<|" (Term.app `le_supᵢ₂ [`k `hn]))))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `not_not "." `mp)
       [(Term.fun
         "fun"
         (Term.basicFun
          [`hn]
          []
          "=>"
          («term_<|_» (Term.proj `h "." `not_le) "<|" (Term.app `le_supᵢ₂ [`k `hn]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`hn]
        []
        "=>"
        («term_<|_» (Term.proj `h "." `not_le) "<|" (Term.app `le_supᵢ₂ [`k `hn]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_» (Term.proj `h "." `not_le) "<|" (Term.app `le_supᵢ₂ [`k `hn]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `le_supᵢ₂ [`k `hn])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hn
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_supᵢ₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `h "." `not_le)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hn
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `not_not "." `mp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `not_not
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_∈_» `k "∈" (Term.app (spectrum.Analysis.NormedSpace.Spectrum.termρ "ρ") [`a]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (spectrum.Analysis.NormedSpace.Spectrum.termρ "ρ") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Analysis.NormedSpace.Spectrum.termρ "ρ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Analysis.NormedSpace.Spectrum.termρ', expected 'spectrum.Analysis.NormedSpace.Spectrum.termρ._@.Analysis.NormedSpace.Spectrum._hyg.520'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  mem_resolvent_set_of_spectral_radius_lt
  { a : A } { k : 𝕜 } ( h : spectralRadius 𝕜 a < ‖ k ‖₊ ) : k ∈ ρ a
  := not_not . mp fun hn => h . not_le <| le_supᵢ₂ k hn
#align
  spectrum.mem_resolvent_set_of_spectral_radius_lt spectrum.mem_resolvent_set_of_spectral_radius_lt

variable [CompleteSpace A]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `is_open_resolvent_set [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" `A] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app `IsOpen [(Term.app (spectrum.Analysis.NormedSpace.Spectrum.termρ "ρ") [`a])])))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj `Units.is_open "." `Preimage)
        [(Term.app
          (Term.proj (Term.app `continuous_algebra_map [`𝕜 `A]) "." `sub)
          [`continuous_const])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `Units.is_open "." `Preimage)
       [(Term.app
         (Term.proj (Term.app `continuous_algebra_map [`𝕜 `A]) "." `sub)
         [`continuous_const])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `continuous_algebra_map [`𝕜 `A]) "." `sub) [`continuous_const])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `continuous_const
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `continuous_algebra_map [`𝕜 `A]) "." `sub)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `continuous_algebra_map [`𝕜 `A])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝕜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `continuous_algebra_map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `continuous_algebra_map [`𝕜 `A])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.paren "(" (Term.app `continuous_algebra_map [`𝕜 `A]) ")") "." `sub)
      [`continuous_const])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `Units.is_open "." `Preimage)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Units.is_open
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `IsOpen [(Term.app (spectrum.Analysis.NormedSpace.Spectrum.termρ "ρ") [`a])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (spectrum.Analysis.NormedSpace.Spectrum.termρ "ρ") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Analysis.NormedSpace.Spectrum.termρ "ρ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Analysis.NormedSpace.Spectrum.termρ', expected 'spectrum.Analysis.NormedSpace.Spectrum.termρ._@.Analysis.NormedSpace.Spectrum._hyg.520'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  is_open_resolvent_set
  ( a : A ) : IsOpen ρ a
  := Units.is_open . Preimage continuous_algebra_map 𝕜 A . sub continuous_const
#align spectrum.is_open_resolvent_set spectrum.is_open_resolvent_set

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `is_closed [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" `A] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app `IsClosed [(Term.app (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ") [`a])])))
      (Command.declValSimple
       ":="
       (Term.proj (Term.app `is_open_resolvent_set [`a]) "." `is_closed_compl)
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `is_open_resolvent_set [`a]) "." `is_closed_compl)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `is_open_resolvent_set [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_open_resolvent_set
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `is_open_resolvent_set [`a])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `IsClosed [(Term.app (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ") [`a])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Analysis.NormedSpace.Spectrum.termσ', expected 'spectrum.Analysis.NormedSpace.Spectrum.termσ._@.Analysis.NormedSpace.Spectrum._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected theorem is_closed ( a : A ) : IsClosed σ a := is_open_resolvent_set a . is_closed_compl
#align spectrum.is_closed spectrum.is_closed

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mem_resolvent_set_of_norm_lt_mul [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a] [":" `A] "}")
        (Term.implicitBinder "{" [`k] [":" `𝕜] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          («term_<_»
           («term_*_»
            (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖")
            "*"
            (Analysis.Normed.Group.Basic.«term‖_‖»
             "‖"
             (Term.typeAscription "(" (num "1") ":" [`A] ")")
             "‖"))
           "<"
           (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `k "‖"))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_∈_» `k "∈" (Term.app (spectrum.Analysis.NormedSpace.Spectrum.termρ "ρ") [`a]))))
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
             [(Tactic.rwRule [] `resolventSet)
              ","
              (Tactic.rwRule [] `Set.mem_setOf_eq)
              ","
              (Tactic.rwRule [] `Algebra.algebra_map_eq_smul_one)]
             "]")
            [])
           []
           (Mathlib.Tactic.Nontriviality.nontriviality "nontriviality" [`A] [])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hk []]
              [(Term.typeSpec ":" («term_≠_» `k "≠" (num "0")))]
              ":="
              (Term.app
               `ne_zero_of_norm_ne_zero
               [(Term.proj
                 (Term.app
                  (Term.proj
                   (Term.app
                    `mul_nonneg
                    [(Term.app `norm_nonneg [(Term.hole "_")])
                     (Term.app `norm_nonneg [(Term.hole "_")])])
                   "."
                   `trans_lt)
                  [`h])
                 "."
                 `ne')]))))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `ku
              []
              []
              ":="
              (Term.app
               `Units.map
               [(Term.proj (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ» "↑ₐ") "." `toMonoidHom)
                (Term.app `Units.mk0 [`k `hk])]))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app
                `inv_inv
                [(Analysis.Normed.Group.Basic.«term‖_‖»
                  "‖"
                  (Term.typeAscription "(" (num "1") ":" [`A] ")")
                  "‖")]))
              ","
              (Tactic.rwRule
               []
               (Term.app
                `mul_inv_lt_iff
                [(«term_<|_»
                  (Term.proj `inv_pos "." (fieldIdx "2"))
                  "<|"
                  (Term.app
                   (Term.proj `norm_pos_iff "." (fieldIdx "2"))
                   [(Term.typeAscription
                     "("
                     `one_ne_zero
                     ":"
                     [(«term_≠_» (Term.typeAscription "(" (num "1") ":" [`A] ")") "≠" (num "0"))]
                     ")")]))]))]
             "]")
            [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hku []]
              [(Term.typeSpec
                ":"
                («term_<_»
                 (Analysis.Normed.Group.Basic.«term‖_‖» "‖" («term-_» "-" `a) "‖")
                 "<"
                 («term_⁻¹»
                  (Analysis.Normed.Group.Basic.«term‖_‖»
                   "‖"
                   (Term.typeAscription "(" (coeNotation "↑" («term_⁻¹» `ku "⁻¹")) ":" [`A] ")")
                   "‖")
                  "⁻¹")))]
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
                    [(Tactic.simpArgs
                      "["
                      [(Tactic.simpLemma [] [] `ku) "," (Tactic.simpLemma [] [] `norm_algebra_map)]
                      "]")]
                    ["using" `h]))]))))))
           []
           (Std.Tactic.Simpa.simpa
            "simpa"
            []
            []
            (Std.Tactic.Simpa.simpaArgsRest
             []
             []
             []
             [(Tactic.simpArgs
               "["
               [(Tactic.simpLemma [] [] `ku)
                ","
                (Tactic.simpLemma [] [] `sub_eq_add_neg)
                ","
                (Tactic.simpLemma [] [] `Algebra.algebra_map_eq_smul_one)]
               "]")]
             ["using" (Term.proj (Term.app `ku.add [(«term-_» "-" `a) `hku]) "." `IsUnit)]))])))
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
            [(Tactic.rwRule [] `resolventSet)
             ","
             (Tactic.rwRule [] `Set.mem_setOf_eq)
             ","
             (Tactic.rwRule [] `Algebra.algebra_map_eq_smul_one)]
            "]")
           [])
          []
          (Mathlib.Tactic.Nontriviality.nontriviality "nontriviality" [`A] [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hk []]
             [(Term.typeSpec ":" («term_≠_» `k "≠" (num "0")))]
             ":="
             (Term.app
              `ne_zero_of_norm_ne_zero
              [(Term.proj
                (Term.app
                 (Term.proj
                  (Term.app
                   `mul_nonneg
                   [(Term.app `norm_nonneg [(Term.hole "_")])
                    (Term.app `norm_nonneg [(Term.hole "_")])])
                  "."
                  `trans_lt)
                 [`h])
                "."
                `ne')]))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `ku
             []
             []
             ":="
             (Term.app
              `Units.map
              [(Term.proj (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ» "↑ₐ") "." `toMonoidHom)
               (Term.app `Units.mk0 [`k `hk])]))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app
               `inv_inv
               [(Analysis.Normed.Group.Basic.«term‖_‖»
                 "‖"
                 (Term.typeAscription "(" (num "1") ":" [`A] ")")
                 "‖")]))
             ","
             (Tactic.rwRule
              []
              (Term.app
               `mul_inv_lt_iff
               [(«term_<|_»
                 (Term.proj `inv_pos "." (fieldIdx "2"))
                 "<|"
                 (Term.app
                  (Term.proj `norm_pos_iff "." (fieldIdx "2"))
                  [(Term.typeAscription
                    "("
                    `one_ne_zero
                    ":"
                    [(«term_≠_» (Term.typeAscription "(" (num "1") ":" [`A] ")") "≠" (num "0"))]
                    ")")]))]))]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hku []]
             [(Term.typeSpec
               ":"
               («term_<_»
                (Analysis.Normed.Group.Basic.«term‖_‖» "‖" («term-_» "-" `a) "‖")
                "<"
                («term_⁻¹»
                 (Analysis.Normed.Group.Basic.«term‖_‖»
                  "‖"
                  (Term.typeAscription "(" (coeNotation "↑" («term_⁻¹» `ku "⁻¹")) ":" [`A] ")")
                  "‖")
                 "⁻¹")))]
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
                   [(Tactic.simpArgs
                     "["
                     [(Tactic.simpLemma [] [] `ku) "," (Tactic.simpLemma [] [] `norm_algebra_map)]
                     "]")]
                   ["using" `h]))]))))))
          []
          (Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            []
            [(Tactic.simpArgs
              "["
              [(Tactic.simpLemma [] [] `ku)
               ","
               (Tactic.simpLemma [] [] `sub_eq_add_neg)
               ","
               (Tactic.simpLemma [] [] `Algebra.algebra_map_eq_smul_one)]
              "]")]
            ["using" (Term.proj (Term.app `ku.add [(«term-_» "-" `a) `hku]) "." `IsUnit)]))])))
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
        [(Tactic.simpArgs
          "["
          [(Tactic.simpLemma [] [] `ku)
           ","
           (Tactic.simpLemma [] [] `sub_eq_add_neg)
           ","
           (Tactic.simpLemma [] [] `Algebra.algebra_map_eq_smul_one)]
          "]")]
        ["using" (Term.proj (Term.app `ku.add [(«term-_» "-" `a) `hku]) "." `IsUnit)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `ku.add [(«term-_» "-" `a) `hku]) "." `IsUnit)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `ku.add [(«term-_» "-" `a) `hku])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hku
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term-_» "-" `a)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 75, (some 75, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term-_» "-" `a) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ku.add
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `ku.add [(Term.paren "(" («term-_» "-" `a) ")") `hku])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Algebra.algebra_map_eq_smul_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_eq_add_neg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ku
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hku []]
         [(Term.typeSpec
           ":"
           («term_<_»
            (Analysis.Normed.Group.Basic.«term‖_‖» "‖" («term-_» "-" `a) "‖")
            "<"
            («term_⁻¹»
             (Analysis.Normed.Group.Basic.«term‖_‖»
              "‖"
              (Term.typeAscription "(" (coeNotation "↑" («term_⁻¹» `ku "⁻¹")) ":" [`A] ")")
              "‖")
             "⁻¹")))]
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
               [(Tactic.simpArgs
                 "["
                 [(Tactic.simpLemma [] [] `ku) "," (Tactic.simpLemma [] [] `norm_algebra_map)]
                 "]")]
               ["using" `h]))]))))))
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
            [(Tactic.simpArgs
              "["
              [(Tactic.simpLemma [] [] `ku) "," (Tactic.simpLemma [] [] `norm_algebra_map)]
              "]")]
            ["using" `h]))])))
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
        [(Tactic.simpArgs
          "["
          [(Tactic.simpLemma [] [] `ku) "," (Tactic.simpLemma [] [] `norm_algebra_map)]
          "]")]
        ["using" `h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_algebra_map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ku
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_»
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" («term-_» "-" `a) "‖")
       "<"
       («term_⁻¹»
        (Analysis.Normed.Group.Basic.«term‖_‖»
         "‖"
         (Term.typeAscription "(" (coeNotation "↑" («term_⁻¹» `ku "⁻¹")) ":" [`A] ")")
         "‖")
        "⁻¹"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⁻¹»
       (Analysis.Normed.Group.Basic.«term‖_‖»
        "‖"
        (Term.typeAscription "(" (coeNotation "↑" («term_⁻¹» `ku "⁻¹")) ":" [`A] ")")
        "‖")
       "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Analysis.Normed.Group.Basic.«term‖_‖»
       "‖"
       (Term.typeAscription "(" (coeNotation "↑" («term_⁻¹» `ku "⁻¹")) ":" [`A] ")")
       "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" (coeNotation "↑" («term_⁻¹» `ku "⁻¹")) ":" [`A] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (coeNotation "↑" («term_⁻¹» `ku "⁻¹"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⁻¹» `ku "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ku
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" («term-_» "-" `a) "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term-_» "-" `a)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app
           `inv_inv
           [(Analysis.Normed.Group.Basic.«term‖_‖»
             "‖"
             (Term.typeAscription "(" (num "1") ":" [`A] ")")
             "‖")]))
         ","
         (Tactic.rwRule
          []
          (Term.app
           `mul_inv_lt_iff
           [(«term_<|_»
             (Term.proj `inv_pos "." (fieldIdx "2"))
             "<|"
             (Term.app
              (Term.proj `norm_pos_iff "." (fieldIdx "2"))
              [(Term.typeAscription
                "("
                `one_ne_zero
                ":"
                [(«term_≠_» (Term.typeAscription "(" (num "1") ":" [`A] ")") "≠" (num "0"))]
                ")")]))]))]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mul_inv_lt_iff
       [(«term_<|_»
         (Term.proj `inv_pos "." (fieldIdx "2"))
         "<|"
         (Term.app
          (Term.proj `norm_pos_iff "." (fieldIdx "2"))
          [(Term.typeAscription
            "("
            `one_ne_zero
            ":"
            [(«term_≠_» (Term.typeAscription "(" (num "1") ":" [`A] ")") "≠" (num "0"))]
            ")")]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj `inv_pos "." (fieldIdx "2"))
       "<|"
       (Term.app
        (Term.proj `norm_pos_iff "." (fieldIdx "2"))
        [(Term.typeAscription
          "("
          `one_ne_zero
          ":"
          [(«term_≠_» (Term.typeAscription "(" (num "1") ":" [`A] ")") "≠" (num "0"))]
          ")")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `norm_pos_iff "." (fieldIdx "2"))
       [(Term.typeAscription
         "("
         `one_ne_zero
         ":"
         [(«term_≠_» (Term.typeAscription "(" (num "1") ":" [`A] ")") "≠" (num "0"))]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       `one_ne_zero
       ":"
       [(«term_≠_» (Term.typeAscription "(" (num "1") ":" [`A] ")") "≠" (num "0"))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» (Term.typeAscription "(" (num "1") ":" [`A] ")") "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription "(" (num "1") ":" [`A] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `norm_pos_iff "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `norm_pos_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `inv_pos "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `inv_pos
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_»
      (Term.proj `inv_pos "." (fieldIdx "2"))
      "<|"
      (Term.app
       (Term.proj `norm_pos_iff "." (fieldIdx "2"))
       [(Term.typeAscription
         "("
         `one_ne_zero
         ":"
         [(«term_≠_» (Term.typeAscription "(" (num "1") ":" [`A] ")") "≠" (num "0"))]
         ")")]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_inv_lt_iff
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `inv_inv
       [(Analysis.Normed.Group.Basic.«term‖_‖»
         "‖"
         (Term.typeAscription "(" (num "1") ":" [`A] ")")
         "‖")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term‖_‖»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term‖_‖»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖»
       "‖"
       (Term.typeAscription "(" (num "1") ":" [`A] ")")
       "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" (num "1") ":" [`A] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `inv_inv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticLet_
       "let"
       (Term.letDecl
        (Term.letIdDecl
         `ku
         []
         []
         ":="
         (Term.app
          `Units.map
          [(Term.proj (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ» "↑ₐ") "." `toMonoidHom)
           (Term.app `Units.mk0 [`k `hk])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Units.map
       [(Term.proj (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ» "↑ₐ") "." `toMonoidHom)
        (Term.app `Units.mk0 [`k `hk])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Units.mk0 [`k `hk])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hk
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Units.mk0
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Units.mk0 [`k `hk]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ» "↑ₐ") "." `toMonoidHom)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ» "↑ₐ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ»', expected 'spectrum.Analysis.NormedSpace.Spectrum.term↑ₐ._@.Analysis.NormedSpace.Spectrum._hyg.1016'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  mem_resolvent_set_of_norm_lt_mul
  { a : A } { k : 𝕜 } ( h : ‖ a ‖ * ‖ ( 1 : A ) ‖ < ‖ k ‖ ) : k ∈ ρ a
  :=
    by
      rw [ resolventSet , Set.mem_setOf_eq , Algebra.algebra_map_eq_smul_one ]
        nontriviality A
        have
          hk
            : k ≠ 0
            :=
            ne_zero_of_norm_ne_zero mul_nonneg norm_nonneg _ norm_nonneg _ . trans_lt h . ne'
        let ku := Units.map ↑ₐ . toMonoidHom Units.mk0 k hk
        rw
          [
            ← inv_inv ‖ ( 1 : A ) ‖
              ,
              mul_inv_lt_iff inv_pos . 2 <| norm_pos_iff . 2 ( one_ne_zero : ( 1 : A ) ≠ 0 )
            ]
          at h
        have hku : ‖ - a ‖ < ‖ ( ↑ ku ⁻¹ : A ) ‖ ⁻¹ := by simpa [ ku , norm_algebra_map ] using h
        simpa
          [ ku , sub_eq_add_neg , Algebra.algebra_map_eq_smul_one ] using ku.add - a hku . IsUnit
#align spectrum.mem_resolvent_set_of_norm_lt_mul spectrum.mem_resolvent_set_of_norm_lt_mul

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mem_resolvent_set_of_norm_lt [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `NormOneClass [`A]) "]")
        (Term.implicitBinder "{" [`a] [":" `A] "}")
        (Term.implicitBinder "{" [`k] [":" `𝕜] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          («term_<_»
           (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖")
           "<"
           (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `k "‖"))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_∈_» `k "∈" (Term.app (spectrum.Analysis.NormedSpace.Spectrum.termρ "ρ") [`a]))))
      (Command.declValSimple
       ":="
       (Term.app
        `mem_resolvent_set_of_norm_lt_mul
        [(Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Std.Tactic.tacticRwa__
              "rwa"
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `norm_one) "," (Tactic.rwRule [] `mul_one)]
               "]")
              [])])))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mem_resolvent_set_of_norm_lt_mul
       [(Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Std.Tactic.tacticRwa__
             "rwa"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `norm_one) "," (Tactic.rwRule [] `mul_one)]
              "]")
             [])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.tacticRwa__
           "rwa"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `norm_one) "," (Tactic.rwRule [] `mul_one)] "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `norm_one) "," (Tactic.rwRule [] `mul_one)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(Std.Tactic.tacticRwa__
          "rwa"
          (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `norm_one) "," (Tactic.rwRule [] `mul_one)] "]")
          [])])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mem_resolvent_set_of_norm_lt_mul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_∈_» `k "∈" (Term.app (spectrum.Analysis.NormedSpace.Spectrum.termρ "ρ") [`a]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (spectrum.Analysis.NormedSpace.Spectrum.termρ "ρ") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Analysis.NormedSpace.Spectrum.termρ "ρ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Analysis.NormedSpace.Spectrum.termρ', expected 'spectrum.Analysis.NormedSpace.Spectrum.termρ._@.Analysis.NormedSpace.Spectrum._hyg.520'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  mem_resolvent_set_of_norm_lt
  [ NormOneClass A ] { a : A } { k : 𝕜 } ( h : ‖ a ‖ < ‖ k ‖ ) : k ∈ ρ a
  := mem_resolvent_set_of_norm_lt_mul by rwa [ norm_one , mul_one ]
#align spectrum.mem_resolvent_set_of_norm_lt spectrum.mem_resolvent_set_of_norm_lt

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `norm_le_norm_mul_of_mem [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a] [":" `A] "}")
        (Term.implicitBinder "{" [`k] [":" `𝕜] "}")
        (Term.explicitBinder
         "("
         [`hk]
         [":" («term_∈_» `k "∈" (Term.app (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ") [`a]))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `k "‖")
         "≤"
         («term_*_»
          (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖")
          "*"
          (Analysis.Normed.Group.Basic.«term‖_‖»
           "‖"
           (Term.typeAscription "(" (num "1") ":" [`A] ")")
           "‖")))))
      (Command.declValSimple
       ":="
       («term_<|_» `le_of_not_lt "<|" (Term.app `mt [`mem_resolvent_set_of_norm_lt_mul `hk]))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_» `le_of_not_lt "<|" (Term.app `mt [`mem_resolvent_set_of_norm_lt_mul `hk]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mt [`mem_resolvent_set_of_norm_lt_mul `hk])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hk
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `mem_resolvent_set_of_norm_lt_mul
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `le_of_not_lt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≤_»
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `k "‖")
       "≤"
       («term_*_»
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖")
        "*"
        (Analysis.Normed.Group.Basic.«term‖_‖»
         "‖"
         (Term.typeAscription "(" (num "1") ":" [`A] ")")
         "‖")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖")
       "*"
       (Analysis.Normed.Group.Basic.«term‖_‖»
        "‖"
        (Term.typeAscription "(" (num "1") ":" [`A] ")")
        "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖»
       "‖"
       (Term.typeAscription "(" (num "1") ":" [`A] ")")
       "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" (num "1") ":" [`A] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `k "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_» `k "∈" (Term.app (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ") [`a]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Analysis.NormedSpace.Spectrum.termσ', expected 'spectrum.Analysis.NormedSpace.Spectrum.termσ._@.Analysis.NormedSpace.Spectrum._hyg.8'
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
  norm_le_norm_mul_of_mem
  { a : A } { k : 𝕜 } ( hk : k ∈ σ a ) : ‖ k ‖ ≤ ‖ a ‖ * ‖ ( 1 : A ) ‖
  := le_of_not_lt <| mt mem_resolvent_set_of_norm_lt_mul hk
#align spectrum.norm_le_norm_mul_of_mem spectrum.norm_le_norm_mul_of_mem

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `norm_le_norm_of_mem [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `NormOneClass [`A]) "]")
        (Term.implicitBinder "{" [`a] [":" `A] "}")
        (Term.implicitBinder "{" [`k] [":" `𝕜] "}")
        (Term.explicitBinder
         "("
         [`hk]
         [":" («term_∈_» `k "∈" (Term.app (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ") [`a]))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `k "‖")
         "≤"
         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖"))))
      (Command.declValSimple
       ":="
       («term_<|_» `le_of_not_lt "<|" (Term.app `mt [`mem_resolvent_set_of_norm_lt `hk]))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_» `le_of_not_lt "<|" (Term.app `mt [`mem_resolvent_set_of_norm_lt `hk]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mt [`mem_resolvent_set_of_norm_lt `hk])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hk
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `mem_resolvent_set_of_norm_lt
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `le_of_not_lt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≤_»
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `k "‖")
       "≤"
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `k "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_» `k "∈" (Term.app (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ") [`a]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Analysis.NormedSpace.Spectrum.termσ', expected 'spectrum.Analysis.NormedSpace.Spectrum.termσ._@.Analysis.NormedSpace.Spectrum._hyg.8'
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
  norm_le_norm_of_mem
  [ NormOneClass A ] { a : A } { k : 𝕜 } ( hk : k ∈ σ a ) : ‖ k ‖ ≤ ‖ a ‖
  := le_of_not_lt <| mt mem_resolvent_set_of_norm_lt hk
#align spectrum.norm_le_norm_of_mem spectrum.norm_le_norm_of_mem

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `subset_closed_ball_norm_mul [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" `A] [] ")")]
       (Term.typeSpec
        ":"
        («term_⊆_»
         (Term.app (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ") [`a])
         "⊆"
         (Term.app
          `Metric.closedBall
          [(Term.typeAscription "(" (num "0") ":" [`𝕜] ")")
           («term_*_»
            (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖")
            "*"
            (Analysis.Normed.Group.Basic.«term‖_‖»
             "‖"
             (Term.typeAscription "(" (num "1") ":" [`A] ")")
             "‖"))]))))
      (Command.declValSimple
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [`k `hk]
         []
         "=>"
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.simp
              "simp"
              []
              []
              []
              ["[" [(Tactic.simpLemma [] [] (Term.app `norm_le_norm_mul_of_mem [`hk]))] "]"]
              [])])))))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`k `hk]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.simp
             "simp"
             []
             []
             []
             ["[" [(Tactic.simpLemma [] [] (Term.app `norm_le_norm_mul_of_mem [`hk]))] "]"]
             [])])))))
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
           ["[" [(Tactic.simpLemma [] [] (Term.app `norm_le_norm_mul_of_mem [`hk]))] "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["[" [(Tactic.simpLemma [] [] (Term.app `norm_le_norm_mul_of_mem [`hk]))] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `norm_le_norm_mul_of_mem [`hk])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hk
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm_le_norm_mul_of_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_⊆_»
       (Term.app (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ") [`a])
       "⊆"
       (Term.app
        `Metric.closedBall
        [(Term.typeAscription "(" (num "0") ":" [`𝕜] ")")
         («term_*_»
          (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖")
          "*"
          (Analysis.Normed.Group.Basic.«term‖_‖»
           "‖"
           (Term.typeAscription "(" (num "1") ":" [`A] ")")
           "‖"))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Metric.closedBall
       [(Term.typeAscription "(" (num "0") ":" [`𝕜] ")")
        («term_*_»
         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖")
         "*"
         (Analysis.Normed.Group.Basic.«term‖_‖»
          "‖"
          (Term.typeAscription "(" (num "1") ":" [`A] ")")
          "‖"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖")
       "*"
       (Analysis.Normed.Group.Basic.«term‖_‖»
        "‖"
        (Term.typeAscription "(" (num "1") ":" [`A] ")")
        "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖»
       "‖"
       (Term.typeAscription "(" (num "1") ":" [`A] ")")
       "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" (num "1") ":" [`A] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_*_»
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖")
      "*"
      (Analysis.Normed.Group.Basic.«term‖_‖»
       "‖"
       (Term.typeAscription "(" (num "1") ":" [`A] ")")
       "‖"))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription "(" (num "0") ":" [`𝕜] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `𝕜
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Metric.closedBall
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Analysis.NormedSpace.Spectrum.termσ', expected 'spectrum.Analysis.NormedSpace.Spectrum.termσ._@.Analysis.NormedSpace.Spectrum._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  subset_closed_ball_norm_mul
  ( a : A ) : σ a ⊆ Metric.closedBall ( 0 : 𝕜 ) ‖ a ‖ * ‖ ( 1 : A ) ‖
  := fun k hk => by simp [ norm_le_norm_mul_of_mem hk ]
#align spectrum.subset_closed_ball_norm_mul spectrum.subset_closed_ball_norm_mul

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `subset_closed_ball_norm [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `NormOneClass [`A]) "]")
        (Term.explicitBinder "(" [`a] [":" `A] [] ")")]
       (Term.typeSpec
        ":"
        («term_⊆_»
         (Term.app (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ") [`a])
         "⊆"
         (Term.app
          `Metric.closedBall
          [(Term.typeAscription "(" (num "0") ":" [`𝕜] ")")
           (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖")]))))
      (Command.declValSimple
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [`k `hk]
         []
         "=>"
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.simp
              "simp"
              []
              []
              []
              ["[" [(Tactic.simpLemma [] [] (Term.app `norm_le_norm_of_mem [`hk]))] "]"]
              [])])))))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`k `hk]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.simp
             "simp"
             []
             []
             []
             ["[" [(Tactic.simpLemma [] [] (Term.app `norm_le_norm_of_mem [`hk]))] "]"]
             [])])))))
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
           ["[" [(Tactic.simpLemma [] [] (Term.app `norm_le_norm_of_mem [`hk]))] "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["[" [(Tactic.simpLemma [] [] (Term.app `norm_le_norm_of_mem [`hk]))] "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `norm_le_norm_of_mem [`hk])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hk
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm_le_norm_of_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_⊆_»
       (Term.app (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ") [`a])
       "⊆"
       (Term.app
        `Metric.closedBall
        [(Term.typeAscription "(" (num "0") ":" [`𝕜] ")")
         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Metric.closedBall
       [(Term.typeAscription "(" (num "0") ":" [`𝕜] ")")
        (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term‖_‖»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term‖_‖»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.typeAscription "(" (num "0") ":" [`𝕜] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `𝕜
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Metric.closedBall
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Analysis.NormedSpace.Spectrum.termσ', expected 'spectrum.Analysis.NormedSpace.Spectrum.termσ._@.Analysis.NormedSpace.Spectrum._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  subset_closed_ball_norm
  [ NormOneClass A ] ( a : A ) : σ a ⊆ Metric.closedBall ( 0 : 𝕜 ) ‖ a ‖
  := fun k hk => by simp [ norm_le_norm_of_mem hk ]
#align spectrum.subset_closed_ball_norm spectrum.subset_closed_ball_norm

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `is_bounded [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" `A] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `Metric.Bounded
         [(Term.app (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ") [`a])])))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj (Term.app `Metric.bounded_iff_subset_ball [(num "0")]) "." `mpr)
        [(Term.anonymousCtor
          "⟨"
          [(«term_*_»
            (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖")
            "*"
            (Analysis.Normed.Group.Basic.«term‖_‖»
             "‖"
             (Term.typeAscription "(" (num "1") ":" [`A] ")")
             "‖"))
           ","
           (Term.app `subset_closed_ball_norm_mul [`a])]
          "⟩")])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `Metric.bounded_iff_subset_ball [(num "0")]) "." `mpr)
       [(Term.anonymousCtor
         "⟨"
         [(«term_*_»
           (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖")
           "*"
           (Analysis.Normed.Group.Basic.«term‖_‖»
            "‖"
            (Term.typeAscription "(" (num "1") ":" [`A] ")")
            "‖"))
          ","
          (Term.app `subset_closed_ball_norm_mul [`a])]
         "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(«term_*_»
         (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖")
         "*"
         (Analysis.Normed.Group.Basic.«term‖_‖»
          "‖"
          (Term.typeAscription "(" (num "1") ":" [`A] ")")
          "‖"))
        ","
        (Term.app `subset_closed_ball_norm_mul [`a])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `subset_closed_ball_norm_mul [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `subset_closed_ball_norm_mul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖")
       "*"
       (Analysis.Normed.Group.Basic.«term‖_‖»
        "‖"
        (Term.typeAscription "(" (num "1") ":" [`A] ")")
        "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖»
       "‖"
       (Term.typeAscription "(" (num "1") ":" [`A] ")")
       "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" (num "1") ":" [`A] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Analysis.Normed.Group.Basic.«term‖_‖» "‖" `a "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `Metric.bounded_iff_subset_ball [(num "0")]) "." `mpr)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Metric.bounded_iff_subset_ball [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Metric.bounded_iff_subset_ball
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Metric.bounded_iff_subset_ball [(num "0")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Metric.Bounded
       [(Term.app (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ") [`a])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Analysis.NormedSpace.Spectrum.termσ', expected 'spectrum.Analysis.NormedSpace.Spectrum.termσ._@.Analysis.NormedSpace.Spectrum._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  is_bounded
  ( a : A ) : Metric.Bounded σ a
  :=
    Metric.bounded_iff_subset_ball 0 . mpr ⟨ ‖ a ‖ * ‖ ( 1 : A ) ‖ , subset_closed_ball_norm_mul a ⟩
#align spectrum.is_bounded spectrum.is_bounded

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `is_compact [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `ProperSpace [`𝕜]) "]")
        (Term.explicitBinder "(" [`a] [":" `A] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app `IsCompact [(Term.app (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ") [`a])])))
      (Command.declValSimple
       ":="
       (Term.app
        `Metric.is_compact_of_is_closed_bounded
        [(Term.app `spectrum.is_closed [`a]) (Term.app `is_bounded [`a])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Metric.is_compact_of_is_closed_bounded
       [(Term.app `spectrum.is_closed [`a]) (Term.app `is_bounded [`a])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `is_bounded [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_bounded
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `is_bounded [`a]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `spectrum.is_closed [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `spectrum.is_closed
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `spectrum.is_closed [`a]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Metric.is_compact_of_is_closed_bounded
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `IsCompact [(Term.app (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ") [`a])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Analysis.NormedSpace.Spectrum.termσ', expected 'spectrum.Analysis.NormedSpace.Spectrum.termσ._@.Analysis.NormedSpace.Spectrum._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected
  theorem
    is_compact
    [ ProperSpace 𝕜 ] ( a : A ) : IsCompact σ a
    := Metric.is_compact_of_is_closed_bounded spectrum.is_closed a is_bounded a
#align spectrum.is_compact spectrum.is_compact

theorem spectral_radius_le_nnnorm [NormOneClass A] (a : A) : spectralRadius 𝕜 a ≤ ‖a‖₊ :=
  by
  refine' supᵢ₂_le fun k hk => _
  exact_mod_cast norm_le_norm_of_mem hk
#align spectrum.spectral_radius_le_nnnorm spectrum.spectral_radius_le_nnnorm

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `exists_nnnorm_eq_spectral_radius_of_nonempty [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `ProperSpace [`𝕜]) "]")
        (Term.implicitBinder "{" [`a] [":" `A] "}")
        (Term.explicitBinder
         "("
         [`ha]
         [":"
          (Term.proj
           (Term.app (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ") [`a])
           "."
           `Nonempty)]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Std.ExtendedBinder.«term∃__,_»
         "∃"
         (Lean.binderIdent `k)
         («binderTerm∈_» "∈" (Term.app (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ") [`a]))
         ","
         («term_=_»
          (Term.typeAscription
           "("
           (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" `k "‖₊")
           ":"
           [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
           ")")
          "="
          (Term.app `spectralRadius [`𝕜 `a])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.obtain
            "obtain"
            [(Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hk)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h)])
                  [])]
                "⟩")])]
            []
            [":="
             [(Term.app
               (Term.proj (Term.app `spectrum.is_compact [`a]) "." `exists_forall_ge)
               [`ha `continuous_nnnorm.continuous_on])]])
           []
           (Tactic.exact
            "exact"
            (Term.anonymousCtor
             "⟨"
             [`k
              ","
              `hk
              ","
              (Term.app
               `le_antisymm
               [(Term.app `le_supᵢ₂ [`k `hk])
                («term_<|_»
                 `supᵢ₂_le
                 "<|"
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `h)]))))])]
             "⟩"))])))
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
         [(Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hk)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h)])
                 [])]
               "⟩")])]
           []
           [":="
            [(Term.app
              (Term.proj (Term.app `spectrum.is_compact [`a]) "." `exists_forall_ge)
              [`ha `continuous_nnnorm.continuous_on])]])
          []
          (Tactic.exact
           "exact"
           (Term.anonymousCtor
            "⟨"
            [`k
             ","
             `hk
             ","
             (Term.app
              `le_antisymm
              [(Term.app `le_supᵢ₂ [`k `hk])
               («term_<|_»
                `supᵢ₂_le
                "<|"
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `h)]))))])]
            "⟩"))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.anonymousCtor
        "⟨"
        [`k
         ","
         `hk
         ","
         (Term.app
          `le_antisymm
          [(Term.app `le_supᵢ₂ [`k `hk])
           («term_<|_»
            `supᵢ₂_le
            "<|"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `h)]))))])]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`k
        ","
        `hk
        ","
        (Term.app
         `le_antisymm
         [(Term.app `le_supᵢ₂ [`k `hk])
          («term_<|_»
           `supᵢ₂_le
           "<|"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `h)]))))])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `le_antisymm
       [(Term.app `le_supᵢ₂ [`k `hk])
        («term_<|_»
         `supᵢ₂_le
         "<|"
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `h)]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       `supᵢ₂_le
       "<|"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `h)]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented [(Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `h)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `h)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `supᵢ₂_le
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_»
      `supᵢ₂_le
      "<|"
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented [(Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `h)]))))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `le_supᵢ₂ [`k `hk])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hk
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_supᵢ₂
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `le_supᵢ₂ [`k `hk]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_antisymm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `k)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hk)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h)])
             [])]
           "⟩")])]
       []
       [":="
        [(Term.app
          (Term.proj (Term.app `spectrum.is_compact [`a]) "." `exists_forall_ge)
          [`ha `continuous_nnnorm.continuous_on])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `spectrum.is_compact [`a]) "." `exists_forall_ge)
       [`ha `continuous_nnnorm.continuous_on])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `continuous_nnnorm.continuous_on
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `spectrum.is_compact [`a]) "." `exists_forall_ge)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `spectrum.is_compact [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `spectrum.is_compact
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `spectrum.is_compact [`a])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Std.ExtendedBinder.«term∃__,_»
       "∃"
       (Lean.binderIdent `k)
       («binderTerm∈_» "∈" (Term.app (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ") [`a]))
       ","
       («term_=_»
        (Term.typeAscription
         "("
         (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" `k "‖₊")
         ":"
         [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
         ")")
        "="
        (Term.app `spectralRadius [`𝕜 `a])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.typeAscription
        "("
        (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" `k "‖₊")
        ":"
        [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
        ")")
       "="
       (Term.app `spectralRadius [`𝕜 `a]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `spectralRadius [`𝕜 `a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝕜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `spectralRadius
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription
       "("
       (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" `k "‖₊")
       ":"
       [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" `k "‖₊")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Analysis.NormedSpace.Spectrum.termσ', expected 'spectrum.Analysis.NormedSpace.Spectrum.termσ._@.Analysis.NormedSpace.Spectrum._hyg.8'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  exists_nnnorm_eq_spectral_radius_of_nonempty
  [ ProperSpace 𝕜 ] { a : A } ( ha : σ a . Nonempty )
    : ∃ k ∈ σ a , ( ‖ k ‖₊ : ℝ≥0∞ ) = spectralRadius 𝕜 a
  :=
    by
      obtain
          ⟨ k , hk , h ⟩
          := spectrum.is_compact a . exists_forall_ge ha continuous_nnnorm.continuous_on
        exact ⟨ k , hk , le_antisymm le_supᵢ₂ k hk supᵢ₂_le <| by exact_mod_cast h ⟩
#align
  spectrum.exists_nnnorm_eq_spectral_radius_of_nonempty spectrum.exists_nnnorm_eq_spectral_radius_of_nonempty

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `spectral_radius_lt_of_forall_lt_of_nonempty [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `ProperSpace [`𝕜]) "]")
        (Term.implicitBinder "{" [`a] [":" `A] "}")
        (Term.explicitBinder
         "("
         [`ha]
         [":"
          (Term.proj
           (Term.app (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ") [`a])
           "."
           `Nonempty)]
         []
         ")")
        (Term.implicitBinder "{" [`r] [":" (Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0")] "}")
        (Term.explicitBinder
         "("
         [`hr]
         [":"
          (Std.ExtendedBinder.«term∀__,_»
           "∀"
           (Lean.binderIdent `k)
           («binderTerm∈_» "∈" (Term.app (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ") [`a]))
           ","
           («term_<_» (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" `k "‖₊") "<" `r))]
         []
         ")")]
       (Term.typeSpec ":" («term_<_» (Term.app `spectralRadius [`𝕜 `a]) "<" `r)))
      (Command.declValSimple
       ":="
       («term_<|_»
        (Term.proj (Term.proj `supₛ_image "." `symm) "." `trans_lt)
        "<|"
        (Term.app
         (Term.proj
          (Term.app
           (Term.proj (Term.app `spectrum.is_compact [`a]) "." `Sup_lt_iff_of_continuous)
           [`ha
            (Term.proj
             (Term.app (Term.proj `Ennreal.continuous_coe "." `comp) [`continuous_nnnorm])
             "."
             `ContinuousOn)
            (Term.typeAscription "(" `r ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")])
          "."
          `mpr)
         [(Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `hr)])))]))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj (Term.proj `supₛ_image "." `symm) "." `trans_lt)
       "<|"
       (Term.app
        (Term.proj
         (Term.app
          (Term.proj (Term.app `spectrum.is_compact [`a]) "." `Sup_lt_iff_of_continuous)
          [`ha
           (Term.proj
            (Term.app (Term.proj `Ennreal.continuous_coe "." `comp) [`continuous_nnnorm])
            "."
            `ContinuousOn)
           (Term.typeAscription "(" `r ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")])
         "."
         `mpr)
        [(Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `hr)])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app
         (Term.proj (Term.app `spectrum.is_compact [`a]) "." `Sup_lt_iff_of_continuous)
         [`ha
          (Term.proj
           (Term.app (Term.proj `Ennreal.continuous_coe "." `comp) [`continuous_nnnorm])
           "."
           `ContinuousOn)
          (Term.typeAscription "(" `r ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")])
        "."
        `mpr)
       [(Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `hr)])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented [(Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `hr)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `hr)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hr
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented [(Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `hr)])))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        (Term.proj (Term.app `spectrum.is_compact [`a]) "." `Sup_lt_iff_of_continuous)
        [`ha
         (Term.proj
          (Term.app (Term.proj `Ennreal.continuous_coe "." `comp) [`continuous_nnnorm])
          "."
          `ContinuousOn)
         (Term.typeAscription "(" `r ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")])
       "."
       `mpr)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj (Term.app `spectrum.is_compact [`a]) "." `Sup_lt_iff_of_continuous)
       [`ha
        (Term.proj
         (Term.app (Term.proj `Ennreal.continuous_coe "." `comp) [`continuous_nnnorm])
         "."
         `ContinuousOn)
        (Term.typeAscription "(" `r ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" `r ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.proj
       (Term.app (Term.proj `Ennreal.continuous_coe "." `comp) [`continuous_nnnorm])
       "."
       `ContinuousOn)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `Ennreal.continuous_coe "." `comp) [`continuous_nnnorm])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `continuous_nnnorm
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `Ennreal.continuous_coe "." `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Ennreal.continuous_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `Ennreal.continuous_coe "." `comp) [`continuous_nnnorm])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `spectrum.is_compact [`a]) "." `Sup_lt_iff_of_continuous)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `spectrum.is_compact [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `spectrum.is_compact
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `spectrum.is_compact [`a])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj
       (Term.paren "(" (Term.app `spectrum.is_compact [`a]) ")")
       "."
       `Sup_lt_iff_of_continuous)
      [`ha
       (Term.proj
        (Term.paren
         "("
         (Term.app (Term.proj `Ennreal.continuous_coe "." `comp) [`continuous_nnnorm])
         ")")
        "."
        `ContinuousOn)
       (Term.typeAscription "(" `r ":" [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")] ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj (Term.proj `supₛ_image "." `symm) "." `trans_lt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `supₛ_image "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `supₛ_image
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_<_» (Term.app `spectralRadius [`𝕜 `a]) "<" `r)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `spectralRadius [`𝕜 `a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝕜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `spectralRadius
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.ExtendedBinder.«term∀__,_»
       "∀"
       (Lean.binderIdent `k)
       («binderTerm∈_» "∈" (Term.app (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ") [`a]))
       ","
       («term_<_» (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" `k "‖₊") "<" `r))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" `k "‖₊") "<" `r)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" `k "‖₊")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Analysis.NormedSpace.Spectrum.termσ', expected 'spectrum.Analysis.NormedSpace.Spectrum.termσ._@.Analysis.NormedSpace.Spectrum._hyg.8'
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
  spectral_radius_lt_of_forall_lt_of_nonempty
  [ ProperSpace 𝕜 ] { a : A } ( ha : σ a . Nonempty ) { r : ℝ≥0 } ( hr : ∀ k ∈ σ a , ‖ k ‖₊ < r )
    : spectralRadius 𝕜 a < r
  :=
    supₛ_image . symm . trans_lt
      <|
      spectrum.is_compact a . Sup_lt_iff_of_continuous
            ha Ennreal.continuous_coe . comp continuous_nnnorm . ContinuousOn ( r : ℝ≥0∞ )
          .
          mpr
        by exact_mod_cast hr
#align
  spectrum.spectral_radius_lt_of_forall_lt_of_nonempty spectrum.spectral_radius_lt_of_forall_lt_of_nonempty

open Ennreal Polynomial

variable (𝕜)

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `spectral_radius_le_pow_nnnorm_pow_one_div [])
      (Command.declSig
       [(Term.explicitBinder "(" [`a] [":" `A] [] ")")
        (Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")]
       (Term.typeSpec
        ":"
        («term_≤_»
         (Term.app `spectralRadius [`𝕜 `a])
         "≤"
         («term_*_»
          («term_^_»
           (Analysis.Normed.Group.Basic.«term‖_‖₊»
            "‖"
            («term_^_» `a "^" («term_+_» `n "+" (num "1")))
            "‖₊")
           "^"
           (Term.typeAscription
            "("
            («term_/_» (num "1") "/" («term_+_» `n "+" (num "1")))
            ":"
            [(Data.Real.Basic.termℝ "ℝ")]
            ")"))
          "*"
          («term_^_»
           (Analysis.Normed.Group.Basic.«term‖_‖₊»
            "‖"
            (Term.typeAscription "(" (num "1") ":" [`A] ")")
            "‖₊")
           "^"
           (Term.typeAscription
            "("
            («term_/_» (num "1") "/" («term_+_» `n "+" (num "1")))
            ":"
            [(Data.Real.Basic.termℝ "ℝ")]
            ")"))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.app
             `supᵢ₂_le
             [(Term.fun "fun" (Term.basicFun [`k `hk] [] "=>" (Term.hole "_")))]))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`pow_mem []]
              [(Term.typeSpec
                ":"
                («term_∈_»
                 («term_^_» `k "^" («term_+_» `n "+" (num "1")))
                 "∈"
                 (Term.app
                  (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ")
                  [(«term_^_» `a "^" («term_+_» `n "+" (num "1")))])))]
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
                      [(Tactic.simpLemma [] [] `one_mul)
                       ","
                       (Tactic.simpLemma [] [] `Algebra.algebra_map_eq_smul_one)
                       ","
                       (Tactic.simpLemma [] [] `one_smul)
                       ","
                       (Tactic.simpLemma [] [] `aeval_monomial)
                       ","
                       (Tactic.simpLemma [] [] `one_mul)
                       ","
                       (Tactic.simpLemma [] [] `eval_monomial)]
                      "]")]
                    ["using"
                     (Term.app
                      `subset_polynomial_aeval
                      [`a
                       (Term.app
                        `monomial
                        [(«term_+_» `n "+" (num "1"))
                         (Term.typeAscription "(" (num "1") ":" [`𝕜] ")")])
                       (Term.anonymousCtor "⟨" [`k "," `hk "," `rfl] "⟩")])]))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`nnnorm_pow_le []]
              [(Term.typeSpec
                ":"
                («term_≤_»
                 (Term.typeAscription
                  "("
                  (coeNotation
                   "↑"
                   («term_^_»
                    (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" `k "‖₊")
                    "^"
                    («term_+_» `n "+" (num "1"))))
                  ":"
                  [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
                  ")")
                 "≤"
                 («term_*_»
                  (Analysis.Normed.Group.Basic.«term‖_‖₊»
                   "‖"
                   («term_^_» `a "^" («term_+_» `n "+" (num "1")))
                   "‖₊")
                  "*"
                  (Analysis.Normed.Group.Basic.«term‖_‖₊»
                   "‖"
                   (Term.typeAscription "(" (num "1") ":" [`A] ")")
                   "‖₊"))))]
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
                      [(Tactic.simpLemma
                        []
                        []
                        (Term.app `Real.to_nnreal_mul [(Term.app `norm_nonneg [(Term.hole "_")])]))
                       ","
                       (Tactic.simpLemma [] [] `norm_to_nnreal)
                       ","
                       (Tactic.simpLemma
                        []
                        []
                        (Term.app `nnnorm_pow [`k («term_+_» `n "+" (num "1"))]))
                       ","
                       (Tactic.simpLemma [] [] `Ennreal.coe_mul)]
                      "]")]
                    ["using"
                     (Term.app
                      `coe_mono
                      [(Term.app
                        `Real.to_nnreal_mono
                        [(Term.app `norm_le_norm_mul_of_mem [`pow_mem])])])]))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hn []]
              [(Term.typeSpec
                ":"
                («term_<_»
                 (num "0")
                 "<"
                 (Term.typeAscription
                  "("
                  (Term.typeAscription "(" («term_+_» `n "+" (num "1")) ":" [(termℕ "ℕ")] ")")
                  ":"
                  [(Data.Real.Basic.termℝ "ℝ")]
                  ")")))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `Nat.succ_pos')]))))))
           []
           (convert
            "convert"
            []
            (Term.app
             `monotone_rpow_of_nonneg
             [(Term.proj (Term.app `one_div_pos.mpr [`hn]) "." `le) `nnnorm_pow_le])
            [])
           []
           (Tactic.tacticErw__
            "erw"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `coe_pow)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `rpow_nat_cast)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `rpow_mul)
              ","
              (Tactic.rwRule [] (Term.app `mul_one_div_cancel [`hn.ne']))
              ","
              (Tactic.rwRule [] `rpow_one)]
             "]")
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `Nat.cast_succ) "," (Tactic.rwRule [] `Ennreal.coe_mul_rpow)]
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
         [(Tactic.refine'
           "refine'"
           (Term.app `supᵢ₂_le [(Term.fun "fun" (Term.basicFun [`k `hk] [] "=>" (Term.hole "_")))]))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`pow_mem []]
             [(Term.typeSpec
               ":"
               («term_∈_»
                («term_^_» `k "^" («term_+_» `n "+" (num "1")))
                "∈"
                (Term.app
                 (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ")
                 [(«term_^_» `a "^" («term_+_» `n "+" (num "1")))])))]
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
                     [(Tactic.simpLemma [] [] `one_mul)
                      ","
                      (Tactic.simpLemma [] [] `Algebra.algebra_map_eq_smul_one)
                      ","
                      (Tactic.simpLemma [] [] `one_smul)
                      ","
                      (Tactic.simpLemma [] [] `aeval_monomial)
                      ","
                      (Tactic.simpLemma [] [] `one_mul)
                      ","
                      (Tactic.simpLemma [] [] `eval_monomial)]
                     "]")]
                   ["using"
                    (Term.app
                     `subset_polynomial_aeval
                     [`a
                      (Term.app
                       `monomial
                       [(«term_+_» `n "+" (num "1"))
                        (Term.typeAscription "(" (num "1") ":" [`𝕜] ")")])
                      (Term.anonymousCtor "⟨" [`k "," `hk "," `rfl] "⟩")])]))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`nnnorm_pow_le []]
             [(Term.typeSpec
               ":"
               («term_≤_»
                (Term.typeAscription
                 "("
                 (coeNotation
                  "↑"
                  («term_^_»
                   (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" `k "‖₊")
                   "^"
                   («term_+_» `n "+" (num "1"))))
                 ":"
                 [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
                 ")")
                "≤"
                («term_*_»
                 (Analysis.Normed.Group.Basic.«term‖_‖₊»
                  "‖"
                  («term_^_» `a "^" («term_+_» `n "+" (num "1")))
                  "‖₊")
                 "*"
                 (Analysis.Normed.Group.Basic.«term‖_‖₊»
                  "‖"
                  (Term.typeAscription "(" (num "1") ":" [`A] ")")
                  "‖₊"))))]
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
                     [(Tactic.simpLemma
                       []
                       []
                       (Term.app `Real.to_nnreal_mul [(Term.app `norm_nonneg [(Term.hole "_")])]))
                      ","
                      (Tactic.simpLemma [] [] `norm_to_nnreal)
                      ","
                      (Tactic.simpLemma
                       []
                       []
                       (Term.app `nnnorm_pow [`k («term_+_» `n "+" (num "1"))]))
                      ","
                      (Tactic.simpLemma [] [] `Ennreal.coe_mul)]
                     "]")]
                   ["using"
                    (Term.app
                     `coe_mono
                     [(Term.app
                       `Real.to_nnreal_mono
                       [(Term.app `norm_le_norm_mul_of_mem [`pow_mem])])])]))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hn []]
             [(Term.typeSpec
               ":"
               («term_<_»
                (num "0")
                "<"
                (Term.typeAscription
                 "("
                 (Term.typeAscription "(" («term_+_» `n "+" (num "1")) ":" [(termℕ "ℕ")] ")")
                 ":"
                 [(Data.Real.Basic.termℝ "ℝ")]
                 ")")))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `Nat.succ_pos')]))))))
          []
          (convert
           "convert"
           []
           (Term.app
            `monotone_rpow_of_nonneg
            [(Term.proj (Term.app `one_div_pos.mpr [`hn]) "." `le) `nnnorm_pow_le])
           [])
          []
          (Tactic.tacticErw__
           "erw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `coe_pow)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `rpow_nat_cast)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `rpow_mul)
             ","
             (Tactic.rwRule [] (Term.app `mul_one_div_cancel [`hn.ne']))
             ","
             (Tactic.rwRule [] `rpow_one)]
            "]")
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `Nat.cast_succ) "," (Tactic.rwRule [] `Ennreal.coe_mul_rpow)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `Nat.cast_succ) "," (Tactic.rwRule [] `Ennreal.coe_mul_rpow)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ennreal.coe_mul_rpow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.cast_succ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticErw__
       "erw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `coe_pow)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `rpow_nat_cast)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `rpow_mul)
         ","
         (Tactic.rwRule [] (Term.app `mul_one_div_cancel [`hn.ne']))
         ","
         (Tactic.rwRule [] `rpow_one)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rpow_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_one_div_cancel [`hn.ne'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hn.ne'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_one_div_cancel
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rpow_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rpow_nat_cast
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_pow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert
       "convert"
       []
       (Term.app
        `monotone_rpow_of_nonneg
        [(Term.proj (Term.app `one_div_pos.mpr [`hn]) "." `le) `nnnorm_pow_le])
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `monotone_rpow_of_nonneg
       [(Term.proj (Term.app `one_div_pos.mpr [`hn]) "." `le) `nnnorm_pow_le])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nnnorm_pow_le
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app `one_div_pos.mpr [`hn]) "." `le)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `one_div_pos.mpr [`hn])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hn
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `one_div_pos.mpr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `one_div_pos.mpr [`hn]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `monotone_rpow_of_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hn []]
         [(Term.typeSpec
           ":"
           («term_<_»
            (num "0")
            "<"
            (Term.typeAscription
             "("
             (Term.typeAscription "(" («term_+_» `n "+" (num "1")) ":" [(termℕ "ℕ")] ")")
             ":"
             [(Data.Real.Basic.termℝ "ℝ")]
             ")")))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `Nat.succ_pos')]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `Nat.succ_pos')])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.NormCast.tacticExact_mod_cast_ "exact_mod_cast" `Nat.succ_pos')
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.succ_pos'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_»
       (num "0")
       "<"
       (Term.typeAscription
        "("
        (Term.typeAscription "(" («term_+_» `n "+" (num "1")) ":" [(termℕ "ℕ")] ")")
        ":"
        [(Data.Real.Basic.termℝ "ℝ")]
        ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.typeAscription "(" («term_+_» `n "+" (num "1")) ":" [(termℕ "ℕ")] ")")
       ":"
       [(Data.Real.Basic.termℝ "ℝ")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" («term_+_» `n "+" (num "1")) ":" [(termℕ "ℕ")] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termℕ "ℕ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`nnnorm_pow_le []]
         [(Term.typeSpec
           ":"
           («term_≤_»
            (Term.typeAscription
             "("
             (coeNotation
              "↑"
              («term_^_»
               (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" `k "‖₊")
               "^"
               («term_+_» `n "+" (num "1"))))
             ":"
             [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
             ")")
            "≤"
            («term_*_»
             (Analysis.Normed.Group.Basic.«term‖_‖₊»
              "‖"
              («term_^_» `a "^" («term_+_» `n "+" (num "1")))
              "‖₊")
             "*"
             (Analysis.Normed.Group.Basic.«term‖_‖₊»
              "‖"
              (Term.typeAscription "(" (num "1") ":" [`A] ")")
              "‖₊"))))]
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
                 [(Tactic.simpLemma
                   []
                   []
                   (Term.app `Real.to_nnreal_mul [(Term.app `norm_nonneg [(Term.hole "_")])]))
                  ","
                  (Tactic.simpLemma [] [] `norm_to_nnreal)
                  ","
                  (Tactic.simpLemma [] [] (Term.app `nnnorm_pow [`k («term_+_» `n "+" (num "1"))]))
                  ","
                  (Tactic.simpLemma [] [] `Ennreal.coe_mul)]
                 "]")]
               ["using"
                (Term.app
                 `coe_mono
                 [(Term.app
                   `Real.to_nnreal_mono
                   [(Term.app `norm_le_norm_mul_of_mem [`pow_mem])])])]))]))))))
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
              [(Tactic.simpLemma
                []
                []
                (Term.app `Real.to_nnreal_mul [(Term.app `norm_nonneg [(Term.hole "_")])]))
               ","
               (Tactic.simpLemma [] [] `norm_to_nnreal)
               ","
               (Tactic.simpLemma [] [] (Term.app `nnnorm_pow [`k («term_+_» `n "+" (num "1"))]))
               ","
               (Tactic.simpLemma [] [] `Ennreal.coe_mul)]
              "]")]
            ["using"
             (Term.app
              `coe_mono
              [(Term.app
                `Real.to_nnreal_mono
                [(Term.app `norm_le_norm_mul_of_mem [`pow_mem])])])]))])))
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
          [(Tactic.simpLemma
            []
            []
            (Term.app `Real.to_nnreal_mul [(Term.app `norm_nonneg [(Term.hole "_")])]))
           ","
           (Tactic.simpLemma [] [] `norm_to_nnreal)
           ","
           (Tactic.simpLemma [] [] (Term.app `nnnorm_pow [`k («term_+_» `n "+" (num "1"))]))
           ","
           (Tactic.simpLemma [] [] `Ennreal.coe_mul)]
          "]")]
        ["using"
         (Term.app
          `coe_mono
          [(Term.app `Real.to_nnreal_mono [(Term.app `norm_le_norm_mul_of_mem [`pow_mem])])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `coe_mono
       [(Term.app `Real.to_nnreal_mono [(Term.app `norm_le_norm_mul_of_mem [`pow_mem])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Real.to_nnreal_mono [(Term.app `norm_le_norm_mul_of_mem [`pow_mem])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `norm_le_norm_mul_of_mem [`pow_mem])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pow_mem
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm_le_norm_mul_of_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `norm_le_norm_mul_of_mem [`pow_mem])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Real.to_nnreal_mono
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `Real.to_nnreal_mono
      [(Term.paren "(" (Term.app `norm_le_norm_mul_of_mem [`pow_mem]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `coe_mono
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ennreal.coe_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `nnnorm_pow [`k («term_+_» `n "+" (num "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `nnnorm_pow
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_to_nnreal
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Real.to_nnreal_mul [(Term.app `norm_nonneg [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `norm_nonneg [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `norm_nonneg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `norm_nonneg [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Real.to_nnreal_mul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       (Term.typeAscription
        "("
        (coeNotation
         "↑"
         («term_^_»
          (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" `k "‖₊")
          "^"
          («term_+_» `n "+" (num "1"))))
        ":"
        [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
        ")")
       "≤"
       («term_*_»
        (Analysis.Normed.Group.Basic.«term‖_‖₊»
         "‖"
         («term_^_» `a "^" («term_+_» `n "+" (num "1")))
         "‖₊")
        "*"
        (Analysis.Normed.Group.Basic.«term‖_‖₊»
         "‖"
         (Term.typeAscription "(" (num "1") ":" [`A] ")")
         "‖₊")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Analysis.Normed.Group.Basic.«term‖_‖₊»
        "‖"
        («term_^_» `a "^" («term_+_» `n "+" (num "1")))
        "‖₊")
       "*"
       (Analysis.Normed.Group.Basic.«term‖_‖₊»
        "‖"
        (Term.typeAscription "(" (num "1") ":" [`A] ")")
        "‖₊"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖₊»
       "‖"
       (Term.typeAscription "(" (num "1") ":" [`A] ")")
       "‖₊")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" (num "1") ":" [`A] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Analysis.Normed.Group.Basic.«term‖_‖₊»
       "‖"
       («term_^_» `a "^" («term_+_» `n "+" (num "1")))
       "‖₊")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `a "^" («term_+_» `n "+" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription
       "("
       (coeNotation
        "↑"
        («term_^_»
         (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" `k "‖₊")
         "^"
         («term_+_» `n "+" (num "1"))))
       ":"
       [(Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ennreal.Data.Real.Ennreal.ennreal "ℝ≥0∞")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (coeNotation
       "↑"
       («term_^_»
        (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" `k "‖₊")
        "^"
        («term_+_» `n "+" (num "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_»
       (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" `k "‖₊")
       "^"
       («term_+_» `n "+" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" `k "‖₊")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_^_»
      (Analysis.Normed.Group.Basic.«term‖_‖₊» "‖" `k "‖₊")
      "^"
      (Term.paren "(" («term_+_» `n "+" (num "1")) ")"))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`pow_mem []]
         [(Term.typeSpec
           ":"
           («term_∈_»
            («term_^_» `k "^" («term_+_» `n "+" (num "1")))
            "∈"
            (Term.app
             (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ")
             [(«term_^_» `a "^" («term_+_» `n "+" (num "1")))])))]
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
                 [(Tactic.simpLemma [] [] `one_mul)
                  ","
                  (Tactic.simpLemma [] [] `Algebra.algebra_map_eq_smul_one)
                  ","
                  (Tactic.simpLemma [] [] `one_smul)
                  ","
                  (Tactic.simpLemma [] [] `aeval_monomial)
                  ","
                  (Tactic.simpLemma [] [] `one_mul)
                  ","
                  (Tactic.simpLemma [] [] `eval_monomial)]
                 "]")]
               ["using"
                (Term.app
                 `subset_polynomial_aeval
                 [`a
                  (Term.app
                   `monomial
                   [(«term_+_» `n "+" (num "1")) (Term.typeAscription "(" (num "1") ":" [`𝕜] ")")])
                  (Term.anonymousCtor "⟨" [`k "," `hk "," `rfl] "⟩")])]))]))))))
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
              [(Tactic.simpLemma [] [] `one_mul)
               ","
               (Tactic.simpLemma [] [] `Algebra.algebra_map_eq_smul_one)
               ","
               (Tactic.simpLemma [] [] `one_smul)
               ","
               (Tactic.simpLemma [] [] `aeval_monomial)
               ","
               (Tactic.simpLemma [] [] `one_mul)
               ","
               (Tactic.simpLemma [] [] `eval_monomial)]
              "]")]
            ["using"
             (Term.app
              `subset_polynomial_aeval
              [`a
               (Term.app
                `monomial
                [(«term_+_» `n "+" (num "1")) (Term.typeAscription "(" (num "1") ":" [`𝕜] ")")])
               (Term.anonymousCtor "⟨" [`k "," `hk "," `rfl] "⟩")])]))])))
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
          [(Tactic.simpLemma [] [] `one_mul)
           ","
           (Tactic.simpLemma [] [] `Algebra.algebra_map_eq_smul_one)
           ","
           (Tactic.simpLemma [] [] `one_smul)
           ","
           (Tactic.simpLemma [] [] `aeval_monomial)
           ","
           (Tactic.simpLemma [] [] `one_mul)
           ","
           (Tactic.simpLemma [] [] `eval_monomial)]
          "]")]
        ["using"
         (Term.app
          `subset_polynomial_aeval
          [`a
           (Term.app
            `monomial
            [(«term_+_» `n "+" (num "1")) (Term.typeAscription "(" (num "1") ":" [`𝕜] ")")])
           (Term.anonymousCtor "⟨" [`k "," `hk "," `rfl] "⟩")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `subset_polynomial_aeval
       [`a
        (Term.app
         `monomial
         [(«term_+_» `n "+" (num "1")) (Term.typeAscription "(" (num "1") ":" [`𝕜] ")")])
        (Term.anonymousCtor "⟨" [`k "," `hk "," `rfl] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`k "," `hk "," `rfl] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.app
       `monomial
       [(«term_+_» `n "+" (num "1")) (Term.typeAscription "(" (num "1") ":" [`𝕜] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" (num "1") ":" [`𝕜] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `𝕜
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `monomial
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `monomial
      [(Term.paren "(" («term_+_» `n "+" (num "1")) ")")
       (Term.typeAscription "(" (num "1") ":" [`𝕜] ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `subset_polynomial_aeval
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eval_monomial
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `aeval_monomial
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_smul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Algebra.algebra_map_eq_smul_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_»
       («term_^_» `k "^" («term_+_» `n "+" (num "1")))
       "∈"
       (Term.app
        (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ")
        [(«term_^_» `a "^" («term_+_» `n "+" (num "1")))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ")
       [(«term_^_» `a "^" («term_+_» `n "+" (num "1")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `a "^" («term_+_» `n "+" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `n "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `n
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `n "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_^_» `a "^" (Term.paren "(" («term_+_» `n "+" (num "1")) ")"))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Analysis.NormedSpace.Spectrum.termσ "σ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Analysis.NormedSpace.Spectrum.termσ', expected 'spectrum.Analysis.NormedSpace.Spectrum.termσ._@.Analysis.NormedSpace.Spectrum._hyg.8'
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
theorem
  spectral_radius_le_pow_nnnorm_pow_one_div
  ( a : A ) ( n : ℕ )
    : spectralRadius 𝕜 a ≤ ‖ a ^ n + 1 ‖₊ ^ ( 1 / n + 1 : ℝ ) * ‖ ( 1 : A ) ‖₊ ^ ( 1 / n + 1 : ℝ )
  :=
    by
      refine' supᵢ₂_le fun k hk => _
        have
          pow_mem
            : k ^ n + 1 ∈ σ a ^ n + 1
            :=
            by
              simpa
                only
                  [
                    one_mul
                      ,
                      Algebra.algebra_map_eq_smul_one
                      ,
                      one_smul
                      ,
                      aeval_monomial
                      ,
                      one_mul
                      ,
                      eval_monomial
                    ]
                  using subset_polynomial_aeval a monomial n + 1 ( 1 : 𝕜 ) ⟨ k , hk , rfl ⟩
        have
          nnnorm_pow_le
            : ( ↑ ‖ k ‖₊ ^ n + 1 : ℝ≥0∞ ) ≤ ‖ a ^ n + 1 ‖₊ * ‖ ( 1 : A ) ‖₊
            :=
            by
              simpa
                only
                  [
                    Real.to_nnreal_mul norm_nonneg _
                      ,
                      norm_to_nnreal
                      ,
                      nnnorm_pow k n + 1
                      ,
                      Ennreal.coe_mul
                    ]
                  using coe_mono Real.to_nnreal_mono norm_le_norm_mul_of_mem pow_mem
        have hn : 0 < ( ( n + 1 : ℕ ) : ℝ ) := by exact_mod_cast Nat.succ_pos'
        convert monotone_rpow_of_nonneg one_div_pos.mpr hn . le nnnorm_pow_le
        erw [ coe_pow , ← rpow_nat_cast , ← rpow_mul , mul_one_div_cancel hn.ne' , rpow_one ]
        rw [ Nat.cast_succ , Ennreal.coe_mul_rpow ]
#align
  spectrum.spectral_radius_le_pow_nnnorm_pow_one_div spectrum.spectral_radius_le_pow_nnnorm_pow_one_div

theorem spectral_radius_le_liminf_pow_nnnorm_pow_one_div (a : A) :
    spectralRadius 𝕜 a ≤ atTop.liminf fun n : ℕ => (‖a ^ n‖₊ : ℝ≥0∞) ^ (1 / n : ℝ) :=
  by
  refine' Ennreal.le_of_forall_lt_one_mul_le fun ε hε => _
  by_cases ε = 0
  · simp only [h, zero_mul, zero_le']
  have hε' : ε⁻¹ ≠ ∞ := fun h' =>
    h (by simpa only [inv_inv, inv_top] using congr_arg (fun x : ℝ≥0∞ => x⁻¹) h')
  simp only [Ennreal.mul_le_iff_le_inv h (hε.trans_le le_top).Ne, mul_comm ε⁻¹,
    liminf_eq_supr_infi_of_nat', Ennreal.supr_mul, Ennreal.infi_mul hε']
  rw [← Ennreal.inv_lt_inv, inv_one] at hε
  obtain ⟨N, hN⟩ :=
    eventually_at_top.mp
      (Ennreal.eventually_pow_one_div_le (Ennreal.coe_ne_top : ↑‖(1 : A)‖₊ ≠ ∞) hε)
  refine' le_trans _ (le_supᵢ _ (N + 1))
  refine' le_infᵢ fun n => _
  simp only [← add_assoc]
  refine' (spectral_radius_le_pow_nnnorm_pow_one_div 𝕜 a (n + N)).trans _
  norm_cast
  exact mul_le_mul_left' (hN (n + N + 1) (by linarith)) _
#align
  spectrum.spectral_radius_le_liminf_pow_nnnorm_pow_one_div spectrum.spectral_radius_le_liminf_pow_nnnorm_pow_one_div

end SpectrumCompact

section resolvent

open Filter Asymptotics

variable [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

-- mathport name: exprρ
local notation "ρ" => resolventSet 𝕜

-- mathport name: «expr↑ₐ»
local notation "↑ₐ" => algebraMap 𝕜 A

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `has_deriv_at_resolvent [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a] [":" `A] "}")
        (Term.implicitBinder "{" [`k] [":" `𝕜] "}")
        (Term.explicitBinder
         "("
         [`hk]
         [":"
          («term_∈_» `k "∈" (Term.app (spectrum.Analysis.NormedSpace.Spectrum.termρ_1 "ρ") [`a]))]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `HasDerivAt
         [(Term.app `resolvent [`a])
          («term-_» "-" («term_^_» (Term.app `resolvent [`a `k]) "^" (num "2")))
          `k])))
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
              [`H₁ []]
              [(Term.typeSpec
                ":"
                (Term.app
                 `HasFderivAt
                 [`Ring.inverse
                  (Term.hole "_")
                  («term_-_»
                   (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_1» "↑ₐ") [`k])
                   "-"
                   `a)]))]
              ":="
              (Term.app `hasFderivAtRingInverse [`hk.unit]))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`H₂ []]
              [(Term.typeSpec
                ":"
                (Term.app
                 `HasDerivAt
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [`k]
                    []
                    "=>"
                    («term_-_»
                     (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_1» "↑ₐ") [`k])
                     "-"
                     `a)))
                  (num "1")
                  `k]))]
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
                     (Term.app
                      (Term.proj
                       (Term.proj (Term.app `Algebra.linearMap [`𝕜 `A]) "." `HasDerivAt)
                       "."
                       `sub_const)
                      [`a])]))]))))))
           []
           (Std.Tactic.Simpa.simpa
            "simpa"
            []
            []
            (Std.Tactic.Simpa.simpaArgsRest
             []
             []
             []
             [(Tactic.simpArgs
               "["
               [(Tactic.simpLemma [] [] `resolvent)
                ","
                (Tactic.simpLemma [] [] `sq)
                ","
                (Tactic.simpLemma [] [] `hk.unit_spec)
                ","
                (Tactic.simpLemma
                 []
                 [(patternIgnore (token.«← » "←"))]
                 (Term.app `Ring.inverse_unit [`hk.unit]))]
               "]")]
             ["using" (Term.app `H₁.comp_has_deriv_at [`k `H₂])]))])))
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
             [`H₁ []]
             [(Term.typeSpec
               ":"
               (Term.app
                `HasFderivAt
                [`Ring.inverse
                 (Term.hole "_")
                 («term_-_»
                  (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_1» "↑ₐ") [`k])
                  "-"
                  `a)]))]
             ":="
             (Term.app `hasFderivAtRingInverse [`hk.unit]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`H₂ []]
             [(Term.typeSpec
               ":"
               (Term.app
                `HasDerivAt
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [`k]
                   []
                   "=>"
                   («term_-_»
                    (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_1» "↑ₐ") [`k])
                    "-"
                    `a)))
                 (num "1")
                 `k]))]
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
                    (Term.app
                     (Term.proj
                      (Term.proj (Term.app `Algebra.linearMap [`𝕜 `A]) "." `HasDerivAt)
                      "."
                      `sub_const)
                     [`a])]))]))))))
          []
          (Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            []
            [(Tactic.simpArgs
              "["
              [(Tactic.simpLemma [] [] `resolvent)
               ","
               (Tactic.simpLemma [] [] `sq)
               ","
               (Tactic.simpLemma [] [] `hk.unit_spec)
               ","
               (Tactic.simpLemma
                []
                [(patternIgnore (token.«← » "←"))]
                (Term.app `Ring.inverse_unit [`hk.unit]))]
              "]")]
            ["using" (Term.app `H₁.comp_has_deriv_at [`k `H₂])]))])))
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
        [(Tactic.simpArgs
          "["
          [(Tactic.simpLemma [] [] `resolvent)
           ","
           (Tactic.simpLemma [] [] `sq)
           ","
           (Tactic.simpLemma [] [] `hk.unit_spec)
           ","
           (Tactic.simpLemma
            []
            [(patternIgnore (token.«← » "←"))]
            (Term.app `Ring.inverse_unit [`hk.unit]))]
          "]")]
        ["using" (Term.app `H₁.comp_has_deriv_at [`k `H₂])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `H₁.comp_has_deriv_at [`k `H₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `H₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `H₁.comp_has_deriv_at
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Ring.inverse_unit [`hk.unit])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hk.unit
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ring.inverse_unit
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hk.unit_spec
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `resolvent
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`H₂ []]
         [(Term.typeSpec
           ":"
           (Term.app
            `HasDerivAt
            [(Term.fun
              "fun"
              (Term.basicFun
               [`k]
               []
               "=>"
               («term_-_»
                (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_1» "↑ₐ") [`k])
                "-"
                `a)))
             (num "1")
             `k]))]
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
                (Term.app
                 (Term.proj
                  (Term.proj (Term.app `Algebra.linearMap [`𝕜 `A]) "." `HasDerivAt)
                  "."
                  `sub_const)
                 [`a])]))]))))))
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
             (Term.app
              (Term.proj
               (Term.proj (Term.app `Algebra.linearMap [`𝕜 `A]) "." `HasDerivAt)
               "."
               `sub_const)
              [`a])]))])))
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
         (Term.app
          (Term.proj
           (Term.proj (Term.app `Algebra.linearMap [`𝕜 `A]) "." `HasDerivAt)
           "."
           `sub_const)
          [`a])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.proj (Term.app `Algebra.linearMap [`𝕜 `A]) "." `HasDerivAt) "." `sub_const)
       [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.proj (Term.app `Algebra.linearMap [`𝕜 `A]) "." `HasDerivAt) "." `sub_const)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app `Algebra.linearMap [`𝕜 `A]) "." `HasDerivAt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Algebra.linearMap [`𝕜 `A])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `𝕜
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Algebra.linearMap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Algebra.linearMap [`𝕜 `A])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `HasDerivAt
       [(Term.fun
         "fun"
         (Term.basicFun
          [`k]
          []
          "=>"
          («term_-_»
           (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_1» "↑ₐ") [`k])
           "-"
           `a)))
        (num "1")
        `k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`k]
        []
        "=>"
        («term_-_»
         (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_1» "↑ₐ") [`k])
         "-"
         `a)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_1» "↑ₐ") [`k]) "-" `a)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_1» "↑ₐ") [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `k
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_1» "↑ₐ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_1»', expected 'spectrum.Analysis.NormedSpace.Spectrum.term↑ₐ_1._@.Analysis.NormedSpace.Spectrum._hyg.2096'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
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
theorem
  has_deriv_at_resolvent
  { a : A } { k : 𝕜 } ( hk : k ∈ ρ a ) : HasDerivAt resolvent a - resolvent a k ^ 2 k
  :=
    by
      have H₁ : HasFderivAt Ring.inverse _ ↑ₐ k - a := hasFderivAtRingInverse hk.unit
        have
          H₂
            : HasDerivAt fun k => ↑ₐ k - a 1 k
            :=
            by simpa using Algebra.linearMap 𝕜 A . HasDerivAt . sub_const a
        simpa
          [ resolvent , sq , hk.unit_spec , ← Ring.inverse_unit hk.unit ]
            using H₁.comp_has_deriv_at k H₂
#align spectrum.has_deriv_at_resolvent spectrum.has_deriv_at_resolvent

/- TODO: Once there is sufficient API for bornology, we should get a nice filter / asymptotics
version of this, for example: `tendsto (resolvent a) (cobounded 𝕜) (𝓝 0)` or more specifically
`(resolvent a) =O[cobounded 𝕜] (λ z, z⁻¹)`. -/
theorem norm_resolvent_le_forall (a : A) :
    ∀ ε > 0, ∃ R > 0, ∀ z : 𝕜, R ≤ ‖z‖ → ‖resolvent a z‖ ≤ ε :=
  by
  obtain ⟨c, c_pos, hc⟩ := (@NormedRing.inverse_one_sub_norm A _ _).exists_pos
  rw [is_O_with_iff, eventually_iff, Metric.mem_nhds_iff] at hc
  rcases hc with ⟨δ, δ_pos, hδ⟩
  simp only [CstarRing.norm_one, mul_one] at hδ
  intro ε hε
  have ha₁ : 0 < ‖a‖ + 1 := lt_of_le_of_lt (norm_nonneg a) (lt_add_one _)
  have min_pos : 0 < min (δ * (‖a‖ + 1)⁻¹) (ε * c⁻¹) :=
    lt_min (mul_pos δ_pos (inv_pos.mpr ha₁)) (mul_pos hε (inv_pos.mpr c_pos))
  refine' ⟨(min (δ * (‖a‖ + 1)⁻¹) (ε * c⁻¹))⁻¹, inv_pos.mpr min_pos, fun z hz => _⟩
  have hnz : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (inv_pos.mpr min_pos) hz)
  replace hz := inv_le_of_inv_le min_pos hz
  rcases(⟨Units.mk0 z hnz, Units.val_mk0 hnz⟩ : IsUnit z) with ⟨z, rfl⟩
  have lt_δ : ‖z⁻¹ • a‖ < δ :=
    by
    rw [Units.smul_def, norm_smul, Units.val_inv_eq_inv_val, norm_inv]
    calc
      ‖(z : 𝕜)‖⁻¹ * ‖a‖ ≤ δ * (‖a‖ + 1)⁻¹ * ‖a‖ :=
        mul_le_mul_of_nonneg_right (hz.trans (min_le_left _ _)) (norm_nonneg _)
      _ < δ :=
        by
        conv =>
          rw [mul_assoc]
          rhs
          rw [(mul_one δ).symm]
        exact
          mul_lt_mul_of_pos_left
            ((inv_mul_lt_iff ha₁).mpr ((mul_one (‖a‖ + 1)).symm ▸ lt_add_one _)) δ_pos
      
  rw [← inv_smul_smul z (resolvent a (z : 𝕜)), units_smul_resolvent_self, resolvent,
    Algebra.algebra_map_eq_smul_one, one_smul, Units.smul_def, norm_smul, Units.val_inv_eq_inv_val,
    norm_inv]
  calc
    _ ≤ ε * c⁻¹ * c :=
      mul_le_mul (hz.trans (min_le_right _ _)) (hδ (mem_ball_zero_iff.mpr lt_δ)) (norm_nonneg _)
        (mul_pos hε (inv_pos.mpr c_pos)).le
    _ = _ := inv_mul_cancel_right₀ c_pos.ne.symm ε
    
#align spectrum.norm_resolvent_le_forall spectrum.norm_resolvent_le_forall

end resolvent

section OneSubSmul

open ContinuousMultilinearMap Ennreal FormalMultilinearSeries

open Nnreal Ennreal

variable [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]

variable (𝕜)

/-- In a Banach algebra `A` over a nontrivially normed field `𝕜`, for any `a : A` the
power series with coefficients `a ^ n` represents the function `(1 - z • a)⁻¹` in a disk of
radius `‖a‖₊⁻¹`. -/
theorem hasFpowerSeriesOnBallInverseOneSubSmul [CompleteSpace A] (a : A) :
    HasFpowerSeriesOnBall (fun z : 𝕜 => Ring.inverse (1 - z • a))
      (fun n => ContinuousMultilinearMap.mkPiField 𝕜 (Fin n) (a ^ n)) 0 ‖a‖₊⁻¹ :=
  { r_le :=
      by
      refine'
        le_of_forall_nnreal_lt fun r hr => le_radius_of_bound_nnreal _ (max 1 ‖(1 : A)‖₊) fun n => _
      rw [← norm_to_nnreal, norm_mk_pi_field, norm_to_nnreal]
      cases n
      · simp only [le_refl, mul_one, or_true_iff, le_max_iff, pow_zero]
      · refine'
          le_trans (le_trans (mul_le_mul_right' (nnnorm_pow_le' a n.succ_pos) (r ^ n.succ)) _)
            (le_max_left _ _)
        · by_cases ‖a‖₊ = 0
          · simp only [h, zero_mul, zero_le', pow_succ]
          · rw [← coe_inv h, coe_lt_coe, Nnreal.lt_inv_iff_mul_lt h] at hr
            simpa only [← mul_pow, mul_comm] using pow_le_one' hr.le n.succ
    r_pos := Ennreal.inv_pos.mpr coe_ne_top
    HasSum := fun y hy =>
      by
      have norm_lt : ‖y • a‖ < 1 := by
        by_cases h : ‖a‖₊ = 0
        · simp only [nnnorm_eq_zero.mp h, norm_zero, zero_lt_one, smul_zero]
        · have nnnorm_lt : ‖y‖₊ < ‖a‖₊⁻¹ := by
            simpa only [← coe_inv h, mem_ball_zero_iff, Metric.emetric_ball_nnreal] using hy
          rwa [← coe_nnnorm, ← Real.lt_to_nnreal_iff_coe_lt, Real.to_nnreal_one, nnnorm_smul, ←
            Nnreal.lt_inv_iff_mul_lt h]
      simpa [← smul_pow, (NormedRing.summable_geometric_of_norm_lt_1 _ norm_lt).has_sum_iff] using
        (NormedRing.inverse_one_sub _ norm_lt).symm }
#align
  spectrum.has_fpower_series_on_ball_inverse_one_sub_smul spectrum.hasFpowerSeriesOnBallInverseOneSubSmul

variable {𝕜}

theorem is_unit_one_sub_smul_of_lt_inv_radius {a : A} {z : 𝕜} (h : ↑‖z‖₊ < (spectralRadius 𝕜 a)⁻¹) :
    IsUnit (1 - z • a) := by
  by_cases hz : z = 0
  · simp only [hz, isUnit_one, sub_zero, zero_smul]
  · let u := Units.mk0 z hz
    suffices hu : IsUnit (u⁻¹ • 1 - a)
    · rwa [IsUnit.smul_sub_iff_sub_inv_smul, inv_inv u] at hu
    · rw [Units.smul_def, ← Algebra.algebra_map_eq_smul_one, ← mem_resolvent_set_iff]
      refine' mem_resolvent_set_of_spectral_radius_lt _
      rwa [Units.val_inv_eq_inv_val, nnnorm_inv,
        coe_inv (nnnorm_ne_zero_iff.mpr (Units.val_mk0 hz ▸ hz : (u : 𝕜) ≠ 0)), lt_inv_iff_lt_inv]
#align spectrum.is_unit_one_sub_smul_of_lt_inv_radius spectrum.is_unit_one_sub_smul_of_lt_inv_radius

/-- In a Banach algebra `A` over `𝕜`, for `a : A` the function `λ z, (1 - z • a)⁻¹` is
differentiable on any closed ball centered at zero of radius `r < (spectral_radius 𝕜 a)⁻¹`. -/
theorem differentiable_on_inverse_one_sub_smul [CompleteSpace A] {a : A} {r : ℝ≥0}
    (hr : (r : ℝ≥0∞) < (spectralRadius 𝕜 a)⁻¹) :
    DifferentiableOn 𝕜 (fun z : 𝕜 => Ring.inverse (1 - z • a)) (Metric.closedBall 0 r) :=
  by
  intro z z_mem
  apply DifferentiableAt.differentiable_within_at
  have hu : IsUnit (1 - z • a) :=
    by
    refine' is_unit_one_sub_smul_of_lt_inv_radius (lt_of_le_of_lt (coe_mono _) hr)
    simpa only [norm_to_nnreal, Real.to_nnreal_coe] using
      Real.to_nnreal_mono (mem_closed_ball_zero_iff.mp z_mem)
  have H₁ : Differentiable 𝕜 fun w : 𝕜 => 1 - w • a := (differentiable_id.smul_const a).const_sub 1
  exact DifferentiableAt.comp z (differentiable_at_inverse hu.unit) H₁.differentiable_at
#align
  spectrum.differentiable_on_inverse_one_sub_smul spectrum.differentiable_on_inverse_one_sub_smul

end OneSubSmul

section GelfandFormula

open Filter Ennreal ContinuousMultilinearMap

open TopologicalSpace

variable [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The `limsup` relationship for the spectral radius used to prove `spectrum.gelfand_formula`. -/
theorem limsup_pow_nnnorm_pow_one_div_le_spectral_radius (a : A) :
    limsup (fun n : ℕ => ↑‖a ^ n‖₊ ^ (1 / n : ℝ)) atTop ≤ spectralRadius ℂ a :=
  by
  refine' ennreal.inv_le_inv.mp (le_of_forall_pos_nnreal_lt fun r r_pos r_lt => _)
  simp_rw [inv_limsup, ← one_div]
  let p : FormalMultilinearSeries ℂ ℂ A := fun n =>
    ContinuousMultilinearMap.mkPiField ℂ (Fin n) (a ^ n)
  suffices h : (r : ℝ≥0∞) ≤ p.radius
  · convert h
    simp only [p.radius_eq_liminf, ← norm_to_nnreal, norm_mk_pi_field]
    congr
    ext n
    rw [norm_to_nnreal, Ennreal.coe_rpow_def ‖a ^ n‖₊ (1 / n : ℝ), if_neg]
    exact fun ha => by linarith [ha.2, (one_div_nonneg.mpr n.cast_nonneg : 0 ≤ (1 / n : ℝ))]
  · have H₁ := (differentiable_on_inverse_one_sub_smul r_lt).HasFpowerSeriesOnBall r_pos
    exact ((has_fpower_series_on_ball_inverse_one_sub_smul ℂ a).exchangeRadius H₁).r_le
#align
  spectrum.limsup_pow_nnnorm_pow_one_div_le_spectral_radius spectrum.limsup_pow_nnnorm_pow_one_div_le_spectral_radius

/-- **Gelfand's formula**: Given an element `a : A` of a complex Banach algebra, the
`spectral_radius` of `a` is the limit of the sequence `‖a ^ n‖₊ ^ (1 / n)` -/
theorem pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius (a : A) :
    Tendsto (fun n : ℕ => (‖a ^ n‖₊ ^ (1 / n : ℝ) : ℝ≥0∞)) atTop (𝓝 (spectralRadius ℂ a)) :=
  tendsto_of_le_liminf_of_limsup_le (spectral_radius_le_liminf_pow_nnnorm_pow_one_div ℂ a)
    (limsup_pow_nnnorm_pow_one_div_le_spectral_radius a)
#align
  spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius

/- This is the same as `pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius` but for `norm`
instead of `nnnorm`. -/
/-- **Gelfand's formula**: Given an element `a : A` of a complex Banach algebra, the
`spectral_radius` of `a` is the limit of the sequence `‖a ^ n‖₊ ^ (1 / n)` -/
theorem pow_norm_pow_one_div_tendsto_nhds_spectral_radius (a : A) :
    Tendsto (fun n : ℕ => Ennreal.ofReal (‖a ^ n‖ ^ (1 / n : ℝ))) atTop (𝓝 (spectralRadius ℂ a)) :=
  by
  convert pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius a
  ext1
  rw [← of_real_rpow_of_nonneg (norm_nonneg _) _, ← coe_nnnorm, coe_nnreal_eq]
  exact one_div_nonneg.mpr (by exact_mod_cast zero_le _)
#align
  spectrum.pow_norm_pow_one_div_tendsto_nhds_spectral_radius spectrum.pow_norm_pow_one_div_tendsto_nhds_spectral_radius

end GelfandFormula

section NonemptySpectrum

variable [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [Nontrivial A] (a : A)

/-- In a (nontrivial) complex Banach algebra, every element has nonempty spectrum. -/
protected theorem nonempty : (spectrum ℂ a).Nonempty :=
  by
  /- Suppose `σ a = ∅`, then resolvent set is `ℂ`, any `(z • 1 - a)` is a unit, and `resolvent`
    is differentiable on `ℂ`. -/
  rw [Set.nonempty_iff_ne_empty]
  by_contra h
  have H₀ : resolventSet ℂ a = Set.univ := by rwa [spectrum, Set.compl_empty_iff] at h
  have H₁ : Differentiable ℂ fun z : ℂ => resolvent a z := fun z =>
    (has_deriv_at_resolvent (H₀.symm ▸ Set.mem_univ z : z ∈ resolventSet ℂ a)).DifferentiableAt
  /- The norm of the resolvent is small for all sufficently large `z`, and by compactness and
    continuity it is bounded on the complement of a large ball, thus uniformly bounded on `ℂ`.
    By Liouville's theorem `λ z, resolvent a z` is constant -/
  have H₂ := norm_resolvent_le_forall a
  have H₃ : ∀ z : ℂ, resolvent a z = resolvent a (0 : ℂ) :=
    by
    refine' fun z => H₁.apply_eq_apply_of_bounded (bounded_iff_forall_norm_le.mpr _) z 0
    rcases H₂ 1 zero_lt_one with ⟨R, R_pos, hR⟩
    rcases(ProperSpace.is_compact_closed_ball (0 : ℂ) R).exists_bound_of_continuous_on
        H₁.continuous.continuous_on with
      ⟨C, hC⟩
    use max C 1
    rintro _ ⟨w, rfl⟩
    refine' Or.elim (em (‖w‖ ≤ R)) (fun hw => _) fun hw => _
    · exact (hC w (mem_closed_ball_zero_iff.mpr hw)).trans (le_max_left _ _)
    · exact (hR w (not_le.mp hw).le).trans (le_max_right _ _)
  -- `resolvent a 0 = 0`, which is a contradition because it isn't a unit.
  have H₅ : resolvent a (0 : ℂ) = 0 :=
    by
    refine' norm_eq_zero.mp (le_antisymm (le_of_forall_pos_le_add fun ε hε => _) (norm_nonneg _))
    rcases H₂ ε hε with ⟨R, R_pos, hR⟩
    simpa only [H₃ R] using
      (zero_add ε).symm.subst (hR R (by exact_mod_cast (Real.norm_of_nonneg R_pos.lt.le).symm.le))
  -- `not_is_unit_zero` is where we need `nontrivial A`, it is unavoidable.
  exact
    not_isUnit_zero
      (H₅.subst (is_unit_resolvent.mp (mem_resolvent_set_iff.mp (H₀.symm ▸ Set.mem_univ 0))))
#align spectrum.nonempty spectrum.nonempty

/-- In a complex Banach algebra, the spectral radius is always attained by some element of the
spectrum. -/
theorem exists_nnnorm_eq_spectral_radius : ∃ z ∈ spectrum ℂ a, (‖z‖₊ : ℝ≥0∞) = spectralRadius ℂ a :=
  exists_nnnorm_eq_spectral_radius_of_nonempty (spectrum.nonempty a)
#align spectrum.exists_nnnorm_eq_spectral_radius spectrum.exists_nnnorm_eq_spectral_radius

/-- In a complex Banach algebra, if every element of the spectrum has norm strictly less than
`r : ℝ≥0`, then the spectral radius is also strictly less than `r`. -/
theorem spectral_radius_lt_of_forall_lt {r : ℝ≥0} (hr : ∀ z ∈ spectrum ℂ a, ‖z‖₊ < r) :
    spectralRadius ℂ a < r :=
  spectral_radius_lt_of_forall_lt_of_nonempty (spectrum.nonempty a) hr
#align spectrum.spectral_radius_lt_of_forall_lt spectrum.spectral_radius_lt_of_forall_lt

open Polynomial

open Polynomial

/-- The **spectral mapping theorem** for polynomials in a Banach algebra over `ℂ`. -/
theorem map_polynomial_aeval (p : ℂ[X]) :
    spectrum ℂ (aeval a p) = (fun k => eval k p) '' spectrum ℂ a :=
  map_polynomial_aeval_of_nonempty a p (spectrum.nonempty a)
#align spectrum.map_polynomial_aeval spectrum.map_polynomial_aeval

/-- A specialization of the spectral mapping theorem for polynomials in a Banach algebra over `ℂ`
to monic monomials. -/
protected theorem map_pow (n : ℕ) : spectrum ℂ (a ^ n) = (fun x => x ^ n) '' spectrum ℂ a := by
  simpa only [aeval_X_pow, eval_pow, eval_X] using map_polynomial_aeval a (X ^ n)
#align spectrum.map_pow spectrum.map_pow

end NonemptySpectrum

section GelfandMazurIsomorphism

variable [NormedRing A] [NormedAlgebra ℂ A] (hA : ∀ {a : A}, IsUnit a ↔ a ≠ 0)

include hA

-- mathport name: exprσ
local notation "σ" => spectrum ℂ

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `algebra_map_eq_of_mem [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a] [":" `A] "}")
        (Term.implicitBinder "{" [`z] [":" (Data.Complex.Basic.termℂ "ℂ")] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          («term_∈_» `z "∈" (Term.app (spectrum.Analysis.NormedSpace.Spectrum.termσ_1 "σ") [`a]))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_» (Term.app `algebraMap [(Data.Complex.Basic.termℂ "ℂ") `A `z]) "=" `a)))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.tacticRwa__
            "rwa"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `mem_iff)
              ","
              (Tactic.rwRule [] `hA)
              ","
              (Tactic.rwRule [] `not_not)
              ","
              (Tactic.rwRule [] `sub_eq_zero)]
             "]")
            [(Tactic.location "at" (Tactic.locationHyp [`h] []))])])))
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
         [(Std.Tactic.tacticRwa__
           "rwa"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `mem_iff)
             ","
             (Tactic.rwRule [] `hA)
             ","
             (Tactic.rwRule [] `not_not)
             ","
             (Tactic.rwRule [] `sub_eq_zero)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`h] []))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `mem_iff)
         ","
         (Tactic.rwRule [] `hA)
         ","
         (Tactic.rwRule [] `not_not)
         ","
         (Tactic.rwRule [] `sub_eq_zero)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_eq_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `not_not
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hA
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_» (Term.app `algebraMap [(Data.Complex.Basic.termℂ "ℂ") `A `z]) "=" `a)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `algebraMap [(Data.Complex.Basic.termℂ "ℂ") `A `z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Complex.Basic.termℂ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Complex.Basic.termℂ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Data.Complex.Basic.termℂ "ℂ")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `algebraMap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_» `z "∈" (Term.app (spectrum.Analysis.NormedSpace.Spectrum.termσ_1 "σ") [`a]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (spectrum.Analysis.NormedSpace.Spectrum.termσ_1 "σ") [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Analysis.NormedSpace.Spectrum.termσ_1 "σ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Analysis.NormedSpace.Spectrum.termσ_1', expected 'spectrum.Analysis.NormedSpace.Spectrum.termσ_1._@.Analysis.NormedSpace.Spectrum._hyg.2687'
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
  algebra_map_eq_of_mem
  { a : A } { z : ℂ } ( h : z ∈ σ a ) : algebraMap ℂ A z = a
  := by rwa [ mem_iff , hA , not_not , sub_eq_zero ] at h
#align spectrum.algebra_map_eq_of_mem spectrum.algebra_map_eq_of_mem

/-- **Gelfand-Mazur theorem**: For a complex Banach division algebra, the natural `algebra_map ℂ A`
is an algebra isomorphism whose inverse is given by selecting the (unique) element of
`spectrum ℂ a`. In addition, `algebra_map_isometry` guarantees this map is an isometry.

Note: because `normed_division_ring` requires the field `norm_mul' : ∀ a b, ‖a * b‖ = ‖a‖ * ‖b‖`, we
don't use this type class and instead opt for a `normed_ring` in which the nonzero elements are
precisely the units. This allows for the application of this isomorphism in broader contexts, e.g.,
to the quotient of a complex Banach algebra by a maximal ideal. In the case when `A` is actually a
`normed_division_ring`, one may fill in the argument `hA` with the lemma `is_unit_iff_ne_zero`. -/
@[simps]
noncomputable def NormedRing.algEquivComplexOfComplete [CompleteSpace A] : ℂ ≃ₐ[ℂ] A :=
  let nt : Nontrivial A := ⟨⟨1, 0, hA.mp ⟨⟨1, 1, mul_one _, mul_one _⟩, rfl⟩⟩⟩
  { Algebra.ofId ℂ A with
    toFun := algebraMap ℂ A
    invFun := fun a => (@spectrum.nonempty _ _ _ _ nt a).some
    left_inv := fun z => by
      simpa only [@scalar_eq _ _ _ _ _ nt _] using
        (@spectrum.nonempty _ _ _ _ nt <| algebraMap ℂ A z).some_mem
    right_inv := fun a => algebra_map_eq_of_mem (@hA) (@spectrum.nonempty _ _ _ _ nt a).some_mem }
#align normed_ring.alg_equiv_complex_of_complete NormedRing.algEquivComplexOfComplete

end GelfandMazurIsomorphism

section ExpMapping

-- mathport name: «expr↑ₐ»
local notation "↑ₐ" => algebraMap 𝕜 A

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "For `𝕜 = ℝ` or `𝕜 = ℂ`, `exp 𝕜` maps the spectrum of `a` into the spectrum of `exp 𝕜 a`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `exp_mem_exp [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `IsROrC [`𝕜]) "]")
        (Term.instBinder "[" [] (Term.app `NormedRing [`A]) "]")
        (Term.instBinder "[" [] (Term.app `NormedAlgebra [`𝕜 `A]) "]")
        (Term.instBinder "[" [] (Term.app `CompleteSpace [`A]) "]")
        (Term.explicitBinder "(" [`a] [":" `A] [] ")")
        (Term.implicitBinder "{" [`z] [":" `𝕜] "}")
        (Term.explicitBinder
         "("
         [`hz]
         [":" («term_∈_» `z "∈" (Term.app `spectrum [`𝕜 `a]))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_∈_» (Term.app `exp [`𝕜 `z]) "∈" (Term.app `spectrum [`𝕜 (Term.app `exp [`𝕜 `a])]))))
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
              [`hexpmul []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Term.app `exp [`𝕜 `a])
                 "="
                 («term_*_»
                  (Term.app
                   `exp
                   [`𝕜
                    («term_-_»
                     `a
                     "-"
                     (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z]))])
                  "*"
                  (Term.app
                   (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ")
                   [(Term.app `exp [`𝕜 `z])]))))]
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
                    [(Tactic.rwRule [] (Term.app `algebra_map_exp_comm [`z]))
                     ","
                     (Tactic.rwRule
                      [(patternIgnore (token.«← » "←"))]
                      (Term.app
                       `exp_add_of_commute
                       [(Term.proj
                         (Term.app
                          `Algebra.commutes
                          [`z
                           («term_-_»
                            `a
                            "-"
                            (Term.app
                             (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ")
                             [`z]))])
                         "."
                         `symm)]))
                     ","
                     (Tactic.rwRule [] `sub_add_cancel)]
                    "]")
                   [])]))))))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `b
              []
              []
              ":="
              (Topology.Algebra.InfiniteSum.«term∑'_,_»
               "∑'"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder (Lean.binderIdent `n) [(group ":" (termℕ "ℕ"))]))
               ", "
               (Algebra.Group.Defs.«term_•_»
                (Term.typeAscription
                 "("
                 («term_⁻¹» (Term.proj («term_+_» `n "+" (num "1")) "." `factorial) "⁻¹")
                 ":"
                 [`𝕜]
                 ")")
                " • "
                («term_^_»
                 («term_-_»
                  `a
                  "-"
                  (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z]))
                 "^"
                 `n))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hb []]
              [(Term.typeSpec
                ":"
                (Term.app
                 `Summable
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [`n]
                    [(Term.typeSpec ":" (termℕ "ℕ"))]
                    "=>"
                    (Algebra.Group.Defs.«term_•_»
                     (Term.typeAscription
                      "("
                      («term_⁻¹» (Term.proj («term_+_» `n "+" (num "1")) "." `factorial) "⁻¹")
                      ":"
                      [`𝕜]
                      ")")
                     " • "
                     («term_^_»
                      («term_-_»
                       `a
                       "-"
                       (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z]))
                      "^"
                      `n))))]))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.refine'
                   "refine'"
                   (Term.app
                    `summable_of_norm_bounded_eventually
                    [(Term.hole "_")
                     (Term.app
                      `Real.summable_pow_div_factorial
                      [(Analysis.Normed.Group.Basic.«term‖_‖»
                        "‖"
                        («term_-_»
                         `a
                         "-"
                         (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z]))
                        "‖")])
                     (Term.hole "_")]))
                  []
                  (Tactic.filterUpwards
                   "filter_upwards"
                   [(Tactic.termList
                     "["
                     [(Term.app `Filter.eventually_cofinite_ne [(num "0")])]
                     "]")]
                   ["with" [`n `hn]]
                   [])
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `norm_smul)
                     ","
                     (Tactic.rwRule [] `mul_comm)
                     ","
                     (Tactic.rwRule [] `norm_inv)
                     ","
                     (Tactic.rwRule [] `IsROrC.norm_eq_abs)
                     ","
                     (Tactic.rwRule [] `IsROrC.abs_cast_nat)
                     ","
                     (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `div_eq_mul_inv)]
                    "]")
                   [])
                  []
                  (Tactic.exact
                   "exact"
                   (Term.app
                    `div_le_div
                    [(Term.app `pow_nonneg [(Term.app `norm_nonneg [(Term.hole "_")]) `n])
                     (Term.app
                      `norm_pow_le'
                      [(«term_-_»
                        `a
                        "-"
                        (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z]))
                       (Term.app `zero_lt_iff.mpr [`hn])])
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.NormCast.tacticExact_mod_cast_
                          "exact_mod_cast"
                          (Term.app `Nat.factorial_pos [`n]))])))
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.NormCast.tacticExact_mod_cast_
                          "exact_mod_cast"
                          (Term.app
                           `Nat.factorial_le
                           [(Term.proj (Term.app `lt_add_one [`n]) "." `le)]))])))]))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`h₀ []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Topology.Algebra.InfiniteSum.«term∑'_,_»
                  "∑'"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder (Lean.binderIdent `n) [(group ":" (termℕ "ℕ"))]))
                  ", "
                  (Algebra.Group.Defs.«term_•_»
                   (Term.typeAscription
                    "("
                    («term_⁻¹» (Term.proj («term_+_» `n "+" (num "1")) "." `factorial) "⁻¹")
                    ":"
                    [`𝕜]
                    ")")
                   " • "
                   («term_^_»
                    («term_-_»
                     `a
                     "-"
                     (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z]))
                    "^"
                    («term_+_» `n "+" (num "1")))))
                 "="
                 («term_*_»
                  («term_-_»
                   `a
                   "-"
                   (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z]))
                  "*"
                  `b)))]
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
                      [(Tactic.simpLemma [] [] `mul_smul_comm)
                       ","
                       (Tactic.simpLemma [] [] `pow_succ)]
                      "]")]
                    ["using"
                     (Term.app
                      `hb.tsum_mul_left
                      [(«term_-_»
                        `a
                        "-"
                        (Term.app
                         (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ")
                         [`z]))])]))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`h₁ []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Topology.Algebra.InfiniteSum.«term∑'_,_»
                  "∑'"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder (Lean.binderIdent `n) [(group ":" (termℕ "ℕ"))]))
                  ", "
                  (Algebra.Group.Defs.«term_•_»
                   (Term.typeAscription
                    "("
                    («term_⁻¹» (Term.proj («term_+_» `n "+" (num "1")) "." `factorial) "⁻¹")
                    ":"
                    [`𝕜]
                    ")")
                   " • "
                   («term_^_»
                    («term_-_»
                     `a
                     "-"
                     (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z]))
                    "^"
                    («term_+_» `n "+" (num "1")))))
                 "="
                 («term_*_»
                  `b
                  "*"
                  («term_-_»
                   `a
                   "-"
                   (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z])))))]
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
                      [(Tactic.simpLemma [] [] `pow_succ')
                       ","
                       (Tactic.simpLemma [] [] `Algebra.smul_mul_assoc)]
                      "]")]
                    ["using"
                     (Term.app
                      `hb.tsum_mul_right
                      [(«term_-_»
                        `a
                        "-"
                        (Term.app
                         (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ")
                         [`z]))])]))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`h₃ []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Term.app
                  `exp
                  [`𝕜
                   («term_-_»
                    `a
                    "-"
                    (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z]))])
                 "="
                 («term_+_»
                  (num "1")
                  "+"
                  («term_*_»
                   («term_-_»
                    `a
                    "-"
                    (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z]))
                   "*"
                   `b))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `exp_eq_tsum)] "]")
                   [])
                  []
                  (convert
                   "convert"
                   []
                   (Term.app
                    `tsum_eq_zero_add
                    [(Term.app
                      `exp_series_summable'
                      [(«term_-_»
                        `a
                        "-"
                        (Term.app
                         (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ")
                         [`z]))])])
                   [])
                  []
                  (Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [] `Nat.factorial_zero)
                     ","
                     (Tactic.simpLemma [] [] `Nat.cast_one)
                     ","
                     (Tactic.simpLemma [] [] `inv_one)
                     ","
                     (Tactic.simpLemma [] [] `pow_zero)
                     ","
                     (Tactic.simpLemma [] [] `one_smul)]
                    "]"]
                   [])
                  []
                  (Tactic.exact "exact" `h₀.symm)]))))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `spectrum.mem_iff)
              ","
              (Tactic.rwRule [] `IsUnit.sub_iff)
              ","
              (Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               (Term.app
                `one_mul
                [(Term.app
                  (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ")
                  [(Term.app `exp [`𝕜 `z])])]))
              ","
              (Tactic.rwRule [] `hexpmul)
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `_root_.sub_mul)
              ","
              (Tactic.rwRule
               []
               (Term.app
                `Commute.isUnit_mul_iff
                [(Term.proj
                  (Term.app
                   `Algebra.commutes
                   [(Term.app `exp [`𝕜 `z])
                    («term_-_»
                     (Term.app
                      `exp
                      [`𝕜
                       («term_-_»
                        `a
                        "-"
                        (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z]))])
                     "-"
                     (num "1"))])
                  "."
                  `symm)]))
              ","
              (Tactic.rwRule [] (Term.app `sub_eq_iff_eq_add'.mpr [`h₃]))
              ","
              (Tactic.rwRule
               []
               (Term.app
                `Commute.isUnit_mul_iff
                [(Term.typeAscription
                  "("
                  (Term.subst `h₀ "▸" [`h₁])
                  ":"
                  [(«term_=_»
                    («term_*_»
                     («term_-_»
                      `a
                      "-"
                      (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z]))
                     "*"
                     `b)
                    "="
                    («term_*_»
                     `b
                     "*"
                     («term_-_»
                      `a
                      "-"
                      (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z]))))]
                  ")")]))]
             "]")
            [])
           []
           (Tactic.exact
            "exact"
            (Term.app
             `not_and_of_not_left
             [(Term.hole "_")
              (Term.app
               `not_and_of_not_left
               [(Term.hole "_")
                (Term.app
                 (Term.proj (Term.app `not_iff_not.mpr [`IsUnit.sub_iff]) "." `mp)
                 [`hz])])]))])))
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
             [`hexpmul []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.app `exp [`𝕜 `a])
                "="
                («term_*_»
                 (Term.app
                  `exp
                  [`𝕜
                   («term_-_»
                    `a
                    "-"
                    (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z]))])
                 "*"
                 (Term.app
                  (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ")
                  [(Term.app `exp [`𝕜 `z])]))))]
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
                   [(Tactic.rwRule [] (Term.app `algebra_map_exp_comm [`z]))
                    ","
                    (Tactic.rwRule
                     [(patternIgnore (token.«← » "←"))]
                     (Term.app
                      `exp_add_of_commute
                      [(Term.proj
                        (Term.app
                         `Algebra.commutes
                         [`z
                          («term_-_»
                           `a
                           "-"
                           (Term.app
                            (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ")
                            [`z]))])
                        "."
                        `symm)]))
                    ","
                    (Tactic.rwRule [] `sub_add_cancel)]
                   "]")
                  [])]))))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `b
             []
             []
             ":="
             (Topology.Algebra.InfiniteSum.«term∑'_,_»
              "∑'"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `n) [(group ":" (termℕ "ℕ"))]))
              ", "
              (Algebra.Group.Defs.«term_•_»
               (Term.typeAscription
                "("
                («term_⁻¹» (Term.proj («term_+_» `n "+" (num "1")) "." `factorial) "⁻¹")
                ":"
                [`𝕜]
                ")")
               " • "
               («term_^_»
                («term_-_»
                 `a
                 "-"
                 (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z]))
                "^"
                `n))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hb []]
             [(Term.typeSpec
               ":"
               (Term.app
                `Summable
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [`n]
                   [(Term.typeSpec ":" (termℕ "ℕ"))]
                   "=>"
                   (Algebra.Group.Defs.«term_•_»
                    (Term.typeAscription
                     "("
                     («term_⁻¹» (Term.proj («term_+_» `n "+" (num "1")) "." `factorial) "⁻¹")
                     ":"
                     [`𝕜]
                     ")")
                    " • "
                    («term_^_»
                     («term_-_»
                      `a
                      "-"
                      (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z]))
                     "^"
                     `n))))]))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.refine'
                  "refine'"
                  (Term.app
                   `summable_of_norm_bounded_eventually
                   [(Term.hole "_")
                    (Term.app
                     `Real.summable_pow_div_factorial
                     [(Analysis.Normed.Group.Basic.«term‖_‖»
                       "‖"
                       («term_-_»
                        `a
                        "-"
                        (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z]))
                       "‖")])
                    (Term.hole "_")]))
                 []
                 (Tactic.filterUpwards
                  "filter_upwards"
                  [(Tactic.termList
                    "["
                    [(Term.app `Filter.eventually_cofinite_ne [(num "0")])]
                    "]")]
                  ["with" [`n `hn]]
                  [])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `norm_smul)
                    ","
                    (Tactic.rwRule [] `mul_comm)
                    ","
                    (Tactic.rwRule [] `norm_inv)
                    ","
                    (Tactic.rwRule [] `IsROrC.norm_eq_abs)
                    ","
                    (Tactic.rwRule [] `IsROrC.abs_cast_nat)
                    ","
                    (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `div_eq_mul_inv)]
                   "]")
                  [])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.app
                   `div_le_div
                   [(Term.app `pow_nonneg [(Term.app `norm_nonneg [(Term.hole "_")]) `n])
                    (Term.app
                     `norm_pow_le'
                     [(«term_-_»
                       `a
                       "-"
                       (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z]))
                      (Term.app `zero_lt_iff.mpr [`hn])])
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.NormCast.tacticExact_mod_cast_
                         "exact_mod_cast"
                         (Term.app `Nat.factorial_pos [`n]))])))
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.NormCast.tacticExact_mod_cast_
                         "exact_mod_cast"
                         (Term.app
                          `Nat.factorial_le
                          [(Term.proj (Term.app `lt_add_one [`n]) "." `le)]))])))]))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h₀ []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Topology.Algebra.InfiniteSum.«term∑'_,_»
                 "∑'"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `n) [(group ":" (termℕ "ℕ"))]))
                 ", "
                 (Algebra.Group.Defs.«term_•_»
                  (Term.typeAscription
                   "("
                   («term_⁻¹» (Term.proj («term_+_» `n "+" (num "1")) "." `factorial) "⁻¹")
                   ":"
                   [`𝕜]
                   ")")
                  " • "
                  («term_^_»
                   («term_-_»
                    `a
                    "-"
                    (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z]))
                   "^"
                   («term_+_» `n "+" (num "1")))))
                "="
                («term_*_»
                 («term_-_»
                  `a
                  "-"
                  (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z]))
                 "*"
                 `b)))]
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
                     [(Tactic.simpLemma [] [] `mul_smul_comm)
                      ","
                      (Tactic.simpLemma [] [] `pow_succ)]
                     "]")]
                   ["using"
                    (Term.app
                     `hb.tsum_mul_left
                     [(«term_-_»
                       `a
                       "-"
                       (Term.app
                        (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ")
                        [`z]))])]))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h₁ []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Topology.Algebra.InfiniteSum.«term∑'_,_»
                 "∑'"
                 (Std.ExtendedBinder.extBinders
                  (Std.ExtendedBinder.extBinder (Lean.binderIdent `n) [(group ":" (termℕ "ℕ"))]))
                 ", "
                 (Algebra.Group.Defs.«term_•_»
                  (Term.typeAscription
                   "("
                   («term_⁻¹» (Term.proj («term_+_» `n "+" (num "1")) "." `factorial) "⁻¹")
                   ":"
                   [`𝕜]
                   ")")
                  " • "
                  («term_^_»
                   («term_-_»
                    `a
                    "-"
                    (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z]))
                   "^"
                   («term_+_» `n "+" (num "1")))))
                "="
                («term_*_»
                 `b
                 "*"
                 («term_-_»
                  `a
                  "-"
                  (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z])))))]
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
                     [(Tactic.simpLemma [] [] `pow_succ')
                      ","
                      (Tactic.simpLemma [] [] `Algebra.smul_mul_assoc)]
                     "]")]
                   ["using"
                    (Term.app
                     `hb.tsum_mul_right
                     [(«term_-_»
                       `a
                       "-"
                       (Term.app
                        (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ")
                        [`z]))])]))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h₃ []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.app
                 `exp
                 [`𝕜
                  («term_-_»
                   `a
                   "-"
                   (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z]))])
                "="
                («term_+_»
                 (num "1")
                 "+"
                 («term_*_»
                  («term_-_»
                   `a
                   "-"
                   (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z]))
                  "*"
                  `b))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `exp_eq_tsum)] "]")
                  [])
                 []
                 (convert
                  "convert"
                  []
                  (Term.app
                   `tsum_eq_zero_add
                   [(Term.app
                     `exp_series_summable'
                     [(«term_-_»
                       `a
                       "-"
                       (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z]))])])
                  [])
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `Nat.factorial_zero)
                    ","
                    (Tactic.simpLemma [] [] `Nat.cast_one)
                    ","
                    (Tactic.simpLemma [] [] `inv_one)
                    ","
                    (Tactic.simpLemma [] [] `pow_zero)
                    ","
                    (Tactic.simpLemma [] [] `one_smul)]
                   "]"]
                  [])
                 []
                 (Tactic.exact "exact" `h₀.symm)]))))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `spectrum.mem_iff)
             ","
             (Tactic.rwRule [] `IsUnit.sub_iff)
             ","
             (Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              (Term.app
               `one_mul
               [(Term.app
                 (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ")
                 [(Term.app `exp [`𝕜 `z])])]))
             ","
             (Tactic.rwRule [] `hexpmul)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `_root_.sub_mul)
             ","
             (Tactic.rwRule
              []
              (Term.app
               `Commute.isUnit_mul_iff
               [(Term.proj
                 (Term.app
                  `Algebra.commutes
                  [(Term.app `exp [`𝕜 `z])
                   («term_-_»
                    (Term.app
                     `exp
                     [`𝕜
                      («term_-_»
                       `a
                       "-"
                       (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z]))])
                    "-"
                    (num "1"))])
                 "."
                 `symm)]))
             ","
             (Tactic.rwRule [] (Term.app `sub_eq_iff_eq_add'.mpr [`h₃]))
             ","
             (Tactic.rwRule
              []
              (Term.app
               `Commute.isUnit_mul_iff
               [(Term.typeAscription
                 "("
                 (Term.subst `h₀ "▸" [`h₁])
                 ":"
                 [(«term_=_»
                   («term_*_»
                    («term_-_»
                     `a
                     "-"
                     (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z]))
                    "*"
                    `b)
                   "="
                   («term_*_»
                    `b
                    "*"
                    («term_-_»
                     `a
                     "-"
                     (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z]))))]
                 ")")]))]
            "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            `not_and_of_not_left
            [(Term.hole "_")
             (Term.app
              `not_and_of_not_left
              [(Term.hole "_")
               (Term.app
                (Term.proj (Term.app `not_iff_not.mpr [`IsUnit.sub_iff]) "." `mp)
                [`hz])])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `not_and_of_not_left
        [(Term.hole "_")
         (Term.app
          `not_and_of_not_left
          [(Term.hole "_")
           (Term.app (Term.proj (Term.app `not_iff_not.mpr [`IsUnit.sub_iff]) "." `mp) [`hz])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `not_and_of_not_left
       [(Term.hole "_")
        (Term.app
         `not_and_of_not_left
         [(Term.hole "_")
          (Term.app (Term.proj (Term.app `not_iff_not.mpr [`IsUnit.sub_iff]) "." `mp) [`hz])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `not_and_of_not_left
       [(Term.hole "_")
        (Term.app (Term.proj (Term.app `not_iff_not.mpr [`IsUnit.sub_iff]) "." `mp) [`hz])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `not_iff_not.mpr [`IsUnit.sub_iff]) "." `mp) [`hz])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hz
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `not_iff_not.mpr [`IsUnit.sub_iff]) "." `mp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `not_iff_not.mpr [`IsUnit.sub_iff])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `IsUnit.sub_iff
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `not_iff_not.mpr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `not_iff_not.mpr [`IsUnit.sub_iff])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.paren "(" (Term.app `not_iff_not.mpr [`IsUnit.sub_iff]) ")") "." `mp)
      [`hz])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `not_and_of_not_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `not_and_of_not_left
      [(Term.hole "_")
       (Term.paren
        "("
        (Term.app
         (Term.proj (Term.paren "(" (Term.app `not_iff_not.mpr [`IsUnit.sub_iff]) ")") "." `mp)
         [`hz])
        ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `not_and_of_not_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `spectrum.mem_iff)
         ","
         (Tactic.rwRule [] `IsUnit.sub_iff)
         ","
         (Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          (Term.app
           `one_mul
           [(Term.app
             (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ")
             [(Term.app `exp [`𝕜 `z])])]))
         ","
         (Tactic.rwRule [] `hexpmul)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `_root_.sub_mul)
         ","
         (Tactic.rwRule
          []
          (Term.app
           `Commute.isUnit_mul_iff
           [(Term.proj
             (Term.app
              `Algebra.commutes
              [(Term.app `exp [`𝕜 `z])
               («term_-_»
                (Term.app
                 `exp
                 [`𝕜
                  («term_-_»
                   `a
                   "-"
                   (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z]))])
                "-"
                (num "1"))])
             "."
             `symm)]))
         ","
         (Tactic.rwRule [] (Term.app `sub_eq_iff_eq_add'.mpr [`h₃]))
         ","
         (Tactic.rwRule
          []
          (Term.app
           `Commute.isUnit_mul_iff
           [(Term.typeAscription
             "("
             (Term.subst `h₀ "▸" [`h₁])
             ":"
             [(«term_=_»
               («term_*_»
                («term_-_»
                 `a
                 "-"
                 (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z]))
                "*"
                `b)
               "="
               («term_*_»
                `b
                "*"
                («term_-_»
                 `a
                 "-"
                 (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z]))))]
             ")")]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Commute.isUnit_mul_iff
       [(Term.typeAscription
         "("
         (Term.subst `h₀ "▸" [`h₁])
         ":"
         [(«term_=_»
           («term_*_»
            («term_-_»
             `a
             "-"
             (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z]))
            "*"
            `b)
           "="
           («term_*_»
            `b
            "*"
            («term_-_»
             `a
             "-"
             (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z]))))]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (Term.subst `h₀ "▸" [`h₁])
       ":"
       [(«term_=_»
         («term_*_»
          («term_-_»
           `a
           "-"
           (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z]))
          "*"
          `b)
         "="
         («term_*_»
          `b
          "*"
          («term_-_»
           `a
           "-"
           (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z]))))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       («term_*_»
        («term_-_» `a "-" (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z]))
        "*"
        `b)
       "="
       («term_*_»
        `b
        "*"
        («term_-_»
         `a
         "-"
         (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       `b
       "*"
       («term_-_» `a "-" (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» `a "-" (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ") [`z])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2» "↑ₐ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'spectrum.Analysis.NormedSpace.Spectrum.«term↑ₐ_2»', expected 'spectrum.Analysis.NormedSpace.Spectrum.term↑ₐ_2._@.Analysis.NormedSpace.Spectrum._hyg.3201'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- For `𝕜 = ℝ` or `𝕜 = ℂ`, `exp 𝕜` maps the spectrum of `a` into the spectrum of `exp 𝕜 a`. -/
  theorem
    exp_mem_exp
    [ IsROrC 𝕜 ]
        [ NormedRing A ]
        [ NormedAlgebra 𝕜 A ]
        [ CompleteSpace A ]
        ( a : A )
        { z : 𝕜 }
        ( hz : z ∈ spectrum 𝕜 a )
      : exp 𝕜 z ∈ spectrum 𝕜 exp 𝕜 a
    :=
      by
        have
            hexpmul
              : exp 𝕜 a = exp 𝕜 a - ↑ₐ z * ↑ₐ exp 𝕜 z
              :=
              by
                rw
                  [
                    algebra_map_exp_comm z
                      ,
                      ← exp_add_of_commute Algebra.commutes z a - ↑ₐ z . symm
                      ,
                      sub_add_cancel
                    ]
          let b := ∑' n : ℕ , ( n + 1 . factorial ⁻¹ : 𝕜 ) • a - ↑ₐ z ^ n
          have
            hb
              : Summable fun n : ℕ => ( n + 1 . factorial ⁻¹ : 𝕜 ) • a - ↑ₐ z ^ n
              :=
              by
                refine'
                    summable_of_norm_bounded_eventually
                      _ Real.summable_pow_div_factorial ‖ a - ↑ₐ z ‖ _
                  filter_upwards [ Filter.eventually_cofinite_ne 0 ] with n hn
                  rw
                    [
                      norm_smul
                        ,
                        mul_comm
                        ,
                        norm_inv
                        ,
                        IsROrC.norm_eq_abs
                        ,
                        IsROrC.abs_cast_nat
                        ,
                        ← div_eq_mul_inv
                      ]
                  exact
                    div_le_div
                      pow_nonneg norm_nonneg _ n
                        norm_pow_le' a - ↑ₐ z zero_lt_iff.mpr hn
                        by exact_mod_cast Nat.factorial_pos n
                        by exact_mod_cast Nat.factorial_le lt_add_one n . le
          have
            h₀
              : ∑' n : ℕ , ( n + 1 . factorial ⁻¹ : 𝕜 ) • a - ↑ₐ z ^ n + 1 = a - ↑ₐ z * b
              :=
              by simpa only [ mul_smul_comm , pow_succ ] using hb.tsum_mul_left a - ↑ₐ z
          have
            h₁
              : ∑' n : ℕ , ( n + 1 . factorial ⁻¹ : 𝕜 ) • a - ↑ₐ z ^ n + 1 = b * a - ↑ₐ z
              :=
              by simpa only [ pow_succ' , Algebra.smul_mul_assoc ] using hb.tsum_mul_right a - ↑ₐ z
          have
            h₃
              : exp 𝕜 a - ↑ₐ z = 1 + a - ↑ₐ z * b
              :=
              by
                rw [ exp_eq_tsum ]
                  convert tsum_eq_zero_add exp_series_summable' a - ↑ₐ z
                  simp only [ Nat.factorial_zero , Nat.cast_one , inv_one , pow_zero , one_smul ]
                  exact h₀.symm
          rw
            [
              spectrum.mem_iff
                ,
                IsUnit.sub_iff
                ,
                ← one_mul ↑ₐ exp 𝕜 z
                ,
                hexpmul
                ,
                ← _root_.sub_mul
                ,
                Commute.isUnit_mul_iff Algebra.commutes exp 𝕜 z exp 𝕜 a - ↑ₐ z - 1 . symm
                ,
                sub_eq_iff_eq_add'.mpr h₃
                ,
                Commute.isUnit_mul_iff ( h₀ ▸ h₁ : a - ↑ₐ z * b = b * a - ↑ₐ z )
              ]
          exact not_and_of_not_left _ not_and_of_not_left _ not_iff_not.mpr IsUnit.sub_iff . mp hz
#align spectrum.exp_mem_exp spectrum.exp_mem_exp

end ExpMapping

end spectrum

namespace AlgHom

section NormedField

variable {F : Type _} [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

-- mathport name: «expr↑ₐ»
local notation "↑ₐ" => algebraMap 𝕜 A

/-- An algebra homomorphism into the base field, as a continuous linear map (since it is
automatically bounded). See note [lower instance priority] -/
instance (priority := 100) [AlgHomClass F 𝕜 A 𝕜] : ContinuousLinearMapClass F 𝕜 A 𝕜 :=
  { AlgHomClass.linearMapClass with
    map_continuous := fun φ =>
      (AddMonoidHomClass.continuous_of_bound φ ‖(1 : A)‖) fun a =>
        mul_comm ‖a‖ ‖(1 : A)‖ ▸ spectrum.norm_le_norm_mul_of_mem (apply_mem_spectrum φ _) }

/-- An algebra homomorphism into the base field, as a continuous linear map (since it is
automatically bounded). -/
def toContinuousLinearMap (φ : A →ₐ[𝕜] 𝕜) : A →L[𝕜] 𝕜 :=
  { φ.toLinearMap with cont := map_continuous φ }
#align alg_hom.to_continuous_linear_map AlgHom.toContinuousLinearMap

@[simp]
theorem coe_to_continuous_linear_map (φ : A →ₐ[𝕜] 𝕜) : ⇑φ.toContinuousLinearMap = φ :=
  rfl
#align alg_hom.coe_to_continuous_linear_map AlgHom.coe_to_continuous_linear_map

theorem norm_apply_le_self_mul_norm_one [AlgHomClass F 𝕜 A 𝕜] (f : F) (a : A) :
    ‖f a‖ ≤ ‖a‖ * ‖(1 : A)‖ :=
  spectrum.norm_le_norm_mul_of_mem (apply_mem_spectrum f _)
#align alg_hom.norm_apply_le_self_mul_norm_one AlgHom.norm_apply_le_self_mul_norm_one

theorem norm_apply_le_self [NormOneClass A] [AlgHomClass F 𝕜 A 𝕜] (f : F) (a : A) : ‖f a‖ ≤ ‖a‖ :=
  spectrum.norm_le_norm_of_mem (apply_mem_spectrum f _)
#align alg_hom.norm_apply_le_self AlgHom.norm_apply_le_self

end NormedField

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

-- mathport name: «expr↑ₐ»
local notation "↑ₐ" => algebraMap 𝕜 A

@[simp]
theorem to_continuous_linear_map_norm [NormOneClass A] (φ : A →ₐ[𝕜] 𝕜) :
    ‖φ.toContinuousLinearMap‖ = 1 :=
  ContinuousLinearMap.op_norm_eq_of_bounds zero_le_one
    (fun a => (one_mul ‖a‖).symm ▸ spectrum.norm_le_norm_of_mem (apply_mem_spectrum φ _))
    fun _ _ h => by simpa only [coe_to_continuous_linear_map, map_one, norm_one, mul_one] using h 1
#align alg_hom.to_continuous_linear_map_norm AlgHom.to_continuous_linear_map_norm

end NontriviallyNormedField

end AlgHom

namespace WeakDual

namespace CharacterSpace

variable [NontriviallyNormedField 𝕜] [NormedRing A] [CompleteSpace A]

variable [NormedAlgebra 𝕜 A]

/-- The equivalence between characters and algebra homomorphisms into the base field. -/
def equivAlgHom : characterSpace 𝕜 A ≃ (A →ₐ[𝕜] 𝕜)
    where
  toFun := toAlgHom
  invFun f :=
    { val := f.toContinuousLinearMap
      property := by
        rw [eq_set_map_one_map_mul]
        exact ⟨map_one f, map_mul f⟩ }
  left_inv f := Subtype.ext <| ContinuousLinearMap.ext fun x => rfl
  right_inv f := AlgHom.ext fun x => rfl
#align weak_dual.character_space.equiv_alg_hom WeakDual.characterSpace.equivAlgHom

@[simp]
theorem equiv_alg_hom_coe (f : characterSpace 𝕜 A) : ⇑(equivAlgHom f) = f :=
  rfl
#align weak_dual.character_space.equiv_alg_hom_coe WeakDual.characterSpace.equiv_alg_hom_coe

@[simp]
theorem equiv_alg_hom_symm_coe (f : A →ₐ[𝕜] 𝕜) : ⇑(equivAlgHom.symm f) = f :=
  rfl
#align
  weak_dual.character_space.equiv_alg_hom_symm_coe WeakDual.characterSpace.equiv_alg_hom_symm_coe

end CharacterSpace

end WeakDual

